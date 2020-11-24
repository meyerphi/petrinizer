module Solver.Simplifier (
     checkSubsumptionSat
    ,generateCuts
    ,greedySimplify
    ,formulaToCut
    ,simplifyPositiveCut
) where

import Data.SBV
import Data.Maybe
import Data.Ord (comparing)
import Data.List (minimumBy)
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Identity
import qualified Data.Map as M
import qualified Data.Set as S

import Util
import Options
import Solver
import Solver.TransitionInvariant
import Property
import PetriNet

checkTransPositive :: SBMap Transition -> S.Set Transition -> SBool
checkTransPositive m ts = sOr $ map (val m) $ S.elems ts

checkTransNegative :: SBMap Transition -> S.Set Transition -> SBool
checkTransNegative m ts = sAnd $ map (sNot . val m) $ S.elems ts

checkCutPositive :: SBMap Transition -> SimpleCut -> SBool
checkCutPositive m (c0, cs) =
        checkTransNegative m c0 .&& sAnd (map (checkTransPositive m) cs)

checkCutNegative :: SBMap Transition -> SimpleCut -> SBool
checkCutNegative m (c0, cs) =
        checkTransPositive m c0 .|| sOr (map (checkTransNegative m) cs)

checkCuts :: SimpleCut -> [SimpleCut] -> SBMap Transition -> SBool
checkCuts c0 cs m = checkCutPositive m c0 .&& sAnd (map (checkCutNegative m) cs)

getSubsumption :: BMap Transition -> [Transition]
getSubsumption m = M.keys (M.filter id m)

checkSubsumptionSat :: SimpleCut -> [SimpleCut] -> ConstraintProblem Bool [Transition]
checkSubsumptionSat c0 cs =
        let m = makeVarMap $ S.elems $ S.unions $ map cutTransitions (c0:cs)
        in  ("constraint subsumption", "subsumption",
            getNames m,
            \fm -> checkCuts c0 cs (fmap fm m),
            \fm -> getSubsumption (fmap fm m))

cutTransitions :: SimpleCut -> S.Set Transition
cutTransitions (c0, cs) = S.unions (c0:cs)

type SimpConfig = ([[SimpleCut] -> OptIO [SimpleCut]], SimpleCut, Int)

noSimp :: PetriNet -> Formula Transition -> SimpConfig
noSimp _ _ = ([], (S.empty, []), 0)

simpWithoutFormula :: PetriNet -> Formula Transition -> SimpConfig
simpWithoutFormula net f =
        (
        [ return . simplifyCuts
        , return . removeImplicants
        , greedySimplify net f
        , return . combineCuts
        , simplifyBySubsumption
        ]
        , (S.empty, [])
        , 2
        )

simpWithFormula :: PetriNet -> Formula Transition -> SimpConfig
simpWithFormula net f =
        (
        [ return . simplifyCuts
        , return . removeImplicants
        , return . filterInvariantTransitions net
        , greedySimplify net FTrue
        , return . combineCuts
        , simplifyBySubsumption
        ]
        , second (S.fromList (transitions net) :) (formulaToCut f)
        , 2
        )

applySimpConfig :: SimpConfig -> [Cut] -> OptIO [SimpleCut]
applySimpConfig (simpFunctions, initialCut, otfIndex) cuts = do
            let (otfSimps, afterSimps) = splitAt otfIndex simpFunctions
            let simpFunction = foldl (>=>) return afterSimps
            let otfFunction = foldl (>=>) return otfSimps
            let cnfCuts = map cutToSimpleDNFCuts cuts
            dnfCuts <- foldM (combine otfFunction) [initialCut] cnfCuts
            simpFunction dnfCuts
        where
            combine simpFunction cs1 cs2 =
                simpFunction [ (c1c0 `S.union` c2c0, c1cs ++ c2cs)
                             | (c1c0, c1cs) <- cs1, (c2c0, c2cs) <- cs2 ]

generateCuts :: PetriNet -> Formula Transition -> [Cut] -> OptIO [SimpleCut]
generateCuts net f cuts = do
        let configs = [noSimp, simpWithFormula, simpWithoutFormula]
        auto <- opt optAuto
        simp <- opt optSimpMethod
        let simpConfig | auto = drop 1 configs
                       | simp >= 0 && simp < length configs = [configs !! simp]
                       | otherwise =
                           error ("Invalid simplification: " ++ show simp)
        let tasks = map (\c -> applySimpConfig (c net f) cuts) simpConfig
        rs <- parallelIO tasks
        when auto $ verbosePut 2 $
            "Number of disjuncts in tested simplifications: " ++ show (map length rs)
        return $ minimumBy (comparing length) rs

combineCuts :: [SimpleCut] -> [SimpleCut]
combineCuts cuts =
            M.toList $ M.fromListWithKey combineFunc cuts
        where
            combineFunc c0 cs cs' =
                simplifyPositiveCut c0 [ c `S.union` c' | c <- cs, c' <- cs' ]

filterInvariantTransitions :: PetriNet -> [SimpleCut] -> [SimpleCut]
filterInvariantTransitions net =
        let ts = S.fromList $ invariantTransitions net
        in  runIdentity . simplifyWithFilter (return . filterTransitions ts) isMoreGeneralCut

filterTransitions :: S.Set Transition -> SimpleCut -> (Bool, SimpleCut)
filterTransitions ts (c0, cs) =
        let c0' = c0 `S.difference` ts
            cs' = filter (S.null . S.intersection ts) cs
            changed = c0 /= c0' || cs /= cs'
        in  (changed, (c0', cs'))

invariantTransitions :: PetriNet -> [Transition]
invariantTransitions net = filter (\t -> lpre net t == lpost net t) $ transitions net

removeImplicants :: [SimpleCut] -> [SimpleCut]
removeImplicants = removeWith isMoreGeneralCut

simplifyCuts :: [SimpleCut] -> [SimpleCut]
simplifyCuts = mapMaybe simplifyCut

simplifyCut :: SimpleCut -> Maybe SimpleCut
simplifyCut (c0, cs) =
        let cs' = simplifyPositiveCut c0 cs
        in  if any S.null cs' then
                Nothing
            else
                Just (c0, cs')

simplifyPositiveCut :: S.Set Transition -> [S.Set Transition] -> [S.Set Transition]
simplifyPositiveCut c0 =
        removeWith S.isSubsetOf . map (`S.difference` c0)

simplifyBySubsumption :: [SimpleCut] -> OptIO [SimpleCut]
simplifyBySubsumption = simplifyBySubsumption' []

simplifyBySubsumption' :: [SimpleCut] -> [SimpleCut] -> OptIO [SimpleCut]
simplifyBySubsumption' acc [] = return $ reverse acc
simplifyBySubsumption' acc (c0:cs) = do
        -- TODO: check with prime implicants
        r <- checkSat $ checkSubsumptionSat c0 (acc ++ cs)
        let acc' = case r of
                    Nothing -> acc
                    Just _ -> c0:acc
        simplifyBySubsumption' acc' cs

simplifyWithFilter :: (Monad m) => (a -> m (Bool, a)) -> (a -> a -> Bool) -> [a] -> m [a]
simplifyWithFilter simp f = simpFilter []
        where
            simpFilter acc [] = return $ reverse acc
            simpFilter acc (x:xs) = do
                (changed, x') <- simp x
                if changed then
                    simpFilter (x' : notFilter x' acc) (notFilter x' xs)
                else
                    simpFilter (x' : acc) xs
            notFilter x = filter (not . f x)

removeWith :: (a -> a -> Bool) -> [a] -> [a]
removeWith f = removeCuts' []
        where
            removeCuts' acc [] = reverse acc
            removeCuts' acc (x:xs) = removeCuts' (x : notFilter x acc) (notFilter x xs)
            notFilter x = filter (not . f x)

-- c1 `isMoreGeneralCut` c2 <=> (c2 => c1)
isMoreGeneralCut :: SimpleCut -> SimpleCut -> Bool
isMoreGeneralCut (c1c0, c1cs) (c2c0, c2cs) =
        c1c0 `S.isSubsetOf` c2c0 && all (\c1 -> any (`S.isSubsetOf` c1) c2cs) c1cs

cutToSimpleDNFCuts :: Cut -> [SimpleCut]
cutToSimpleDNFCuts (ts, u) = (S.empty, [S.fromList u]) : map (\(_, t) -> (S.fromList t, [])) ts

-- TODO: allow formulas with or
formulaToCut :: Formula Transition -> SimpleCut
formulaToCut = transformF
        where
            transformF FTrue = (S.empty, [])
            transformF (p :&: q) =
                let (p0, ps) = transformF p
                    (q0, qs) = transformF q
                in  (p0 `S.union` q0, ps ++ qs)
            transformF (LinearInequation ts Gt (Const 0)) =
                (S.empty, [transformTerm ts])
            transformF (LinearInequation ts Ge (Const 1)) =
                (S.empty, [transformTerm ts])
            transformF (LinearInequation ts Eq (Const 0)) =
                (transformTerm ts, [])
            transformF (LinearInequation ts Le (Const 0)) =
                (transformTerm ts, [])
            transformF (LinearInequation ts Lt (Const 1)) =
                (transformTerm ts, [])
            transformF f =
                error $ "formula not supported for invariant: " ++ show f
            transformTerm (t :+: u) = transformTerm t `S.union` transformTerm u
            transformTerm (Var x) = S.singleton x
            transformTerm t =
                error $ "term not supported for invariant: " ++ show t

checkCut :: PetriNet -> Formula Transition -> SimpleCut -> OptIO Bool
checkCut net f cut =
        liftM isNothing $ checkSat $ checkTransitionInvariantWithSimpleCutSat net f cut

greedySimplifyCut :: PetriNet -> Formula Transition -> Bool -> SimpleCut ->
        SimpleCut-> OptIO (Bool, SimpleCut)
greedySimplifyCut net f changed cutAcc@(c0Acc, csAcc) (c0, cs) =
        case (S.null c0, cs) of
            (True, []) -> return (changed, cutAcc)
            (False, _) -> do
                let (c, c0') = S.deleteFindMin c0
                let cut = (c0Acc `S.union` c0', csAcc ++ cs)
                r <- checkCut net f cut
                greedySimplifyCut net f (r || changed)
                    (if r then cutAcc else (S.insert c c0Acc, csAcc)) (c0', cs)
            (True, c:cs') -> do
                let cut = (c0Acc `S.union` c0, csAcc ++ cs')
                r <- checkCut net f cut
                greedySimplifyCut net f (r || changed)
                    (if r then cutAcc else (c0Acc, c:csAcc)) (c0, cs')

greedySimplify :: PetriNet -> Formula Transition -> [SimpleCut] -> OptIO [SimpleCut]
greedySimplify net f =
        simplifyWithFilter (greedySimplifyCut net f False (S.empty, [])) isMoreGeneralCut

