module Solver.LivenessInvariant (
    checkLivenessInvariantSat
  , LivenessInvariant
  , invariantSize
  , cutToLivenessInvariant
  , SimpleCut
) where

import Data.SBV
import Data.List (intercalate)
import qualified Data.Map as M
import qualified Data.Set as S

import Util
import Solver
import Solver.Simplifier
import Property
import PetriNet

data LivenessInvariant =
            RankingFunction (SimpleCut, IVector Place)
          | ComponentCut (SimpleCut, [Trap]) -- TODO: add proof why 

instance Invariant LivenessInvariant where
        invariantSize (RankingFunction ((c0, cs), ps)) =
                S.size c0 + sum (map S.size cs) + size ps
        invariantSize (ComponentCut ((c0, cs), ps)) =
                S.size c0 + sum (map S.size cs) + sum (map length ps)

showSimpleCuts :: SimpleCut -> String
showSimpleCuts cs = intercalate " ∧ " (showSimpleCut cs)
        where showSimpleCut (ts0, cs1) =
                if S.null ts0 then
                    map (showTrans True) cs1
                else
                    showTrans False ts0 : map (showTrans True) cs1
              showTrans pos ts =
                  if pos then
                       let d = intercalate " ∨ "
                                (map (\t -> show t ++ " ∈ σ") (S.toList ts))
                       in  if S.size ts == 1 then d else "(" ++ d ++ ")"
                  else
                       intercalate " ∧ " (map (\t -> show t ++ " ∉ σ") (S.toList ts))

instance Show LivenessInvariant where
        show (RankingFunction (cs, xs)) =
                    "[" ++ showSimpleCuts cs ++ "]: " ++
                    intercalate " + " (map showWeighted (items xs))
        show (ComponentCut (cs, ps)) =
                    "[" ++ showSimpleCuts cs ++ "]: " ++
                    show ps

type NamedCut = (S.Set Transition, [(String, S.Set Transition)])

placeName :: Place -> String
placeName p = "@p" ++ show p

nameCut :: SimpleCut -> NamedCut
nameCut (c0, cs) = (c0, numPref "@comp" `zip` cs)

cutNames :: PetriNet -> NamedCut -> [String]
cutNames net (_, c) =
        ["@yone", "@comp0"] ++
        map placeName (places net) ++
        map fst c

cutToSimpleCNFCut :: Cut -> SimpleCut
cutToSimpleCNFCut (ts, u) = (S.fromList u, map (\(_, t) -> S.fromList t) ts)

toSimpleCut :: NamedCut -> SimpleCut
toSimpleCut (c0, ncs) = (c0, map snd ncs)

checkLivenessInvariant :: PetriNet -> NamedCut -> SIMap String -> SBool
checkLivenessInvariant net (comp0, comps) m =
            sAnd (map checkTransition (transitions net)) .&&
            val m "@yone" + sum (map addComp comps) .> 0 .&&
            sAnd (map (checkNonNegativity . placeName) (places net)) .&&
            checkNonNegativity "@yone" .&&
            checkNonNegativity "@comp0" .&&
            sAnd (map (\(n, _) -> checkNonNegativity n) comps)
        where checkTransition t =
                let incoming = map addPlace $ lpre net t
                    outgoing = map addPlace $ lpost net t
                    yone = val m "@yone"
                    addCompT (n, ts) = if t `S.member` ts then val m n else 0
                    comp0Val = addCompT ("@comp0", comp0)
                    compsVal = sum $ map addCompT comps
                in  sum outgoing - sum incoming + yone + compsVal .<= comp0Val
              addPlace (p,w) = literal w * val m (placeName p)
              addComp (n, _) = val m n
              checkNonNegativity x = val m x .>= 0

checkLivenessInvariantSat :: PetriNet -> Formula Transition -> SimpleCut -> ConstraintProblem Integer LivenessInvariant
checkLivenessInvariantSat net f (c0, cs) =
        -- TODO: use own variables for formula cut
        let (f0, fs) = formulaToCut f
            c0' = c0 `S.union` f0
            cut = (c0', simplifyPositiveCut c0' (cs ++ fs))
            namedCut = nameCut cut
            names = cutNames net namedCut
            myVarMap fvm = M.fromList $ names `zip` fmap fvm names
        in  ("liveness invariant constraints", "liveness invariant",
             names,
             checkLivenessInvariant net namedCut . myVarMap,
             getLivenessInvariant net namedCut . myVarMap)

cutToLivenessInvariant :: Cut -> LivenessInvariant
cutToLivenessInvariant c = ComponentCut (cutToSimpleCNFCut c, map fst (fst c))

getLivenessInvariant :: PetriNet -> NamedCut -> IMap String -> LivenessInvariant
getLivenessInvariant net cut y =
        RankingFunction
                (toSimpleCut cut,
                 buildVector (map (\p -> (p, val y (placeName p))) (places net)))
