{-# LANGUAGE FlexibleContexts #-}

module Solver.TerminalMarkingReachable
    (checkTerminalMarkingReachableSat,
     TerminalMarkingReachableInvariant)
where

import Data.SBV
import Data.List (intercalate,genericReplicate)
import qualified Data.Map as M

import Util
import PetriNet
import Property
import Solver
import StructuralComputation

type TerminalMarkingReachableInvariant = [BlockInvariant]
data BlockInvariant =
            BlockInvariant (Integer, [Transition], IVector Place)

instance Invariant BlockInvariant where
        invariantSize (BlockInvariant (_, ti, yi)) = if null ti then 0 else size yi

instance Show BlockInvariant where
        show (BlockInvariant (i, ti, yi)) =
                "T_" ++ show i ++ ":\n" ++ unlines (map show ti) ++
                    (if null ti then "" else "\nY_" ++ show i ++ ": " ++ intercalate " + " (map showWeighted (items yi)) ++ "\n")

nonNegativityConstraints :: (Ord a, Show a) => SIMap a -> SBool
nonNegativityConstraints m =
            bAnd $ map checkVal $ vals m
        where checkVal x = x .>= 0

checkNonNegativityConstraints :: (Ord a, Show a) => [SIMap a] -> SBool
checkNonNegativityConstraints xs =
            bAnd $ map nonNegativityConstraints xs

blockTerminationConstraints :: PetriNet -> Integer -> SIMap Transition -> SIMap Place -> SBool
blockTerminationConstraints net i b y =
            bAnd $ map checkTransition $ transitions net
        where checkTransition t =
                let incoming = map addPlace $ lpre net t
                    outgoing = map addPlace $ lpost net t
                in  (val b t .== literal i) ==> (sum outgoing - sum incoming .< 0)
              addPlace (p, w) = literal w * val y p

terminationConstraints :: PetriNet -> Integer -> SIMap Transition -> [SIMap Place] -> SBool
terminationConstraints net k b ys =
        bAnd $ [blockTerminationConstraints net i b y | (i,y) <- zip [1..] ys]

blockConstraints :: PetriNet -> Integer -> SIMap Transition -> SBool
blockConstraints net k b =
            bAnd $ map checkBlock $ transitions net
        where checkBlock t = literal 1 .<= val b t &&& val b t .<= literal k

blockOrderConstraints :: PetriNet -> [Triplet] -> Integer -> SIMap Transition -> SBool
blockOrderConstraints net triplets k b =
            bAnd $ map checkTriplet triplets
        where checkTriplet (s,t,ts) = (val b s .> val b t) ==> bOr (map (\t' -> val b t' .== val b t) ts)

checkTerminalMarkingReachable :: PetriNet -> [Triplet] -> Integer -> SIMap Transition -> [SIMap Place] -> SBool
checkTerminalMarkingReachable net triplets k b ys =
        blockConstraints net k b &&&
        terminationConstraints net k b ys &&&
        blockOrderConstraints net triplets k b &&&
        checkNonNegativityConstraints ys

checkTerminalMarkingReachableSat :: PetriNet -> [Triplet] -> Integer -> ConstraintProblem Integer TerminalMarkingReachableInvariant
checkTerminalMarkingReachableSat net triplets k =
        let makeYName i = (++) (genericReplicate i '\'')
            ys = [makeVarMapWith (makeYName i) $ places net | i <- [1..k]]
            b = makeVarMap $ transitions net
        in  ("terminal marking reachable", "invariant",
             concat (map getNames ys) ++ getNames b,
             \fm -> checkTerminalMarkingReachable net triplets k (fmap fm b) (map (fmap fm) ys),
             \fm -> invariantFromAssignment net k (fmap fm b) (map (fmap fm) ys))

invariantFromAssignment :: PetriNet -> Integer -> IMap Transition -> [IMap Place] -> TerminalMarkingReachableInvariant
invariantFromAssignment net k b ys =
        [BlockInvariant (i, M.keys (M.filter (== i) b), makeVector y) | (i,y) <- zip [1..] ys]
