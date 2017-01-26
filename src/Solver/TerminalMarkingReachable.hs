{-# LANGUAGE FlexibleContexts #-}

module Solver.TerminalMarkingReachable
    (checkTerminalMarkingReachableSat,
     TerminalMarkingReachableInvariant)
where

import Data.SBV
import Data.List (intercalate)
import qualified Data.Map as M

import Util
import PetriNet
import Property
import Solver
import StructuralComputation

type TerminalMarkingReachableInvariant = [BlockInvariant]
data BlockInvariant =
            BlockInvariant (Int, [Transition], IVector Place)

instance Invariant BlockInvariant where
        invariantSize (BlockInvariant (_, _, yi)) = size yi

instance Show BlockInvariant where
        show (BlockInvariant (i, ti, yi)) =
                "T_" ++ show i ++ ": " ++ show ti ++ "; " ++ intercalate " + " (map showWeighted (items yi))

nonNegativityConstraints :: (Ord a, Show a) => SIMap a -> SBool
nonNegativityConstraints m =
            bAnd $ map checkVal $ vals m
        where checkVal x = x .>= 0

checkTerminalMarkingReachable :: PetriNet -> [Triplet] -> Int -> [SIMap Place] -> SIMap Transition -> SBool
checkTerminalMarkingReachable net triplets k ys b =
        bAnd (map nonNegativityConstraints ys)
        -- farkas lemma constraints
        -- triplet constraints
        -- block constraints

checkTerminalMarkingReachableSat :: PetriNet -> [Triplet] -> Int -> ConstraintProblem Integer TerminalMarkingReachableInvariant
checkTerminalMarkingReachableSat net triplets k =
        let makeYName i = (++) (replicate i '\'')
            ys = [makeVarMapWith (makeYName i) $ places net | i <- [1..k]]
            b = makeVarMap $ transitions net
        in  ("terminal marking reachable", "invariant",
             concat (map getNames ys) ++ getNames b,
             \fm -> checkTerminalMarkingReachable net triplets k (map (fmap fm) ys) (fmap fm b),
             \fm -> invariantFromAssignment (map (fmap fm) ys) (fmap fm b))

invariantFromAssignment :: [IMap Place] -> IMap Transition -> TerminalMarkingReachableInvariant
invariantFromAssignment ys b = [BlockInvariant (1, [], buildVector [])]
