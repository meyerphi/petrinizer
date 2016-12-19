{-# LANGUAGE FlexibleContexts #-}

module Solver.UniqueTerminalMarking
    (checkUniqueTerminalMarkingSat,
     checkUnmarkedTrapSat)
where

import Data.SBV
import qualified Data.Map as M

import Util
import PetriNet
import Property
import Solver

stateEquationConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Transition -> SBool
stateEquationConstraints net m0 m x =
            bAnd $ map checkStateEquation $ places net
        where checkStateEquation p =
                let incoming = map addTransition $ lpre net p
                    outgoing = map addTransition $ lpost net p
                in  val m0 p + sum incoming - sum outgoing .== val m p
              addTransition (t,w) = literal w * val x t

nonNegativityConstraints :: (Ord a, Show a) => SIMap a -> SBool
nonNegativityConstraints m =
            bAnd $ map checkVal $ vals m
        where checkVal x = x .>= 0

terminalConstraints :: PetriNet -> SIMap Place -> SBool
terminalConstraints net m =
            bAnd $ map checkTransition $ transitions net
        where checkTransition t = bOr $ map checkPlace $ lpre net t
              checkPlace (p,w) = val m p .< literal w

nonEqualityConstraints :: (Ord a, Show a) => PetriNet -> SIMap a -> SIMap a -> SBool
nonEqualityConstraints net m1 m2 =
            if elemsSet m1 /= elemsSet m2 then
                false
            else
                bOr $ map checkNonEquality $ elems m1
        where checkNonEquality x = val m1 x ./= val m2 x

checkTrap :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> Trap -> SBool
checkTrap net m0 m1 m2 x1 x2 trap =
            checkMarkingDelta m0 m1 &&&
            checkMarkingDelta m0 m2 &&&
            checkSequenceDelta x1 m1 &&&
            checkSequenceDelta x2 m2
        where checkMarkingDelta m0 m =
                sum (map (val m0) trap) .>= 1 ==> sum (map (val m) trap) .>= 1
              checkSequenceDelta x m =
                sum (map (val x) (mpre net trap)) .>= 1 ==> sum (map (val m) trap) .>= 1

checkTrapConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Trap] -> SBool
checkTrapConstraints net m0 m1 m2 x1 x2 traps =
        bAnd $ map (checkTrap net m0 m1 m2 x1 x2) traps

checkUniqueTerminalMarking :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Trap] -> SBool
checkUniqueTerminalMarking net m0 m1 m2 x1 x2 traps =
        nonEqualityConstraints net m1 m2 &&&
        stateEquationConstraints net m0 m1 x1 &&&
        stateEquationConstraints net m0 m2 x2 &&&
        nonNegativityConstraints m0 &&&
        nonNegativityConstraints m1 &&&
        nonNegativityConstraints m2 &&&
        nonNegativityConstraints x1 &&&
        nonNegativityConstraints x2 &&&
        terminalConstraints net m1 &&&
        terminalConstraints net m2 &&&
        checkTrapConstraints net m0 m1 m2 x1 x2 traps

checkUniqueTerminalMarkingSat :: PetriNet -> [Trap] -> ConstraintProblem Integer (Marking, Marking, Marking, FiringVector, FiringVector)
checkUniqueTerminalMarkingSat net traps =
        let m0 = makeVarMap $ places net
            m1 = makeVarMapWith prime $ places net
            m2 = makeVarMapWith (prime . prime) $ places net
            x1 = makeVarMap $ transitions net
            x2 = makeVarMapWith prime $ transitions net
        in  ("unique terminal marking", "(m0, m1, m2, x1, x2)",
             getNames m0 ++ getNames m1 ++ getNames m2 ++ getNames x1 ++ getNames x2,
             \fm -> checkUniqueTerminalMarking net (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2) traps,
             \fm -> markingsFromAssignment (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2))

markingsFromAssignment :: IMap Place -> IMap Place -> IMap Place -> IMap Transition -> IMap Transition -> (Marking, Marking, Marking, FiringVector, FiringVector)
markingsFromAssignment m0 m1 m2 x1 x2 = (makeVector m0, makeVector m1, makeVector m2, makeVector x1, makeVector x2)

-- trap refinement constraints

trapConstraints :: PetriNet -> SBMap Place -> SBool
trapConstraints net b =
            bAnd $ map trapConstraint $ transitions net
        where trapConstraint t =
                  bOr (mval b (pre net t)) ==> bOr (mval b (post net t))

trapMarkedByMarking :: PetriNet -> Marking -> SBMap Place -> SBool
trapMarkedByMarking net m b = bOr $ mval b $ elems m

trapMarkedBySequence :: PetriNet -> FiringVector -> SBMap Place -> SBool
trapMarkedBySequence net x b = bOr $ mval b $ mpost net $ elems x

trapUnassigned :: Marking -> SBMap Place -> SBool
trapUnassigned m b = bAnd $ map (bnot . val b) $ elems m

properTrap :: SBMap Place -> SBool
properTrap b = bOr $ vals b

checkUnmarkedTrap :: PetriNet -> Marking -> Marking -> FiringVector -> SBMap Place -> SBool
checkUnmarkedTrap net m0 m x b =
        trapConstraints net b &&&
        (trapMarkedByMarking net m0 b ||| trapMarkedBySequence net x b) &&&
        trapUnassigned m b &&&
        properTrap b

checkUnmarkedTrapSat :: PetriNet -> Marking -> Marking -> FiringVector -> ConstraintProblem Bool Trap
checkUnmarkedTrapSat net m0 m x =
        let b = makeVarMap $ places net
        in  ("unmarked trap marked by sequence or initial marking", "trap",
             getNames b,
             \fm -> checkUnmarkedTrap net m0 m x (fmap fm b),
             \fm -> trapFromAssignment (fmap fm b))

trapFromAssignment :: BMap Place -> Trap
trapFromAssignment b = M.keys $ M.filter id b
