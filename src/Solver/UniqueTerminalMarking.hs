{-# LANGUAGE FlexibleContexts #-}

module Solver.UniqueTerminalMarking
    (checkUniqueTerminalMarkingSat,
     checkUnmarkedTrapSat,
     checkUnmarkedSiphonSat)
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
            (markedByMarking m0 ==> (markedByMarking m1 &&& markedByMarking m2)) &&&
            (markedBySequence x1 ==> markedByMarking m1) &&&
            (markedBySequence x2 ==> markedByMarking m2)
        where markedByMarking m = sum (map (val m) trap) .>= 1
              markedBySequence x = sum (map (val x) (mpre net trap)) .>= 1

checkTrapConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Trap] -> SBool
checkTrapConstraints net m0 m1 m2 x1 x2 traps =
        bAnd $ map (checkTrap net m0 m1 m2 x1 x2) traps

checkSiphon :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> Siphon -> SBool
checkSiphon net m0 m1 m2 x1 x2 siphon =
            unmarkedByMarking m0 ==> (unmarkedByMarking m1 &&& unmarkedByMarking m2 &&& notPresetOfSequence x1 &&& notPresetOfSequence x2)
        where unmarkedByMarking m = sum (map (val m) siphon) .== 0
              notPresetOfSequence x = sum (map (val x) (mpost net siphon)) .== 0

checkSiphonConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Siphon] -> SBool
checkSiphonConstraints net m0 m1 m2 x1 x2 siphons =
        bAnd $ map (checkSiphon net m0 m1 m2 x1 x2) siphons

checkUniqueTerminalMarking :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition ->
        [Trap] -> [Siphon] -> SBool
checkUniqueTerminalMarking net m0 m1 m2 x1 x2 traps siphons =
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
        checkTrapConstraints net m0 m1 m2 x1 x2 traps &&&
        checkSiphonConstraints net m0 m1 m2 x1 x2 siphons

checkUniqueTerminalMarkingSat :: PetriNet -> [Trap] -> [Siphon] -> ConstraintProblem Integer (Marking, Marking, Marking, FiringVector, FiringVector)
checkUniqueTerminalMarkingSat net traps siphons =
        let m0 = makeVarMap $ places net
            m1 = makeVarMapWith prime $ places net
            m2 = makeVarMapWith (prime . prime) $ places net
            x1 = makeVarMap $ transitions net
            x2 = makeVarMapWith prime $ transitions net
        in  ("unique terminal marking", "(m0, m1, m2, x1, x2)",
             getNames m0 ++ getNames m1 ++ getNames m2 ++ getNames x1 ++ getNames x2,
             \fm -> checkUniqueTerminalMarking net (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2) traps siphons,
             \fm -> markingsFromAssignment (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2))

markingsFromAssignment :: IMap Place -> IMap Place -> IMap Place -> IMap Transition -> IMap Transition -> (Marking, Marking, Marking, FiringVector, FiringVector)
markingsFromAssignment m0 m1 m2 x1 x2 = (makeVector m0, makeVector m1, makeVector m2, makeVector x1, makeVector x2)

-- trap and siphon refinement constraints

siphonConstraints :: PetriNet -> SBMap Place -> SBool
siphonConstraints net b =
            bAnd $ map siphonConstraint $ transitions net
        where siphonConstraint t =
                  bOr (mval b (post net t)) ==> bOr (mval b (pre net t))

trapConstraints :: PetriNet -> SBMap Place -> SBool
trapConstraints net b =
            bAnd $ map trapConstraint $ transitions net
        where trapConstraint t =
                  bOr (mval b (pre net t)) ==> bOr (mval b (post net t))

placesMarkedByMarking :: PetriNet -> Marking -> SBMap Place -> SBool
placesMarkedByMarking net m b = bOr $ mval b $ elems m

placesUnmarkedByMarking :: PetriNet -> Marking -> SBMap Place -> SBool
placesUnmarkedByMarking net m b = bAnd $ map (bnot . val b) $ elems m

placesPostsetOfSequence :: PetriNet -> FiringVector -> SBMap Place -> SBool
placesPostsetOfSequence net x b = bOr $ mval b $ mpost net $ elems x

placesPresetOfSequence :: PetriNet -> FiringVector -> SBMap Place -> SBool
placesPresetOfSequence net x b = bOr $ mval b $ mpre net $ elems x

nonemptySet :: (Ord a, Show a) => SBMap a -> SBool
nonemptySet b = bOr $ vals b

checkUnmarkedTrap :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> SBMap Place -> SBool
checkUnmarkedTrap net m0 m1 m2 x1 x2 b =
        trapConstraints net b &&&
        nonemptySet b &&&
        (
            (placesMarkedByMarking net m0 b &&& (placesUnmarkedByMarking net m1 b ||| placesUnmarkedByMarking net m2 b)) |||
            (placesPostsetOfSequence net x1 b &&& placesUnmarkedByMarking net m1 b) |||
            (placesPostsetOfSequence net x2 b &&& placesUnmarkedByMarking net m2 b)
        )

checkUnmarkedTrapSat :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> ConstraintProblem Bool Siphon
checkUnmarkedTrapSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  ("trap marked in m and unmarked in m1 or m2, or marked by x1 and unmarked in m1, or marked by x2 and unmarked in m2", "trap",
             getNames b,
             \fm -> checkUnmarkedTrap net m0 m1 m2 x1 x2 (fmap fm b),
             \fm -> placesFromAssignment (fmap fm b))

checkUnmarkedSiphon :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> SBMap Place -> SBool
checkUnmarkedSiphon net m0 m1 m2 x1 x2 b =
        siphonConstraints net b &&&
        nonemptySet b &&&
        (placesUnmarkedByMarking net m0 b &&&
            (placesMarkedByMarking net m1 b ||| placesMarkedByMarking net m2 b |||
             placesPresetOfSequence net x1 b ||| placesPresetOfSequence net x2 b)
        )

checkUnmarkedSiphonSat :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> ConstraintProblem Bool Siphon
checkUnmarkedSiphonSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  ("siphon unmarked in m0 and marked in m1 or m2 or used as input in x1 or x2", "siphon",
             getNames b,
             \fm -> checkUnmarkedSiphon net m0 m1 m2 x1 x2 (fmap fm b),
             \fm -> placesFromAssignment (fmap fm b))

placesFromAssignment :: BMap Place -> Trap
placesFromAssignment b = M.keys $ M.filter id b
