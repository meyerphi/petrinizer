{-# LANGUAGE FlexibleContexts #-}

module Solver.TerminalMarkingsUniqueConsensus
    (checkTerminalMarkingsUniqueConsensusSat,
     TerminalMarkingsUniqueConsensusCounterExample,
     findUnmarkedTrapSat,
     findGeneralizedSiphonConstraintsSat,
     checkGeneralizedCoTrapSat,
     StableInequality)
where

import Data.SBV
import qualified Data.Map as M
import Data.List ((\\))

import Util
import PetriNet
import Property
import Solver

type TerminalMarkingsUniqueConsensusCounterExample = (Marking, Marking, Marking, FiringVector, FiringVector)

type StableInequality = (IMap Place, Integer)

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
              checkPlace (p,w) = val m p .<= literal (fromInteger (w - 1))

initialMarkingConstraints :: PetriNet -> SIMap Place -> SBool
initialMarkingConstraints net m0 =
        sum (mval m0 (places net \\ initials net)) .== 0

differentConsensusConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SBool
differentConsensusConstraints net m1 m2 =
        (sum (mval m1 (yesStates net)) .> 0 &&& sum (mval m2 (noStates net)) .> 0)

checkTrap :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> Trap -> SBool
checkTrap net m0 m1 m2 x1 x2 trap =
            (markedByMarking m0 ==> (markedByMarking m1 &&& markedByMarking m2))
        where markedByMarking m = sum (mval m trap) .> 0
              markedBySequence x = sum (mval x (mpre net trap)) .> 0

checkTrapConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Trap] -> SBool
checkTrapConstraints net m0 m1 m2 x1 x2 traps =
        bAnd $ map (checkTrap net m0 m1 m2 x1 x2) traps

checkGeneralizedSiphon :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> Siphon -> SBool
checkGeneralizedSiphon net m0 m1 m2 x1 x2 siphon =
            ((unmarkedByMarking m0 &&& unmarkedBySequence x1) ==> (unmarkedByMarking m1)) &&&
            ((unmarkedByMarking m0 &&& unmarkedBySequence x2) ==> (unmarkedByMarking m2))
        where unmarkedByMarking m = sum (mval m siphon) .== 0
              unmarkedBySequence x = sum [ val x t | t <- (mpre net siphon \\ mpost net siphon) ] .== 0

checkGeneralizedSiphonConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Siphon] -> SBool
checkGeneralizedSiphonConstraints net m0 m1 m2 x1 x2 siphons =
        bAnd $ map (checkGeneralizedSiphon net m0 m1 m2 x1 x2) siphons

checkInequalityConstraint :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> StableInequality -> SBool
checkInequalityConstraint net m0 m1 m2 (k, c) =
            (checkInequality m0) ==> (checkInequality m1 &&& checkInequality m2)
        where checkInequality m = sum [ literal (val k p) * (val m p) | p <- places net ] .>= literal c

checkInequalityConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> [StableInequality] -> SBool
checkInequalityConstraints net m0 m1 m2 inequalities =
        bAnd [ checkInequalityConstraint net m0 m1 m2 i | i <- inequalities ]

checkTerminalMarkingsUniqueConsensus :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition ->
        [Trap] -> [Siphon] -> [StableInequality] -> SBool
checkTerminalMarkingsUniqueConsensus net m0 m1 m2 x1 x2 traps siphons inequalities =
        stateEquationConstraints net m0 m1 x1 &&&
        stateEquationConstraints net m0 m2 x2 &&&
        initialMarkingConstraints net m0 &&&
        nonNegativityConstraints m0 &&&
        nonNegativityConstraints m1 &&&
        nonNegativityConstraints m2 &&&
        nonNegativityConstraints x1 &&&
        nonNegativityConstraints x2 &&&
        terminalConstraints net m1 &&&
        terminalConstraints net m2 &&&
        differentConsensusConstraints net m1 m2 &&&
        checkTrapConstraints net m0 m1 m2 x1 x2 traps &&&
        checkGeneralizedSiphonConstraints net m0 m1 m2 x1 x2 siphons &&&
        checkInequalityConstraints net m0 m1 m2 inequalities

checkTerminalMarkingsUniqueConsensusSat :: PetriNet -> [Trap] -> [Siphon] -> [StableInequality] -> ConstraintProblem Integer TerminalMarkingsUniqueConsensusCounterExample
checkTerminalMarkingsUniqueConsensusSat net traps siphons inequalities =
        let m0 = makeVarMap $ places net
            m1 = makeVarMapWith prime $ places net
            m2 = makeVarMapWith (prime . prime) $ places net
            x1 = makeVarMap $ transitions net
            x2 = makeVarMapWith prime $ transitions net
        in  ("unique terminal marking", "(m0, m1, m2, x1, x2)",
             getNames m0 ++ getNames m1 ++ getNames m2 ++ getNames x1 ++ getNames x2,
             \fm -> checkTerminalMarkingsUniqueConsensus net (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2) traps siphons inequalities,
             \fm -> markingsFromAssignment (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2))

markingsFromAssignment :: IMap Place -> IMap Place -> IMap Place -> IMap Transition -> IMap Transition -> TerminalMarkingsUniqueConsensusCounterExample
markingsFromAssignment m0 m1 m2 x1 x2 =
        (makeVector m0, makeVector m1, makeVector m2, makeVector x1, makeVector x2)

-- trap and siphon refinement constraints

generalizedSiphonConstraints :: PetriNet -> FiringVector -> SIMap Place -> SBool
generalizedSiphonConstraints net x b =
            bAnd [ siphonConstraint t | t <- elems x ]
        where siphonConstraint t =
                sum (mval b $ post net t) .> 0 ==> sum (mval b $ pre net t) .> 0

trapConstraints :: PetriNet -> SIMap Place -> SBool
trapConstraints net b =
            bAnd $ map trapConstraint $ transitions net
        where trapConstraint t =
                  sum (mval b $ pre net t) .> 0 ==> sum (mval b $ post net t) .> 0

placesMarkedByMarking :: PetriNet -> Marking -> SIMap Place -> SBool
placesMarkedByMarking net m b = sum (mval b $ elems m) .> 0

placesUnmarkedByMarking :: PetriNet -> Marking -> SIMap Place -> SBool
placesUnmarkedByMarking net m b = sum (mval b $ elems m) .== 0

placesPostsetOfSequence :: PetriNet -> FiringVector -> SIMap Place -> SBool
placesPostsetOfSequence net x b = sum (mval b $ mpost net $ elems x) .> 0

placesPresetOfSequence :: PetriNet -> FiringVector -> SIMap Place -> SBool
placesPresetOfSequence net x b = sum (mval b $ mpre net $ elems x) .> 0

noOutputTransitionEnabled :: PetriNet -> Marking -> SIMap Place -> SBool
noOutputTransitionEnabled net m b =
            bAnd $ map outputTransitionNotEnabled $ transitions net
        where
            outputTransitionNotEnabled t = outputTransitionOfB t ==> transitionNotEnabledInB t
            outputTransitionOfB t = sum [val b p | (p, w) <- lpre net t, val m p >= w] .> 0
            transitionNotEnabledInB t = sum [val b p | (p, w) <- lpre net t, val m p < w] .> 0

nonemptySet :: (Ord a, Show a) => SIMap a -> SBool
nonemptySet b = sum (vals b) .> 0

checkBinary :: SIMap Place -> SBool
checkBinary = bAnd . map (\x -> x .== 0 ||| x .== 1) . vals

checkSizeLimit :: SIMap Place -> Maybe (Int, Integer) -> SBool
checkSizeLimit _ Nothing = true
checkSizeLimit b (Just (1, curSize)) = (.< literal curSize) $ sumVal b
checkSizeLimit b (Just (2, curSize)) = (.> literal curSize) $ sumVal b
checkSizeLimit _ (Just (_, _)) = error "minimization method not supported"

minimizeMethod :: Int -> Integer -> String
minimizeMethod 1 curSize = "size smaller than " ++ show curSize
minimizeMethod 2 curSize = "size larger than " ++ show curSize
minimizeMethod _ _ = error "minimization method not supported"

findUnmarkedTrap :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
findUnmarkedTrap net m0 m1 m2 x1 x2 b sizeLimit =
        placesMarkedByMarking net m0 b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        trapConstraints net b &&&
        ((placesUnmarkedByMarking net m1 b ||| placesUnmarkedByMarking net m2 b))

findUnmarkedTrapSat :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> MinConstraintProblem Integer Trap Integer
findUnmarkedTrapSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("trap marked in m and unmarked in m1 or m2, or marked by x1 and unmarked in m1, or marked by x2 and unmarked in m2", "trap",
             getNames b,
             \fm -> findUnmarkedTrap net m0 m1 m2 x1 x2 (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

findGeneralizedSiphonConstraints :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
findGeneralizedSiphonConstraints net m0 m1 m2 x1 x2 b sizeLimit =
        placesUnmarkedByMarking net m0 b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        (
            (generalizedSiphonConstraints net x1 b &&& placesMarkedByMarking net m1 b) |||
            (generalizedSiphonConstraints net x2 b &&& placesMarkedByMarking net m2 b)
        )

findGeneralizedSiphonConstraintsSat :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> MinConstraintProblem Integer Siphon Integer
findGeneralizedSiphonConstraintsSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("siphon (w.r.t. x1 or x2) not marked in m0 and marked in m1 or m2", "siphon",
             getNames b,
             \fm -> findGeneralizedSiphonConstraints net m0 m1 m2 x1 x2 (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

placesFromAssignment :: IMap Place -> ([Place], Integer)
placesFromAssignment b = (M.keys (M.filter (> 0) b), sum (M.elems b))

-- stable linear inequalities

checkStableInequalityForMarking :: PetriNet -> Marking -> SIMap Place -> SInteger -> SBool
checkStableInequalityForMarking net m k c =
        sum [ (val k p) * literal (val m p) | p <- places net ] .>= c

checkSemiPositiveConstraints :: (Ord a, Show a) => SIMap a -> SBool
checkSemiPositiveConstraints k =
            bAnd [ x .>= 0 | x <- vals k ]

checkSemiNegativeConstraints :: (Ord a, Show a) => SIMap a -> SBool
checkSemiNegativeConstraints k =
            bAnd [ x .<= 0 | x <- vals k ]

checkGeneralizedTCoTrap :: PetriNet -> SIMap Place -> SInteger -> Transition -> SBool
checkGeneralizedTCoTrap net k c t =
            checkTSurInvariant ||| checkTDisabled
        where checkTSurInvariant = sum output - sum input .>= c
              checkTDisabled = sum input .< c
              input = map addPlace $ lpre net t
              output = map addPlace $ lpost net t
              addPlace (p, w) = literal w * val k p

checkGeneralizedCoTrap :: PetriNet -> SIMap Place -> SInteger -> SBool
checkGeneralizedCoTrap net k c =
        bAnd [ checkGeneralizedTCoTrap net k c t | t <- transitions net ]

checkGeneralizedCoTrapConstraints :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> SIMap Place -> SInteger -> SBool
checkGeneralizedCoTrapConstraints net m0 m1 m2 x1 x2 k c =
        checkSemiNegativeConstraints k &&&
        checkGeneralizedCoTrap net k c &&&
        checkStableInequalityForMarking net m0 k c &&&
        ((bnot (checkStableInequalityForMarking net m1 k c)) ||| (bnot (checkStableInequalityForMarking net m2 k c)))

checkGeneralizedCoTrapSat :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> ConstraintProblem Integer StableInequality
checkGeneralizedCoTrapSat net m0 m1 m2 x1 x2 =
        let k = makeVarMap $ places net
            c = "'c"
        in  ("generalized co-trap (stable inequality) holding m but not in m1 or m2", "stable inequality",
             c : getNames k,
             \fm -> checkGeneralizedCoTrapConstraints net m0 m1 m2 x1 x2 (fmap fm k) (fm c),
             \fm -> stableInequalityFromAssignment (fmap fm k) (fm c))

stableInequalityFromAssignment :: IMap Place -> Integer -> StableInequality
stableInequalityFromAssignment k c = (k, c)

