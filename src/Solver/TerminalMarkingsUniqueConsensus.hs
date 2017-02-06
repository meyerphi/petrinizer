{-# LANGUAGE FlexibleContexts #-}

module Solver.TerminalMarkingsUniqueConsensus
    (checkTerminalMarkingsUniqueConsensusSat,
     TerminalMarkingsUniqueConsensusCounterExample,
     checkUnmarkedTrapSat,
     checkGeneralizedSiphonConstraintsSat)
where

import Data.SBV
import qualified Data.Map as M
import Data.List ((\\))

import Util
import PetriNet
import Property
import Solver

type TerminalMarkingsUniqueConsensusCounterExample = (Marking, Marking, Marking, FiringVector, FiringVector)

stateEquationConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Transition -> SBool
stateEquationConstraints net m0 m x =
            bAnd $ map checkStateEquation $ places net
        where checkStateEquation p =
                let incoming = map addTransition $ lpre net p
                    outgoing = map addTransition $ lpost net p
                in  val m0 p + sum incoming - sum outgoing .== val m p
              addTransition (t,w) = literal (fromInteger w) * val x t

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
        (sum (mval m1 (yesStates net)) .> 0 &&& sum (mval m2 (noStates net)) .> 0) |||
        (sum (mval m1 (noStates net)) .> 0 &&& sum (mval m2 (yesStates net)) .> 0)

checkTrap :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> Trap -> SBool
checkTrap net m0 m1 m2 x1 x2 trap =
            (markedByMarking m0 ==> (markedByMarking m1 &&& markedByMarking m2)) &&&
            (markedBySequence x1 ==> markedByMarking m1) &&&
            (markedBySequence x2 ==> markedByMarking m2)
        where markedByMarking m = sum (mval m trap) .> 0
              markedBySequence x = sum (mval x (mpre net trap)) .> 0

checkTrapConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Trap] -> SBool
checkTrapConstraints net m0 m1 m2 x1 x2 traps =
        bAnd $ map (checkTrap net m0 m1 m2 x1 x2) traps

checkSiphon :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> Siphon -> SBool
checkSiphon net m0 m1 m2 x1 x2 siphon =
            noTransitionEnabledByMarking m0 ==> (notPresetOfSequence x1 &&& notPresetOfSequence x2)
        where noTransitionEnabledByMarking m = bAnd $ map (notEnabledByMarkingInSiphon m) $ mpost net siphon
              notEnabledByMarkingInSiphon m t = bOr $ [val m p .< literal w | (p, w) <- lpre net t, p `elem` siphon]
              notPresetOfSequence x = sum (mval x (mpost net siphon)) .== 0

checkSiphonConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> [Siphon] -> SBool
checkSiphonConstraints net m0 m1 m2 x1 x2 siphons =
        bAnd $ map (checkSiphon net m0 m1 m2 x1 x2) siphons

checkTerminalMarkingsUniqueConsensus :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition ->
        [Trap] -> [Siphon] -> SBool
checkTerminalMarkingsUniqueConsensus net m0 m1 m2 x1 x2 traps siphons =
        initialMarkingConstraints net m0 &&&
        differentConsensusConstraints net m1 m2 &&&
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

checkTerminalMarkingsUniqueConsensusSat :: PetriNet -> [Trap] -> [Siphon] -> ConstraintProblem Integer TerminalMarkingsUniqueConsensusCounterExample
checkTerminalMarkingsUniqueConsensusSat net traps siphons =
        let m0 = makeVarMap $ places net
            m1 = makeVarMapWith prime $ places net
            m2 = makeVarMapWith (prime . prime) $ places net
            x1 = makeVarMap $ transitions net
            x2 = makeVarMapWith prime $ transitions net
        in  ("unique terminal marking", "(m0, m1, m2, x1, x2)",
             getNames m0 ++ getNames m1 ++ getNames m2 ++ getNames x1 ++ getNames x2,
             \fm -> checkTerminalMarkingsUniqueConsensus net (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2) traps siphons,
             \fm -> markingsFromAssignment (fmap fm m0) (fmap fm m1) (fmap fm m2) (fmap fm x1) (fmap fm x2))

markingsFromAssignment :: IMap Place -> IMap Place -> IMap Place -> IMap Transition -> IMap Transition -> TerminalMarkingsUniqueConsensusCounterExample
markingsFromAssignment m0 m1 m2 x1 x2 =
        (makeVector m0, makeVector m1, makeVector m2, makeVector x1, makeVector x2)

-- trap and siphon refinement constraints

siphonConstraints :: PetriNet -> Marking -> SIMap Place -> SBool
siphonConstraints net m0 b =
            bAnd $ map siphonConstraint $ transitions net
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

checkUnmarkedTrap :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
checkUnmarkedTrap net m0 m1 m2 x1 x2 b sizeLimit =
        trapConstraints net b &&&
        nonemptySet b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        (
            (placesMarkedByMarking net m0 b &&& (placesUnmarkedByMarking net m1 b ||| placesUnmarkedByMarking net m2 b)) |||
            (placesPostsetOfSequence net x1 b &&& placesUnmarkedByMarking net m1 b) |||
            (placesPostsetOfSequence net x2 b &&& placesUnmarkedByMarking net m2 b)
        )

checkUnmarkedTrapSat :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> MinConstraintProblem Integer Trap Integer
checkUnmarkedTrapSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("trap marked in m and unmarked in m1 or m2, or marked by x1 and unmarked in m1, or marked by x2 and unmarked in m2", "trap",
             getNames b,
             \fm -> checkUnmarkedTrap net m0 m1 m2 x1 x2 (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

checkGeneralizedSiphonConstraints :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
checkGeneralizedSiphonConstraints net m0 m1 m2 x1 x2 b sizeLimit =
        siphonConstraints net m0 b &&&
        nonemptySet b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        noOutputTransitionEnabled net m0 b &&&
        (placesPresetOfSequence net x1 b ||| placesPresetOfSequence net x2 b)

checkGeneralizedSiphonConstraintsSat :: PetriNet -> Marking -> Marking -> Marking -> FiringVector -> FiringVector -> MinConstraintProblem Integer Siphon Integer
checkGeneralizedSiphonConstraintsSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("siphon not enabling any output transitions in m0 and used as input in x1 or x2", "siphon",
             getNames b,
             \fm -> checkGeneralizedSiphonConstraints net m0 m1 m2 x1 x2 (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

placesFromAssignment :: IMap Place -> ([Place], Integer)
placesFromAssignment b = (M.keys (M.filter (> 0) b), sum (M.elems b))
