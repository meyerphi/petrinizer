{-# LANGUAGE FlexibleContexts #-}

module Solver.NonConsensusTerminalMarking
    (checkNonConsensusTerminalMarkingSat,
     NonConsensusTerminalMarkingCounterExample,
     checkUnmarkedTrapSat,
     checkUnmarkedSiphonSat)
where

import Data.SBV
import qualified Data.Map as M
import Data.List ((\\))

import Util
import PetriNet
import Property
import Solver

type NonConsensusTerminalMarkingCounterExample = (RMarking, RMarking, RFiringVector)

stateEquationConstraints :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Transition -> SBool
stateEquationConstraints net m0 m x =
            bAnd $ map checkStateEquation $ places net
        where checkStateEquation p =
                let incoming = map addTransition $ lpre net p
                    outgoing = map addTransition $ lpost net p
                in  val m0 p + sum incoming - sum outgoing .== val m p
              addTransition (t,w) = literal (fromInteger w) * val x t

nonNegativityConstraints :: (Ord a, Show a) => SRMap a -> SBool
nonNegativityConstraints m =
            bAnd $ map checkVal $ vals m
        where checkVal x = x .>= 0

terminalMarkingConstraints :: PetriNet -> SRMap Place -> SBool
terminalMarkingConstraints net m =
            bAnd $ map checkTransition $ transitions net
        where checkTransition t = bOr $ map checkPlace $ lpre net t
              checkPlace (p,w) = val m p .== 0

initialMarkingConstraints :: PetriNet -> SRMap Place -> SBool
initialMarkingConstraints net m0 =
        sum (mval m0 (places net \\ initials net)) .== 0

nonConsensusStateConstraints :: PetriNet -> SRMap Place -> SBool
nonConsensusStateConstraints net m =
        sum (mval m (yesStates net)) .> 0 &&&
        sum (mval m (noStates net)) .> 0

checkTrap :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Transition -> Trap -> SBool
checkTrap net m0 m x trap =
            (markedByMarking m0 ==> markedByMarking m) &&&
            (markedBySequence x ==> markedByMarking m)
        where markedByMarking m = sum (mval m trap) .> 0
              markedBySequence x = sum (mval x (mpre net trap)) .> 0

checkTrapConstraints :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Transition -> [Trap] -> SBool
checkTrapConstraints net m0 m x traps =
        bAnd $ map (checkTrap net m0 m x) traps

checkSiphon :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Transition -> Siphon -> SBool
checkSiphon net m0 m x siphon =
            unmarkedByMarking m0 ==> (unmarkedByMarking m &&& notPresetOfSequence x)
        where unmarkedByMarking m = sum (mval m siphon) .== 0
              notPresetOfSequence x = sum (mval x (mpost net siphon)) .== 0

checkSiphonConstraints :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Transition -> [Siphon] -> SBool
checkSiphonConstraints net m0 m x siphons =
        bAnd $ map (checkSiphon net m0 m x) siphons

checkNonConsensusTerminalMarking :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Transition -> [Trap] -> [Siphon] -> SBool
checkNonConsensusTerminalMarking net m0 m x traps siphons =
        stateEquationConstraints net m0 m x &&&
        nonNegativityConstraints m0 &&&
        nonNegativityConstraints m &&&
        nonNegativityConstraints x &&&
        initialMarkingConstraints net m0 &&&
        terminalMarkingConstraints net m &&&
        nonConsensusStateConstraints net m &&&
        checkTrapConstraints net m0 m x traps &&&
        checkSiphonConstraints net m0 m x siphons

checkNonConsensusTerminalMarkingSat :: PetriNet -> [Trap] -> [Siphon] -> ConstraintProblem AlgReal NonConsensusTerminalMarkingCounterExample
checkNonConsensusTerminalMarkingSat net traps siphons =
        let m0 = makeVarMap $ places net
            m = makeVarMapWith prime $ places net
            x = makeVarMap $ transitions net
        in  ("non-consensus state", "(m0, m, x)",
             getNames m0 ++ getNames m ++ getNames x,
             \fm -> checkNonConsensusTerminalMarking net (fmap fm m0) (fmap fm m) (fmap fm x) traps siphons,
             \fm -> markingsFromAssignment (fmap fm m0) (fmap fm m) (fmap fm x))

markingsFromAssignment :: RMap Place -> RMap Place -> RMap Transition -> NonConsensusTerminalMarkingCounterExample
markingsFromAssignment m0 m x =
        (makeVector m0, makeVector m, makeVector x)

-- trap and siphon refinement constraints

siphonConstraints :: PetriNet -> SIMap Place -> SBool
siphonConstraints net b =
            bAnd $ map siphonConstraint $ transitions net
        where siphonConstraint t =
                  sum (mval b $ post net t) .> 0 ==> sum (mval b $ pre net t) .> 0

trapConstraints :: PetriNet -> SIMap Place -> SBool
trapConstraints net b =
            bAnd $ map trapConstraint $ transitions net
        where trapConstraint t =
                  sum (mval b $ pre net t) .> 0 ==> sum (mval b $ post net t) .> 0

placesMarkedByMarking :: PetriNet -> RMarking -> SIMap Place -> SBool
placesMarkedByMarking net m b = sum (mval b $ elems m) .> 0

placesUnmarkedByMarking :: PetriNet -> RMarking -> SIMap Place -> SBool
placesUnmarkedByMarking net m b = sum (mval b $ elems m) .== 0

placesPostsetOfSequence :: PetriNet -> RFiringVector -> SIMap Place -> SBool
placesPostsetOfSequence net x b = sum (mval b $ mpost net $ elems x) .> 0

placesPresetOfSequence :: PetriNet -> RFiringVector -> SIMap Place -> SBool
placesPresetOfSequence net x b = sum (mval b $ mpre net $ elems x) .> 0

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

checkUnmarkedTrap :: PetriNet -> RMarking -> RMarking -> RFiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
checkUnmarkedTrap net m0 m x b sizeLimit =
        trapConstraints net b &&&
        nonemptySet b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        (
            (placesMarkedByMarking net m0 b &&& placesUnmarkedByMarking net m b) |||
            (placesPostsetOfSequence net x b &&& placesUnmarkedByMarking net m b)
        )

checkUnmarkedTrapSat :: PetriNet -> RMarking -> RMarking -> RFiringVector -> MinConstraintProblem Integer Trap Integer
checkUnmarkedTrapSat net m0 m x =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("trap marked in m and unmarked in m, or marked by x and unmarked in m", "trap",
             getNames b,
             \fm -> checkUnmarkedTrap net m0 m x (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

checkUnmarkedSiphon :: PetriNet -> RMarking -> RMarking -> RFiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
checkUnmarkedSiphon net m0 m x b sizeLimit =
        siphonConstraints net b &&&
        nonemptySet b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        (placesUnmarkedByMarking net m0 b &&& (placesMarkedByMarking net m b ||| placesPresetOfSequence net x b))

checkUnmarkedSiphonSat :: PetriNet -> RMarking -> RMarking -> RFiringVector -> MinConstraintProblem Integer Siphon Integer
checkUnmarkedSiphonSat net m0 m x =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("siphon unmarked in m0 and marked in m or used as input in x", "siphon",
             getNames b,
             \fm -> checkUnmarkedSiphon net m0 m x (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

placesFromAssignment :: IMap Place -> ([Place], Integer)
placesFromAssignment b = (M.keys (M.filter (> 0) b), sum (M.elems b))
