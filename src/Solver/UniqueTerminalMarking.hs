{-# LANGUAGE FlexibleContexts #-}

module Solver.UniqueTerminalMarking
    (checkUniqueTerminalMarkingSat,
     UniqueTerminalMarkingCounterExample,
     checkUnmarkedTrapSat,
     checkUnmarkedSiphonSat)
where

import Data.SBV
import qualified Data.Map as M

import Util
import PetriNet
import Property
import Solver

type UniqueTerminalMarkingCounterExample = (RMarking, RMarking, RMarking, RFiringVector, RFiringVector)

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

terminalConstraints :: PetriNet -> SRMap Place -> SBool
terminalConstraints net m =
            bAnd $ map checkTransition $ transitions net
        where checkTransition t = bOr $ map checkPlace $ lpre net t
              checkPlace (p,w) = val m p .== 0

nonEqualityConstraints :: (Ord a, Show a) => PetriNet -> SRMap a -> SRMap a -> SBool
nonEqualityConstraints net m1 m2 =
            if elemsSet m1 /= elemsSet m2 then
                false
            else
                bOr $ map checkNonEquality $ elems m1
        where checkNonEquality x = val m1 x ./= val m2 x

checkTrap :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Place -> SRMap Transition -> SRMap Transition -> Trap -> SBool
checkTrap net m0 m1 m2 x1 x2 trap =
            (markedByMarking m0 ==> (markedByMarking m1 &&& markedByMarking m2)) &&&
            (markedBySequence x1 ==> markedByMarking m1) &&&
            (markedBySequence x2 ==> markedByMarking m2)
        where markedByMarking m = sum (map (val m) trap) .> 0
              markedBySequence x = sum (map (val x) (mpre net trap)) .> 0

checkTrapConstraints :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Place -> SRMap Transition -> SRMap Transition -> [Trap] -> SBool
checkTrapConstraints net m0 m1 m2 x1 x2 traps =
        bAnd $ map (checkTrap net m0 m1 m2 x1 x2) traps

checkSiphon :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Place -> SRMap Transition -> SRMap Transition -> Siphon -> SBool
checkSiphon net m0 m1 m2 x1 x2 siphon =
            unmarkedByMarking m0 ==> (unmarkedByMarking m1 &&& unmarkedByMarking m2 &&& notPresetOfSequence x1 &&& notPresetOfSequence x2)
        where unmarkedByMarking m = sum (map (val m) siphon) .== 0
              notPresetOfSequence x = sum (map (val x) (mpost net siphon)) .== 0

checkSiphonConstraints :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Place -> SRMap Transition -> SRMap Transition -> [Siphon] -> SBool
checkSiphonConstraints net m0 m1 m2 x1 x2 siphons =
        bAnd $ map (checkSiphon net m0 m1 m2 x1 x2) siphons

checkUniqueTerminalMarking :: PetriNet -> SRMap Place -> SRMap Place -> SRMap Place -> SRMap Transition -> SRMap Transition ->
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

checkUniqueTerminalMarkingSat :: PetriNet -> [Trap] -> [Siphon] -> ConstraintProblem AlgReal UniqueTerminalMarkingCounterExample
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

markingsFromAssignment :: RMap Place -> RMap Place -> RMap Place -> RMap Transition -> RMap Transition -> UniqueTerminalMarkingCounterExample
markingsFromAssignment m0 m1 m2 x1 x2 =
        (makeVector m0, makeVector m1, makeVector m2, makeVector x1, makeVector x2)

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

checkUnmarkedTrap :: PetriNet -> RMarking -> RMarking -> RMarking -> RFiringVector -> RFiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
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

checkUnmarkedTrapSat :: PetriNet -> RMarking -> RMarking -> RMarking -> RFiringVector -> RFiringVector -> MinConstraintProblem Integer Trap Integer
checkUnmarkedTrapSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("trap marked in m and unmarked in m1 or m2, or marked by x1 and unmarked in m1, or marked by x2 and unmarked in m2", "trap",
             getNames b,
             \fm -> checkUnmarkedTrap net m0 m1 m2 x1 x2 (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

checkUnmarkedSiphon :: PetriNet -> RMarking -> RMarking -> RMarking -> RFiringVector -> RFiringVector -> SIMap Place -> Maybe (Int, Integer) -> SBool
checkUnmarkedSiphon net m0 m1 m2 x1 x2 b sizeLimit =
        siphonConstraints net b &&&
        nonemptySet b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        (placesUnmarkedByMarking net m0 b &&&
            (placesMarkedByMarking net m1 b ||| placesMarkedByMarking net m2 b |||
             placesPresetOfSequence net x1 b ||| placesPresetOfSequence net x2 b)
        )

checkUnmarkedSiphonSat :: PetriNet -> RMarking -> RMarking -> RMarking -> RFiringVector -> RFiringVector -> MinConstraintProblem Integer Siphon Integer
checkUnmarkedSiphonSat net m0 m1 m2 x1 x2 =
        let b = makeVarMap $ places net
        in  (minimizeMethod, \sizeLimit ->
            ("siphon unmarked in m0 and marked in m1 or m2 or used as input in x1 or x2", "siphon",
             getNames b,
             \fm -> checkUnmarkedSiphon net m0 m1 m2 x1 x2 (fmap fm b) sizeLimit,
             \fm -> placesFromAssignment (fmap fm b)))

placesFromAssignment :: IMap Place -> ([Place], Integer)
placesFromAssignment b = (M.keys (M.filter (> 0) b), sum (M.elems b))
