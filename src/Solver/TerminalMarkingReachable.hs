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

checkTerminalMarkingReachable :: PetriNet -> [Triplet] -> Integer -> SIMap Transition -> [SIMap Place] -> Maybe (Int, (Int, [Int])) -> SBool
checkTerminalMarkingReachable net triplets k b ys sizeLimit =
        blockConstraints net k b &&&
        terminationConstraints net k b ys &&&
        blockOrderConstraints net triplets k b &&&
        checkNonNegativityConstraints ys &&&
        checkSizeLimit k b ys sizeLimit

checkTerminalMarkingReachableSat :: PetriNet -> [Triplet] -> Integer -> MinConstraintProblem Integer TerminalMarkingReachableInvariant (Int, [Int])
checkTerminalMarkingReachableSat net triplets k =
        let makeYName i = (++) (genericReplicate i '\'')
            ys = [makeVarMapWith (makeYName i) $ places net | i <- [1..k]]
            b = makeVarMap $ transitions net
        in  (minimizeMethod, \sizeLimit ->
            ("terminal marking reachable", "invariant",
             concat (map getNames ys) ++ getNames b,
             \fm -> checkTerminalMarkingReachable net triplets k (fmap fm b) (map (fmap fm) ys) sizeLimit,
             \fm -> invariantFromAssignment net k (fmap fm b) (map (fmap fm) ys)))

minimizeMethod :: Int -> (Int, [Int]) -> String
minimizeMethod 1 (curYSize, _) = "number of places in y less than " ++ show curYSize
minimizeMethod 2 (_, curTSize) = "number of transitions in last block less than " ++ show (last curTSize)
minimizeMethod 3 (curYSize, curTSize) = "number of transitions in last block less than " ++ show (last curTSize) ++
                                        " or same number of transitions and number of places in y less than " ++ show curYSize
minimizeMethod _ _ = error "minimization method not supported"

checkSizeLimit :: Integer -> SIMap Transition -> [SIMap Place] -> Maybe (Int, (Int, [Int])) -> SBool
checkSizeLimit _ _ _ Nothing = true
checkSizeLimit k b ys (Just (1, (curYSize, _))) = (sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .< literal (fromIntegral curYSize))
checkSizeLimit k b ys (Just (2, (_, curTSize))) = (sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .< literal (fromIntegral (last curTSize))
checkSizeLimit k b ys (Just (3, (curYSize, curTSize))) =
        ((sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .< literal (fromIntegral (last curTSize))) ||| (
            ((sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .== literal (fromIntegral (last curTSize))) &&&
            (sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .< literal (fromIntegral curYSize))
        )
checkSizeLimit _ _ _ (Just (_, _)) = error "minimization method not supported"

invariantFromAssignment :: PetriNet -> Integer -> IMap Transition -> [IMap Place] -> (TerminalMarkingReachableInvariant, (Int, [Int]))
invariantFromAssignment net k b ys =
        let invariant = [BlockInvariant (i, M.keys (M.filter (== i) b), makeVector y) | (i,y) <- zip [1..] ys]
        in  (invariant, (sum $ map invariantSize invariant, map (\(BlockInvariant (_, ts, _)) -> length ts) invariant))
