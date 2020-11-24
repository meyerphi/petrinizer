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

type InvariantSize = ([Int], [Integer], [Int])

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
            sAnd $ map checkVal $ vals m
        where checkVal x = x .>= 0

checkNonNegativityConstraints :: (Ord a, Show a) => [SIMap a] -> SBool
checkNonNegativityConstraints xs =
            sAnd $ map nonNegativityConstraints xs

blockTerminationConstraints :: PetriNet -> Integer -> SIMap Transition -> SIMap Place -> SBool
blockTerminationConstraints net i b y =
            sAnd $ map checkTransition $ transitions net
        where checkTransition t =
                let incoming = map addPlace $ lpre net t
                    outgoing = map addPlace $ lpost net t
                in  (val b t .== literal i) .=> (sum outgoing - sum incoming .< 0)
              addPlace (p, w) = literal w * val y p

terminationConstraints :: PetriNet -> Integer -> SIMap Transition -> [SIMap Place] -> SBool
terminationConstraints net k b ys =
        sAnd $ [blockTerminationConstraints net i b y | (i,y) <- zip [1..] ys]

blockConstraints :: PetriNet -> Integer -> SIMap Transition -> SBool
blockConstraints net k b =
            sAnd $ map checkBlock $ transitions net
        where checkBlock t = literal 1 .<= val b t .&& val b t .<= literal k

blockOrderConstraints :: PetriNet -> [Triplet] -> Integer -> SIMap Transition -> SBool
blockOrderConstraints net triplets k b =
            sAnd $ map checkTriplet triplets
        where checkTriplet (s,t,ts) = (val b s .> val b t) .=> sOr (map (\t' -> val b t' .== val b t) ts)

checkTerminalMarkingReachable :: PetriNet -> [Triplet] -> Integer -> SIMap Transition -> [SIMap Place] -> Maybe (Int, InvariantSize) -> SBool
checkTerminalMarkingReachable net triplets k b ys sizeLimit =
        blockConstraints net k b .&&
        terminationConstraints net k b ys .&&
        blockOrderConstraints net triplets k b .&&
        checkNonNegativityConstraints ys .&&
        checkSizeLimit k b ys sizeLimit

checkTerminalMarkingReachableSat :: PetriNet -> [Triplet] -> Integer -> MinConstraintProblem Integer TerminalMarkingReachableInvariant InvariantSize
checkTerminalMarkingReachableSat net triplets k =
        let makeYName i = (++) (genericReplicate i '\'')
            ys = [makeVarMapWith (makeYName i) $ places net | i <- [1..k]]
            b = makeVarMap $ transitions net
        in  (minimizeMethod, \sizeLimit ->
            ("terminal marking reachable", "invariant",
             concat (map getNames ys) ++ getNames b,
             \fm -> checkTerminalMarkingReachable net triplets k (fmap fm b) (map (fmap fm) ys) sizeLimit,
             \fm -> invariantFromAssignment net k (fmap fm b) (map (fmap fm) ys)))

minimizeMethod :: Int -> InvariantSize -> String
minimizeMethod 1 (curYSize, _, _) = "number of places in y less than " ++ show (sum curYSize)
minimizeMethod 2 (_, _, curTSize) = "number of transitions in last block less than " ++ show (last curTSize)
minimizeMethod 3 (curYSize, _, curTSize) = "number of transitions in last block less than " ++ show (last curTSize) ++
                                        " or same number of transitions and number of places in y less than " ++ show curYSize
minimizeMethod 4 (_, curYMax, _) = "maximum coefficient in y is less than " ++ show (maximum curYMax)
minimizeMethod 5 (curYSize, curYMax, _) = "number of places in y less than " ++ show (sum curYSize) ++
                                        " or same number of places and maximum coefficient in y is less than " ++ show (maximum curYMax)
minimizeMethod 6 (curYSize, curYMax, curTSize) = "number of transitions in last block less than " ++ show (last curTSize) ++
                                        " or same number of transitions and number of places in y less than " ++ show (sum curYSize) ++
                                        " or same number of transitions and same number of places and maximum coefficient in y less than " ++ show (maximum curYMax)
minimizeMethod _ _ = error "minimization method not supported"

checkSizeLimit :: Integer -> SIMap Transition -> [SIMap Place] -> Maybe (Int, InvariantSize) -> SBool
checkSizeLimit _ _ _ Nothing = sTrue
checkSizeLimit k b ys (Just (1, (curYSize, _, _))) = (sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .< literal (fromIntegral (sum curYSize)))
checkSizeLimit k b ys (Just (2, (_, _, curTSize))) = (sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .< literal (fromIntegral (last curTSize))
checkSizeLimit k b ys (Just (3, (curYSize, _, curTSize))) =
        ((sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .< literal (fromIntegral (last curTSize))) .|| (
            ((sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .== literal (fromIntegral (last curTSize))) .&&
            (sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .< literal (fromIntegral (sum curYSize)))
        )
checkSizeLimit k b ys (Just (4, (_, curYMax, _))) = ((foldl smax 0 (concatMap vals ys)) .< literal (fromIntegral (maximum curYMax)))
checkSizeLimit k b ys (Just (5, (curYSize, curYMax, _))) =
        (sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .< literal (fromIntegral (sum curYSize))) .|| (
            (sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .== literal (fromIntegral (sum curYSize))) .&&
            ((foldl smax 0 (concatMap vals ys)) .< literal (fromIntegral (maximum curYMax))))
checkSizeLimit k b ys (Just (6, (curYSize, curYMax, curTSize))) =
        ((sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .< literal (fromIntegral (last curTSize))) .|| (
            ((sum (map (\tb -> ite (tb .== (literal k)) (1::SInteger) 0) (vals b))) .== literal (fromIntegral (last curTSize))) .&&
            ((sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .< literal (fromIntegral (sum curYSize))) .|| (
                (sum (map (\y -> sum (map (\yi -> ite (yi .> 0) (1::SInteger) 0) (vals y))) ys) .== literal (fromIntegral (sum curYSize))) .&&
                ((foldl smax 0 (concatMap vals ys)) .< literal (fromIntegral (maximum curYMax))))))
checkSizeLimit _ _ _ (Just (_, _)) = error "minimization method not supported"

invariantFromAssignment :: PetriNet -> Integer -> IMap Transition -> [IMap Place] -> (TerminalMarkingReachableInvariant, InvariantSize)
invariantFromAssignment net k b ys =
            (invariant, (map invariantLength invariant, map invariantMaxCoefficient invariant, map blockSize invariant))
        where
            invariant = [BlockInvariant (i, M.keys (M.filter (== i) b), makeVector y) | (i,y) <- zip [1..] ys]
            invariantMaxCoefficient (BlockInvariant (_, _, yi)) = maximum $ vals yi
            invariantLength (BlockInvariant (_, _, yi)) = size yi
            blockSize (BlockInvariant (_, ti, _)) = length ti
