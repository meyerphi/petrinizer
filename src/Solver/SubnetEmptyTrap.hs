{-# LANGUAGE FlexibleContexts #-}

module Solver.SubnetEmptyTrap
    (checkSubnetEmptyTrapSat)
where

import Data.SBV
import qualified Data.Map as M

import Util
import PetriNet
import Solver

subnetTrapConstraints :: PetriNet -> Marking -> FiringVector ->
        SIMap Place -> SBool
subnetTrapConstraints net m x b =
            bAnd $ map trapConstraint $ elems x
        where placeConstraints = (.> 0) . sum . mval b . filter (\p -> val m p == 0)
              trapConstraint t =
                  placeConstraints (pre net t) ==> placeConstraints (post net t)

properTrap :: SIMap Place -> SBool
properTrap b = sum (vals b) .> 0

checkSizeLimit :: SIMap Place -> Maybe (Int, Integer) -> SBool
checkSizeLimit _ Nothing = true
checkSizeLimit b (Just (_, curSize)) = (.< literal curSize) $ sumVal b

minimizeMethod :: Int -> Integer -> String
minimizeMethod _ curSize = "size smaller than " ++ show curSize

checkBinary :: SIMap Place -> SBool
checkBinary = bAnd . map (\x -> x .== 0 ||| x .== 1) . vals

checkSubnetEmptyTrap :: PetriNet -> Marking -> FiringVector ->
        SIMap Place -> Maybe (Int, Integer) -> SBool
checkSubnetEmptyTrap net m x b sizeLimit =
        subnetTrapConstraints net m x b &&&
        checkSizeLimit b sizeLimit &&&
        checkBinary b &&&
        properTrap b

checkSubnetEmptyTrapSat :: PetriNet -> Marking -> FiringVector -> MinConstraintProblem Integer Trap Integer
checkSubnetEmptyTrapSat net m x =
        let b = makeVarMap $ filter (\p -> val m p == 0) $ mpost net $ elems x
        in  (minimizeMethod, \sizeLimit ->
            ("subnet empty trap constraints", "trap",
            getNames b,
            \fm -> checkSubnetEmptyTrap net m x (fmap fm b) sizeLimit,
            \fm -> trapFromAssignment (fmap fm b)))

trapFromAssignment :: IMap Place -> (Trap, Integer)
trapFromAssignment b = (M.keys (M.filter (> 0) b), sum (M.elems b))

