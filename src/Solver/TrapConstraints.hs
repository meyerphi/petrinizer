{-# LANGUAGE FlexibleContexts #-}

module Solver.TrapConstraints
    (checkTrapSat)
where

import Data.SBV
import qualified Data.Map as M

import Util
import PetriNet
import Solver

trapConstraints :: PetriNet -> SBMap Place -> SBool
trapConstraints net b =
            sAnd $ map trapConstraint $ transitions net
        where trapConstraint t =
                  sOr (mval b (pre net t)) .=> sOr (mval b (post net t))

trapInitiallyMarked :: PetriNet -> SBMap Place -> SBool
trapInitiallyMarked net b = sOr $ mval b $ initials net

trapUnassigned :: Marking -> SBMap Place -> SBool
trapUnassigned m b = sAnd $ map (sNot . val b) $ elems m

checkTrap :: PetriNet -> Marking -> SBMap Place -> SBool
checkTrap net m b =
        trapConstraints net b .&&
        trapInitiallyMarked net b .&&
        trapUnassigned m b

checkTrapSat :: PetriNet -> Marking -> ConstraintProblem Bool Trap
checkTrapSat net m =
        let b = makeVarMap $ places net
        in  ("trap constraints", "trap",
             getNames b,
             \fm -> checkTrap net m (fmap fm b),
             \fm -> trapFromAssignment (fmap fm b))

trapFromAssignment :: BMap Place -> Trap
trapFromAssignment b = M.keys $ M.filter id b

