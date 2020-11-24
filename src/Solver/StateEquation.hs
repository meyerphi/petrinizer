module Solver.StateEquation
    (checkStateEquationSat)
where

import Data.SBV

import Util
import PetriNet
import Property
import Solver
import Solver.Formula

placeConstraints :: PetriNet -> SIMap Place -> SIMap Transition -> SBool
placeConstraints net m x =
            sAnd $ map checkPlaceEquation $ places net
        where checkPlaceEquation p =
                let incoming = map addTransition $ lpre net p
                    outgoing = map addTransition $ lpost net p
                    pinit = literal $ initial net p
                in  pinit + sum incoming - sum outgoing .== val m p
              addTransition (t,w) = literal w * val x t

nonNegativityConstraints :: PetriNet -> SIMap Place -> SIMap Transition -> SBool
nonNegativityConstraints net m x =
            let mnn = map (checkVal m) $ places net
                xnn = map (checkVal x) $ transitions net
            in  sAnd mnn .&& sAnd xnn
        where checkVal mapping n = val mapping n .>= 0

checkTraps :: [Trap] -> SIMap Place -> SBool
checkTraps traps m =
            sAnd $ map checkTrapDelta traps
        where checkTrapDelta trap = sum (map (val m) trap) .>= 1

checkStateEquation :: PetriNet -> Formula Place ->
        SIMap Place -> SIMap Transition -> [Trap] -> SBool
checkStateEquation net f m x traps =
        placeConstraints net m x .&&
        nonNegativityConstraints net m x .&&
        checkTraps traps m .&&
        evaluateFormula f m

checkStateEquationSat :: PetriNet -> Formula Place -> [Trap] ->
        ConstraintProblem Integer Marking
checkStateEquationSat net f traps =
        let m = makeVarMap $ places net
            x = makeVarMap $ transitions net
        in  ("state equation", "marking",
             getNames m ++ getNames x,
             \fm -> checkStateEquation net f (fmap fm m) (fmap fm x) traps,
             \fm -> markingFromAssignment (fmap fm m))

markingFromAssignment :: IMap Place -> Marking
markingFromAssignment = makeVector

