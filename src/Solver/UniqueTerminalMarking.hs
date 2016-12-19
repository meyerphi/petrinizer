module Solver.UniqueTerminalMarking
    (checkUniqueTerminalMarkingSat)
where

import Data.SBV

import Util
import PetriNet
import Property
import Solver

placeConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Transition -> SBool
placeConstraints net m1 m2 x =
            bAnd $ map checkPlaceEquation $ places net
        where checkPlaceEquation p =
                let incoming = map addTransition $ lpre net p
                    outgoing = map addTransition $ lpost net p
                in  val m1 p + sum incoming - sum outgoing .== val m2 p
              addTransition (t,w) = literal w * val x t

nonNegativityConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SBool
nonNegativityConstraints net m1 m2 =
            let m1nn = map (checkVal m1) $ places net
                m2nn = map (checkVal m1) $ places net
            in  bAnd m1nn &&& bAnd m2nn
        where checkVal mapping n = val mapping n .>= 0

checkUniqueTerminalMarking :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Transition -> SBool
checkUniqueTerminalMarking net m1 m2 x =
        placeConstraints net m1 m2 x &&&
        nonNegativityConstraints net m1 m2

checkUniqueTerminalMarkingSat :: PetriNet -> ConstraintProblem Integer (Marking, Marking)
checkUniqueTerminalMarkingSat net =
        let m1 = makeVarMap $ places net
            m2 = makeVarMapWith prime $ places net
            x  = makeVarMap $ transitions net
        in  ("unique terminal marking", "pair of markings",
             getNames m1 ++ getNames m2 ++ getNames x,
             \fm -> checkUniqueTerminalMarking net (fmap fm m1) (fmap fm m2) (fmap fm x),
             \fm -> markingsFromAssignment (fmap fm m1) (fmap fm m2))

markingsFromAssignment :: IMap Place -> IMap Place -> (Marking, Marking)
markingsFromAssignment m1 m2 = (makeVector m1, makeVector m2)

