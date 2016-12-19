module Solver.UniqueTerminalMarking
    (checkUniqueTerminalMarkingSat)
where

import Data.SBV

import Util
import PetriNet
import Property
import Solver

stateEquationConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Transition -> SBool
stateEquationConstraints net m1 m2 x =
            bAnd $ map checkStateEquation $ places net
        where checkStateEquation p =
                let incoming = map addTransition $ lpre net p
                    outgoing = map addTransition $ lpost net p
                in  val m1 p + sum incoming - sum outgoing .== val m2 p
              addTransition (t,w) = literal w * val x t

nonNegativityConstraints :: PetriNet -> SIMap Place -> SBool
nonNegativityConstraints net m =
            bAnd $ map checkVal $ places net
        where checkVal p = val m p .>= 0

terminalConstraints :: PetriNet -> SIMap Place -> SBool
terminalConstraints net m =
            bAnd $ map checkTransition $ transitions net
        where checkTransition :: Transition -> SBool
              checkTransition t = bOr $ map checkPlace $ lpre net t
              checkPlace (p,w) = val m p .< literal w

nonEqualityConstraints :: PetriNet -> SIMap Place -> SIMap Place -> SBool
nonEqualityConstraints net m1 m2 =
            bOr $ map checkNonEquality $ places net
        where checkNonEquality p = val m1 p ./= val m2 p

checkUniqueTerminalMarking :: PetriNet -> SIMap Place -> SIMap Place -> SIMap Transition -> SBool
checkUniqueTerminalMarking net m1 m2 x =
        nonEqualityConstraints net m1 m2 &&&
        stateEquationConstraints net m1 m2 x &&&
        nonNegativityConstraints net m1 &&&
        nonNegativityConstraints net m2 &&&
        terminalConstraints net m1 &&&
        terminalConstraints net m2

checkUniqueTerminalMarkingSat :: PetriNet -> ConstraintProblem Integer (Marking, Marking, FiringVector)
checkUniqueTerminalMarkingSat net =
        let m1 = makeVarMap $ places net
            m2 = makeVarMapWith prime $ places net
            x  = makeVarMap $ transitions net
        in  ("unique terminal marking", "pair of markings and firing vector",
             getNames m1 ++ getNames m2 ++ getNames x,
             \fm -> checkUniqueTerminalMarking net (fmap fm m1) (fmap fm m2) (fmap fm x),
             \fm -> markingsFromAssignment (fmap fm m1) (fmap fm m2) (fmap fm x))

markingsFromAssignment :: IMap Place -> IMap Place -> IMap Transition -> (Marking, Marking, FiringVector)
markingsFromAssignment m1 m2 x = (makeVector m1, makeVector m2, makeVector x)

