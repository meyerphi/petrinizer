{-# LANGUAGE FlexibleContexts #-}

module Solver.SafetyInvariant (
    checkSafetyInvariantSat
  , SafetyInvariant
  , trapToSafetyInvariant
) where

import Data.SBV
import Data.List (intercalate)
import qualified Data.Map as M
import Control.Arrow (second)

import Util
import Solver
import Property
import PetriNet

type SimpleTerm = (IVector Place, Integer)
type NamedTerm = (String, SimpleTerm)

data SafetyInvariant =
            SafetyPlaceInvariant SimpleTerm
          | SafetyTrapInvariant Trap

instance Show SafetyInvariant where
        show (SafetyPlaceInvariant (ps, c)) =
                    intercalate " + " (map showWeighted (items ps)) ++
                    " ≤ " ++ show c
        show (SafetyTrapInvariant ps) =
                    intercalate " + " (map show ps) ++
                    " ≥ 1"

instance Invariant SafetyInvariant where
        invariantSize (SafetyPlaceInvariant (ps, _)) = size ps
        invariantSize (SafetyTrapInvariant ps) = length ps

formulaToSimpleTerms :: Formula Place -> [SimpleTerm]
formulaToSimpleTerms = transformF
        where
            transformF FTrue = []
            transformF (p :&: q) = transformF p ++ transformF q
            transformF (LinearInequation ps Gt (Const 0)) =
                transformT 1 ps 1
            transformF (LinearInequation ps Ge (Const 1)) =
                transformT 1 ps 1
            transformF (LinearInequation ps Eq (Const 0)) =
                transformT (-1) ps 0
            transformF (LinearInequation ps Le (Const 0)) =
                transformT (-1) ps 0
            transformF (LinearInequation ps Lt (Const 1)) =
                transformT (-1) ps 0
            transformF f =
                error $ "formula not supported for invariant: " ++ show f
            transformT fac ps w = [(buildVector (transformTerm fac ps), w)]
            transformTerm fac (t :+: u) =
                transformTerm fac t ++ transformTerm fac u
            transformTerm fac (t :-: u) =
                transformTerm fac t ++ transformTerm (- fac) u
            transformTerm fac (Const c :*: t) = transformTerm (fac * c) t
            transformTerm fac (t :*: Const c) = transformTerm (fac * c) t
            transformTerm fac (Var x) = [(x, fac)]
            transformTerm _ t =
                error $ "term not supported for invariant: " ++ show t

trapToSimpleTerm :: Trap -> SimpleTerm
trapToSimpleTerm traps = (buildVector (map (\p -> (p, 1)) traps), 1)

checkInductivityConstraint :: PetriNet -> SIMap Place -> SBool
checkInductivityConstraint net lambda =
            sAnd $ map checkInductivity $ transitions net
        where checkInductivity t =
                let incoming = map addPlace $ lpre net t
                    outgoing = map addPlace $ lpost net t
                in  sum outgoing - sum incoming .<= 0
              addPlace (p,w) = literal w * val lambda p

checkSafetyConstraint :: PetriNet -> [NamedTerm] -> SIMap Place ->
        SIMap String -> SBool
checkSafetyConstraint net terms lambda y =
            sum (map addPlace (linitials net)) .< sum (map addTerm terms)
        where addPlace (p,w) = literal w * val lambda p
              addTerm (n,(_,c)) = literal c * val y n

checkPropertyConstraint :: PetriNet -> [NamedTerm] -> SIMap Place ->
        SIMap String -> SBool
checkPropertyConstraint net terms lambda y =
            sAnd $ map checkPlace $ places net
        where checkPlace p =
                  val lambda p .>= sum (map (addTerm p) terms)
              addTerm p (n,(ps,_)) = val y n * literal (val ps p)

checkNonNegativityConstraint :: [NamedTerm] -> SIMap String -> SBool
checkNonNegativityConstraint terms y =
            sAnd $ map checkVal terms
        where checkVal (n,_) = val y n .>= 0

checkSafetyInvariant :: PetriNet -> [NamedTerm] -> SIMap Place ->
        SIMap String -> SBool
checkSafetyInvariant net terms lambda y =
        checkInductivityConstraint net lambda  .&&
        checkSafetyConstraint net terms lambda y .&&
        checkPropertyConstraint net terms lambda y .&&
        checkNonNegativityConstraint terms y

-- TODO: split up into many smaller sat problems
checkSafetyInvariantSat :: PetriNet -> Formula Place -> [Trap] ->
        ConstraintProblem Integer SafetyInvariant
checkSafetyInvariantSat net f traps =
        let formTerms = formulaToSimpleTerms f
            namedTraps = numPref "@trap" `zip` traps
            namedTrapTerms = map (second trapToSimpleTerm) namedTraps
            namedFormTerms = numPref "@term" `zip` formTerms
            namedTerms = namedFormTerms ++ namedTrapTerms
            lambda = makeVarMap $ places net
            names = map fst namedTerms
            myVarMap fvm = M.fromList $ names `zip` fmap fvm names
        in  ("safety invariant constraints", "safety invariant",
             getNames lambda ++ names,
             \fm -> checkSafetyInvariant net namedTerms
                (fmap fm lambda) (myVarMap fm),
             \fm -> getSafetyInvariant net (fmap fm lambda))

trapToSafetyInvariant :: Trap -> SafetyInvariant
trapToSafetyInvariant = SafetyTrapInvariant

getSafetyInvariant :: PetriNet -> IMap Place ->
        SafetyInvariant
getSafetyInvariant net lambda =
        SafetyPlaceInvariant
            (buildVector (items lambda),
             sum (map (\(p,i) -> val lambda p * i) (linitials net)))
