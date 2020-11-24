module Solver.Formula
    (evaluateFormula)
where

import Data.SBV

import Util
import Property

evaluateTerm :: (Ord a, Show a) => Term a -> SIMap a -> SInteger
evaluateTerm (Var x) m = val m x
evaluateTerm (Const c) _ = literal c
evaluateTerm (Minus t) m = - evaluateTerm t m
evaluateTerm (t :+: u) m = evaluateTerm t m + evaluateTerm u m
evaluateTerm (t :-: u) m = evaluateTerm t m - evaluateTerm u m
evaluateTerm (t :*: u) m = evaluateTerm t m * evaluateTerm u m

opToFunction :: Op -> SInteger -> SInteger -> SBool
opToFunction Gt = (.>)
opToFunction Ge = (.>=)
opToFunction Eq = (.==)
opToFunction Ne = (./=)
opToFunction Le = (.<=)
opToFunction Lt = (.<)

evaluateFormula :: (Ord a, Show a) => Formula a -> SIMap a -> SBool
evaluateFormula FTrue _ = sTrue
evaluateFormula FFalse _ = sFalse
evaluateFormula (LinearInequation lhs op rhs) m =
        opToFunction op (evaluateTerm lhs m) (evaluateTerm rhs m)
evaluateFormula (Neg p) m = sNot $ evaluateFormula p m
evaluateFormula (p :&: q) m = evaluateFormula p m .&& evaluateFormula q m
evaluateFormula (p :|: q) m = evaluateFormula p m .|| evaluateFormula q m
