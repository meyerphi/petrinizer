{-# LANGUAGE FlexibleContexts #-}

module Solver.TransitionInvariant
    (checkTransitionInvariantSat
    ,checkTransitionInvariantWithSimpleCutSat
    ,tInvariantConstraints
    ,finalInvariantConstraints
    ,nonnegativityConstraints
    ,transitionVectorConstraints
    ,formulaAndRefinementConstraints
    ,checkSimpleCut)
where

import Data.SBV
import qualified Data.Set as S

import Util
import PetriNet
import Property
import Solver
import Solver.Formula

tInvariantConstraints :: PetriNet -> SIMap Transition -> SBool
tInvariantConstraints net x =
            sAnd $ map checkTransitionEquation $ places net
        where checkTransitionEquation p =
                  let incoming = map addTransition $ lpre net p
                      outgoing = map addTransition $ lpost net p
                  in  sum incoming - sum outgoing .>= 0
              addTransition (t,w) = literal w * val x t

finalInvariantConstraints :: SIMap Transition -> SBool
finalInvariantConstraints x = sum (vals x) .> 0

nonnegativityConstraints :: SIMap Transition -> SBool
nonnegativityConstraints x = sAnd $ map (.>= 0) (vals x)

transitionVectorConstraints :: PetriNet -> SIMap Transition -> SBool
transitionVectorConstraints net x =
        nonnegativityConstraints x .&&
        finalInvariantConstraints x .&&
        tInvariantConstraints net x

formulaAndRefinementConstraints :: Formula Transition -> [Cut] -> SIMap Transition -> SBool
formulaAndRefinementConstraints f cuts x =
        checkCuts cuts x .&&
        evaluateFormula f x

checkSimpleCut :: SimpleCut -> SIMap Transition -> SBool
checkSimpleCut (t0, cs) x =
            checkNegative (S.toList t0) .&& sAnd (map (checkPositive . S.toList) cs)
        where checkNegative ts = sum (mval x ts) .== 0
              checkPositive ts = sum (mval x ts) .> 0

checkCuts :: [Cut] -> SIMap Transition -> SBool
checkCuts cuts x = sAnd $ map checkCut cuts
        where checkCut (ts, u) =
                  let cPre = map (sOr . map (positiveVal x) . snd) ts
                      cPost = map (positiveVal x) u
                  in  sAnd cPre .=> sOr cPost

checkTransitionInvariant :: PetriNet -> Formula Transition ->
        [Cut] -> SIMap Transition -> SBool
checkTransitionInvariant net f cuts x =
        transitionVectorConstraints net x .&&
        formulaAndRefinementConstraints f cuts x

checkTransitionInvariantSat :: PetriNet -> Formula Transition -> [Cut] ->
        ConstraintProblem Integer FiringVector
checkTransitionInvariantSat net f cuts =
        let x = makeVarMap $ transitions net
        in  ("transition invariant constraints", "transition invariant",
            getNames x,
            \fm -> checkTransitionInvariant net f cuts (fmap fm x),
            \fm -> firingVectorFromAssignment (fmap fm x))

checkTransitionInvariantWithSimpleCut :: PetriNet -> Formula Transition ->
        SimpleCut -> SIMap Transition -> SBool
checkTransitionInvariantWithSimpleCut net f cut x =
        transitionVectorConstraints net x .&&
        evaluateFormula f x .&&
        checkSimpleCut cut x

checkTransitionInvariantWithSimpleCutSat :: PetriNet -> Formula Transition -> SimpleCut ->
        ConstraintProblem Integer FiringVector
checkTransitionInvariantWithSimpleCutSat net f cut =
        let x = makeVarMap $ transitions net
        in  ("transition invariant constraints with simple cut", "transition invariant",
            getNames x,
            \fm -> checkTransitionInvariantWithSimpleCut net f cut (fmap fm x),
            \fm -> firingVectorFromAssignment (fmap fm x))

firingVectorFromAssignment :: IMap Transition -> FiringVector
firingVectorFromAssignment = makeVector

