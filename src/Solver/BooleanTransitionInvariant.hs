{-# LANGUAGE FlexibleContexts #-}

module Solver.BooleanTransitionInvariant
    (checkBooleanTransitionInvariantSat
    ,checkBooleanTransitionInvariantWithSimpleCutSat)
where

import Data.SBV
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Util
import PetriNet
import Property
import Solver
import Solver.Simplifier

tInvariantConstraints :: PetriNet -> SBMap Transition -> SBool
tInvariantConstraints net x =
            sAnd $ map checkTransitionEquation $ places net
        where checkTransitionEquation p =
                  let incoming = map (val x) $ pre net p \\ post net p
                      outgoing = map (val x) $ post net p \\ pre net p
                  in  sOr outgoing .=> sOr incoming

finalInvariantConstraints :: SBMap Transition -> SBool
finalInvariantConstraints x = sOr $ vals x

transitionVectorConstraints :: PetriNet -> SBMap Transition -> SBool
transitionVectorConstraints net x =
        finalInvariantConstraints x .&&
        tInvariantConstraints net x

formulaAndRefinementConstraints :: SimpleCut -> [Cut] -> SBMap Transition -> SBool
formulaAndRefinementConstraints fcut cuts x =
        checkCuts cuts x .&&
        checkSimpleCut fcut x

checkSimpleCut :: SimpleCut -> SBMap Transition -> SBool
checkSimpleCut (t0, cs) x =
            checkNegative (S.toList t0) .&& sAnd (map (checkPositive . S.toList) cs)
        where checkNegative ts = sAnd (map (sNot . val x) ts)
              checkPositive ts = sOr (map (val x) ts)

checkCuts :: [Cut] -> SBMap Transition -> SBool
checkCuts cuts x = sAnd $ map checkCut cuts
        where checkCut (ts, u) =
                  let cPre = map (sOr . map (val x) . snd) ts
                      cPost = map (val x) u
                  in  sAnd cPre .=> sOr cPost

checkBooleanTransitionInvariant :: PetriNet -> SimpleCut ->
        [Cut] -> SBMap Transition -> SBool
checkBooleanTransitionInvariant net fcut cuts x =
        transitionVectorConstraints net x .&&
        formulaAndRefinementConstraints fcut cuts x

checkBooleanTransitionInvariantSat :: PetriNet -> Formula Transition -> [Cut] ->
        ConstraintProblem Bool FiringVector
checkBooleanTransitionInvariantSat net f cuts =
        let x = makeVarMap $ transitions net
            fcut = formulaToCut f
        in  ("transition invariant constraints", "transition invariant",
            getNames x,
            \fm -> checkBooleanTransitionInvariant net fcut cuts (fmap fm x),
            \fm -> firingVectorFromAssignment (fmap fm x))

checkBooleanTransitionInvariantWithSimpleCut :: PetriNet -> SimpleCut ->
        SimpleCut -> SBMap Transition -> SBool
checkBooleanTransitionInvariantWithSimpleCut net fcut cut x =
        transitionVectorConstraints net x .&&
        checkSimpleCut fcut x .&&
        checkSimpleCut cut x

checkBooleanTransitionInvariantWithSimpleCutSat :: PetriNet -> Formula Transition -> SimpleCut ->
        ConstraintProblem Bool FiringVector
checkBooleanTransitionInvariantWithSimpleCutSat net f cut =
        let x = makeVarMap $ transitions net
            fcut = formulaToCut f
        in  ("transition invariant constraints with simple cut", "transition invariant",
            getNames x,
            \fm -> checkBooleanTransitionInvariantWithSimpleCut net fcut cut (fmap fm x),
            \fm -> firingVectorFromAssignment (fmap fm x))

firingVectorFromAssignment :: BMap Transition -> FiringVector
firingVectorFromAssignment x = makeVector $ M.map (const 1) $ M.filter id x

