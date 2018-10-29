{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Solver
    (prime,checkSat,checkSatMin,val,vals,positiveVal,zeroVal,
     getNames,ConstraintProblem,MinConstraintProblem)
where

import Data.SBV
import qualified Data.Map as M

import Util
import Options
import Control.Monad.IO.Class
import Control.Applicative

type ConstraintProblem a b =
        (String, String, [String], (String -> SBV a) -> SBool, (String -> a) -> b)
type MinConstraintProblem a b c =
        (Int -> c -> String, Maybe (Int, c) -> ConstraintProblem a (b, c))

rebuildModel :: SymWord a => [String] -> Either String (Bool, [a]) ->
        Maybe (Model a)
rebuildModel _ (Left _) = Nothing
rebuildModel _ (Right (True, _)) = error "Prover returned unknown"
rebuildModel vars (Right (False, m)) = Just $ M.fromList $ vars `zip` m

symConstraints :: SymWord a => [String] -> ((String -> SBV a) -> SBool) ->
        Symbolic SBool
symConstraints vars constraint = do
        syms <- mapM exists vars
        return $ constraint $ val $ M.fromList $ vars `zip` syms

getSolverConfig :: Bool -> Bool -> SMTConfig
getSolverConfig verbose auto =
        let tweaks = if auto then [] else ["(set-option :auto_config false)"]
        in  z3{ verbose=verbose }

checkSat :: (SatModel a, SymWord a, Show a, Show b) =>
        ConstraintProblem a b -> OptIO (Maybe b)
checkSat (problemName, resultName, vars, constraint, interpretation) = do
        verbosePut 2 $ "Checking SAT of " ++ problemName
        verbosity <- opt optVerbosity
        autoConf <- opt optSMTAuto
        result <- liftIO (satWith (getSolverConfig (verbosity >= 4) autoConf)
                    (symConstraints vars constraint))
        case rebuildModel vars (getModelAssignment result) of
            Nothing -> do
                verbosePut 2 "- unsat"
                return Nothing
            Just rawModel -> do
                verbosePut 2 "- sat"
                let model = interpretation $ val rawModel
                verbosePut 3 $ "- " ++ resultName ++ ": " ++ show model
                verbosePut 4 $ "- raw model: " ++ show rawModel
                return $ Just model

checkSatMin :: (SatModel a, SymWord a, Show a, Show b, Show c) =>
        MinConstraintProblem a b c -> OptIO (Maybe b)
checkSatMin (minMethod, minProblem) = do
        optMin <- opt optMinimizeRefinement
        r0 <- checkSat $ minProblem Nothing
        case r0 of
            Nothing -> return Nothing
            Just (result, curSize) ->
                if optMin > 0 then
                    Just <$> findSmaller optMin result curSize
                else
                    return $ Just result
    where findSmaller optMin result curSize = do
            verbosePut 2 $ "Checking for " ++ minMethod optMin curSize
            r1 <- checkSat $ minProblem (Just (optMin, curSize))
            case r1 of
                Nothing -> return result
                Just (result', curSize') -> findSmaller optMin result' curSize'

