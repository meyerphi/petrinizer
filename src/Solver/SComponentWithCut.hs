{-# LANGUAGE FlexibleContexts #-}

module Solver.SComponentWithCut
    (checkSComponentWithCutSat)
where

import Data.SBV
import Data.List (genericLength)
import qualified Data.Map as M

import Util
import PetriNet
import Solver

type SizeIndicator = (Integer, Integer, Integer, Integer, Integer)

checkPrePostPlaces :: PetriNet -> SIMap Place -> SIMap Place ->
        SIMap Transition -> SIMap Transition -> SIMap Transition ->
        SBool
checkPrePostPlaces net p1 p2 t0 t1 t2 =
            sAnd (map (checkPrePostPlace p1 [t0,t1]) (places net)) .&&
            sAnd (map (checkPrePostPlace p2 [t0,t2]) (places net))
        where checkPrePostPlace ps ts p =
                  let incoming = map (checkIn ts) $ pre net p
                      outgoing = map (checkIn ts) $ post net p
                  in  val ps p .== 1 .=> sAnd incoming .&& sAnd outgoing
              checkIn xs x = sum (map (`val` x) xs) .== 1

checkPrePostTransitions :: PetriNet -> SIMap Place -> SIMap Place ->
        SIMap Transition -> SIMap Transition -> SIMap Transition ->
        SBool
checkPrePostTransitions net p1 p2 t0 t1 t2 =
            sAnd (map (checkPrePostTransition t0 [p1,p2]) (transitions net)) .&&
            sAnd (map (checkPrePostTransition t1 [p1]) (transitions net)) .&&
            sAnd (map (checkPrePostTransition t2 [p2]) (transitions net))
        where checkPrePostTransition ts ps t =
                  let incoming = checkInOne ps $ pre net t
                      outgoing = checkInOne ps $ post net t
                  in  val ts t .== 1 .=> incoming .&& outgoing
              checkInOne xs x = sum (concatMap (`mval` x) xs) .== 1

checkComponents :: FiringVector -> SIMap Transition -> SIMap Transition -> SBool
checkComponents x t1 t2 = checkComponent t1 .&& checkComponent t2
        where checkTransition ts t = val ts t .== 1
              checkComponent ts = sOr $ map (checkTransition ts) $ elems x

checkZeroUnused :: FiringVector -> SIMap Transition -> SBool
checkZeroUnused x t0 = sAnd (map checkTransition (elems x))
        where checkTransition t = val t0 t .== 0

checkTokens :: PetriNet -> SIMap Place -> SIMap Place -> SBool
checkTokens net p1 p2 =
            sum (map addPlace $ linitials net) .== 1
        where addPlace (p,i) = literal i * (val p1 p + val p2 p)

checkDisjunct :: PetriNet ->
        SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> SIMap Transition ->
        SBool
checkDisjunct net p1 p2 t0 t1 t2 =
            sAnd (map checkPlace (places net)) .&&
            sAnd (map checkTransition (transitions net))
        where checkPlace p = val p1 p + val p2 p .<= 1
              checkTransition t = val t0 t + val t1 t + val t2 t .<= 1

checkBinary :: SIMap Place -> SIMap Place -> SIMap Transition ->
        SIMap Transition -> SIMap Transition -> SBool
checkBinary p1 p2 t0 t1 t2 =
            checkBins p1 .&& checkBins p2 .&& checkBins t0 .&& checkBins t1 .&& checkBins t2
        where checkBins xs = sAnd $ map (\x -> x .== 0 .|| x .== 1) $ vals xs

checkSizeLimit ::
        SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> SIMap Transition ->
        Maybe (Int, SizeIndicator) -> SBool
checkSizeLimit _ _ _ _ _ Nothing = sTrue
checkSizeLimit p1 p2 t0 t1 t2 (Just (minMethod, (p1Size, p2Size, t0Size, t1Size, t2Size))) =
        let p1SizeNext = sumVal p1
            p2SizeNext = sumVal p2
            t0SizeNext = sumVal t0
            t1SizeNext = sumVal t1
            t2SizeNext = sumVal t2
            p1SizeNow = literal p1Size
            p2SizeNow = literal p2Size
            t0SizeNow = literal t0Size
            t1SizeNow = literal t1Size
            t2SizeNow = literal t2Size
        in  case minMethod of
                1 -> (t0SizeNext .< t0SizeNow) .||
                    (t0SizeNext .== t0SizeNow .&&
                        t1SizeNext .> t1SizeNow .&& t2SizeNext .>= t2SizeNow) .||
                    (t0SizeNext .== t0SizeNow .&&
                        t1SizeNext .>= t1SizeNow .&& t2SizeNext .> t2SizeNow)
                2 -> (t1SizeNext .> t1SizeNow .&& t2SizeNext .>= t2SizeNow) .||
                    (t1SizeNext .>= t1SizeNow .&& t2SizeNext .> t2SizeNow) .||
                    (t1SizeNext .== t1SizeNow .&& t2SizeNext .== t2SizeNow .&&
                        t0SizeNext .< t0SizeNow)
                3 -> (p1SizeNext + p2SizeNext .< p1SizeNow + p2SizeNow) .||
                    (p1SizeNext + p2SizeNext .== p1SizeNow + p2SizeNow .&&
                        t0SizeNext .< t0SizeNow)
                4 -> (p1SizeNext + p2SizeNext .> p1SizeNow + p2SizeNow) .||
                    (p1SizeNext + p2SizeNext .== p1SizeNow + p2SizeNow .&&
                        t0SizeNext .< t0SizeNow)
                5 -> (p1SizeNext + p2SizeNext .< p1SizeNow + p2SizeNow)
                6 -> (p1SizeNext + p2SizeNext .> p1SizeNow + p2SizeNow)
                7 -> (t1SizeNext .> t1SizeNow .&& t2SizeNext .>= t2SizeNow) .||
                    (t1SizeNext .>= t1SizeNow .&& t2SizeNext .> t2SizeNow)
                8 -> (t1SizeNext .< t1SizeNow .&& t2SizeNext .<= t2SizeNow) .||
                    (t1SizeNext .<= t1SizeNow .&& t2SizeNext .< t2SizeNow)
                9 -> (t1SizeNext + t2SizeNext .> t1SizeNow + t2SizeNow)
                _ -> error $ "minimization method " ++ show minMethod ++ " not supported"

minimizeMethod :: Int -> SizeIndicator -> String
minimizeMethod minMethod (p1Size, p2Size, t0Size, t1Size, t2Size) =
        case minMethod of
                1 -> "(|t0| < " ++ show t0Size ++ ") || " ++
                    "(|t0| = " ++ show t0Size ++ " && " ++ "|t1| > " ++ show t1Size ++ " && |t2| >= " ++ show t2Size ++ ") || " ++
                    "(|t0| = " ++ show t0Size ++ " && " ++ "|t1| >= " ++ show t1Size ++ " && |t2| > " ++ show t2Size ++ ")"
                2 -> "(|t1| > " ++ show t1Size ++ " && " ++ "|t2| >= " ++ show t2Size ++ ") || " ++
                     "(|t1| >= " ++ show t1Size ++ " && " ++ "|t2| > " ++ show t2Size ++ ") || " ++
                     "(|t1| = " ++ show t1Size ++ " && " ++ "|t2| = " ++ show t2Size ++ " && t0 < " ++ show t0Size ++ ")"
                3 -> "(|p1| + |p2| < " ++ show (p1Size + p2Size) ++ ") || " ++
                    "(|p1| + |p2| = " ++ show (p1Size + p2Size) ++ " && " ++ "|t0| < " ++ show t0Size ++ ")"
                4 -> "(|p1| + |p2| > " ++ show (p1Size + p2Size) ++ ") || " ++
                    "(|p1| + |p2| = " ++ show (p1Size + p2Size) ++ " && " ++ "|t0| < " ++ show t0Size ++ ")"
                5 -> "(|p1| + |p2| < " ++ show (p1Size + p2Size) ++ ")"
                6 -> "(|p1| + |p2| > " ++ show (p1Size + p2Size) ++ ")"
                7 -> "(|t1| > " ++ show t1Size ++ " && |t2| >= " ++ show t2Size ++ ") || " ++
                     "(|t1| >= " ++ show t1Size ++ " && |t2| > " ++ show t2Size ++ ")"
                8 -> "(|t1| < " ++ show t1Size ++ " && |t2| <= " ++ show t2Size ++ ") || " ++
                     "(|t1| <= " ++ show t1Size ++ " && |t2| < " ++ show t2Size ++ ")"
                9 -> "(|t1| + |t2| > " ++ show (t1Size + t2Size) ++ ")"
                _ -> error $ "minimization method " ++ show minMethod ++ " not supported"

checkSComponent :: PetriNet -> FiringVector -> Maybe (Int, SizeIndicator) ->
        SIMap Place -> SIMap Place -> SIMap Transition -> SIMap Transition -> SIMap Transition ->
        SBool
checkSComponent net x sizeLimit p1 p2 t0 t1 t2 =
        checkPrePostPlaces net p1 p2 t0 t1 t2 .&&
        checkPrePostTransitions net p1 p2 t0 t1 t2 .&&
        checkZeroUnused x t0 .&&
        checkComponents x t1 t2 .&&
        checkSizeLimit p1 p2 t0 t1 t2 sizeLimit .&&
        checkTokens net p1 p2 .&&
        checkBinary p1 p2 t0 t1 t2 .&&
        checkDisjunct net p1 p2 t0 t1 t2

checkSComponentWithCutSat :: PetriNet -> FiringVector -> MinConstraintProblem Integer Cut SizeIndicator
checkSComponentWithCutSat net x =
        let p1 = makeVarMapWith ("P1@"++) $ places net
            p2 = makeVarMapWith ("P2@"++) $ places net
            t0 = makeVarMapWith ("T0@"++) $ transitions net
            t1 = makeVarMapWith ("T1@"++) $ transitions net
            t2 = makeVarMapWith ("T2@"++) $ transitions net
        in  (minimizeMethod, \sizeLimit ->
            ("general S-component constraints", "cut",
            getNames p1 ++ getNames p2 ++ getNames t0 ++ getNames t1 ++ getNames t2,
            \fm -> checkSComponent net x sizeLimit
                    (fmap fm p1) (fmap fm p2) (fmap fm t0) (fmap fm t1) (fmap fm t2),
            \fm -> cutFromAssignment
                    (fmap fm p1) (fmap fm p2) (fmap fm t0) (fmap fm t1) (fmap fm t2)))

cutFromAssignment ::
        IMap Place -> IMap Place -> IMap Transition -> IMap Transition -> IMap Transition ->
        (Cut, SizeIndicator)
cutFromAssignment p1m p2m t0m t1m t2m =
        let p1 = M.keys $ M.filter (> 0) p1m
            p2 = M.keys $ M.filter (> 0) p2m
            t0 = M.keys $ M.filter (> 0) t0m
            t1 = M.keys $ M.filter (> 0) t1m
            t2 = M.keys $ M.filter (> 0) t2m
        in  (([(p1,t1),(p2,t2)], t0), (genericLength p1, genericLength p2,
                genericLength t0, genericLength t1, genericLength t2))
