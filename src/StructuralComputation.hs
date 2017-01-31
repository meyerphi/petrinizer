module StructuralComputation
    (Triplet
    ,generateTriplets
    ,trivialTriplet
    ,emptyTriplet)
where

import PetriNet
import qualified Data.Map as M

type Triplet = (Transition, Transition, [Transition])

-- TODO: optimize
generateTriplets :: PetriNet -> [Triplet]
generateTriplets net =
        let
            prePostMultiset t =
                let
                    (pre, post) = context net t
                in
                    (M.fromList pre, M.fromList post)
            prePostMultisets = M.fromList $ [(t, prePostMultiset t) | t <- transitions net]
            multiSetDifference a b = if a > b then Just (a - b) else Nothing
            findT' s t =
                let
                    (sPre, sPost) = prePostMultisets M.! s
                    (tPre, tPost) = prePostMultisets M.! t
                    stSet = M.unionWith (+) sPre (M.differenceWith multiSetDifference tPre sPost)
                in
                    [t' | t' <- transitions net, t' /= s, checkTriple stSet t']
            checkTriple stMultiset t' =
                let
                    (tPre, _) = prePostMultisets M.! t'
                    differenceMultiset = M.differenceWith multiSetDifference tPre stMultiset
                in
                    M.null differenceMultiset
        in
            [(s, t, findT' s t) | s <- transitions net, t <- transitions net, s /= t]

trivialTriplet :: Triplet -> Bool
trivialTriplet (_, t, ts) = elem t ts

emptyTriplet :: Triplet -> Bool
emptyTriplet (_, _, ts) = null ts
