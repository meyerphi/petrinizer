{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module PetriNet
    (PetriNet,Place(..),Transition(..),Marking,FiringVector,
     renamePlace,renameTransition,renamePetriNetPlacesAndTransitions,
     name,showNetName,places,transitions,
     initialMarking,initial,initials,linitials,
     pre,lpre,post,lpost,mpre,mpost,context,ghostTransitions,
     makePetriNet,makePetriNetWithTrans,
     makePetriNetFromStrings,makePetriNetWithTransFromStrings,Trap,Siphon,Cut,
     constructCut,SimpleCut,Invariant(..))
where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow (first,(***))
import Data.List (sort,(\\))

import Util

newtype Place = Place String deriving (Ord,Eq)
newtype Transition = Transition String deriving (Ord,Eq)

instance Show Place where
        show (Place p) = p
instance Show Transition where
        show (Transition t) = t

type SimpleCut = (S.Set Transition, [S.Set Transition])

type ContextMap a b = M.Map a ([(b, Integer)],[(b, Integer)])

class (Ord a, Ord b) => Nodes a b | a -> b where
        lpre :: PetriNet -> a -> [(b, Integer)]
        lpre net = fst . context net
        lpost :: PetriNet -> a -> [(b, Integer)]
        lpost net = snd . context net
        pre :: PetriNet -> a -> [b]
        pre net = map fst . lpre net
        post :: PetriNet -> a -> [b]
        post net = map fst . lpost net
        lmpre :: PetriNet -> [a] -> [(b, Integer)]
        lmpre net = listMap . concatMap (lpre net)
        lmpost :: PetriNet -> [a] -> [(b, Integer)]
        lmpost net = listMap . concatMap (lpost net)
        mpre :: PetriNet -> [a] -> [b]
        mpre net = map fst . lmpre net
        mpost :: PetriNet -> [a] -> [b]
        mpost net = map fst . lmpost net
        context :: PetriNet -> a -> ([(b, Integer)], [(b, Integer)])
        context net x = M.findWithDefault ([],[]) x (contextMap net)
        contextMap :: PetriNet -> ContextMap a b

instance Nodes Place Transition where
        contextMap = adjacencyP
instance Nodes Transition Place where
        contextMap = adjacencyT

type Marking = Vector Place
type FiringVector = Vector Transition

type Trap = [Place]
type Siphon = [Place]
-- TODO: generalize cut type
type Cut = ([([Place], [Transition])], [Transition])

class Invariant a where
        invariantSize :: a -> Int

data PetriNet = PetriNet {
        name :: String,
        places :: [Place],
        transitions :: [Transition],
        adjacencyP :: M.Map Place ([(Transition,Integer)], [(Transition,Integer)]),
        adjacencyT :: M.Map Transition ([(Place,Integer)], [(Place,Integer)]),
        initialMarking :: Marking,
        ghostTransitions :: [Transition]
}

initial :: PetriNet -> Place -> Integer
initial net = val (initialMarking net)

initials :: PetriNet -> [Place]
initials = elems . initialMarking

linitials :: PetriNet -> [(Place,Integer)]
linitials = items . initialMarking

showNetName :: PetriNet -> String
showNetName net = "Petri net" ++
               (if null (name net) then "" else " " ++ show (name net))

instance Show PetriNet where
        show net = showNetName net ++
                   "\nPlaces: " ++ show (places net) ++
                   "\nTransitions: " ++ show (transitions net) ++
                   "\nPlace arcs:\n" ++ unlines
                        (map showContext (M.toList (adjacencyP net))) ++
                   "\nTransition arcs:\n" ++ unlines
                        (map showContext (M.toList (adjacencyT net))) ++
                   "\nInitial: " ++ show (initialMarking net) ++
                   "\nGhost transitions: " ++ show (ghostTransitions net)
                where showContext (s,(l,r)) =
                          show l ++ " -> " ++ show s ++ " -> " ++ show r

-- TODO: better cuts, scc, min cut?

constructCut :: PetriNet -> FiringVector -> [Trap] -> Cut
constructCut net _ traps = (trapComponents, trapOutputs)
        where trapComponent trap = (sort trap, sort (mpre net trap) \\ trapOutputs) :: ([Place], [Transition])
              trapComponents = listSet $ map trapComponent traps
              trapOutput trap = mpost net trap \\ mpre net trap
              trapOutputs = listSet $ concatMap trapOutput traps
{-
constructCut :: PetriNet -> FiringVector -> [Trap] -> Cut
constructCut net x _ = (map (\t -> ([],[t])) tPositive, tNegative)
        where tPositive = elems x
              tNegative = transitions net \\ tPositive
-}

renamePlace :: (String -> String) -> Place -> Place
renamePlace f (Place p) = Place (f p)

renameTransition :: (String -> String) -> Transition -> Transition
renameTransition f (Transition t) = Transition (f t)

renamePetriNetPlacesAndTransitions :: (String -> String) -> PetriNet -> PetriNet
renamePetriNetPlacesAndTransitions f net =
            PetriNet {
                name = name net,
                places      =
                    listSet $ map (renamePlace f) $ places net,
                transitions =
                    listSet $ map (renameTransition f) $ transitions net,
                adjacencyP  = mapAdjacency (renamePlace f) (renameTransition f) $
                    adjacencyP net,
                adjacencyT  = mapAdjacency (renameTransition f) (renamePlace f) $
                    adjacencyT net,
                initialMarking = emap (renamePlace f) $ initialMarking net,
                ghostTransitions =
                    listSet $ map (renameTransition f) $ ghostTransitions net
            }
        where mapAdjacency f g m = M.mapKeys f (M.map (mapContext g) m)
              mapContext f (pre, post) =
                  (listMap (map (first f) pre), listMap (map (first f) post))

makePetriNet :: String -> [Place] -> [Transition] ->
        [Either (Transition, Place, Integer) (Place, Transition, Integer)] ->
        [(Place, Integer)] -> [Transition] -> PetriNet
makePetriNet name places transitions arcs initial gs =
            PetriNet {
                name = name,
                places = listSet places,
                transitions = listSet transitions,
                adjacencyP = M.map (listMap *** listMap) adP,
                adjacencyT = M.map (listMap *** listMap)adT,
                initialMarking = buildVector initial,
                ghostTransitions = listSet gs
            }
        where
            (adP, adT) = foldl buildMaps (M.empty, M.empty) arcs
            buildMaps (mp,mt) (Left (_,_,0)) = (mp,mt)
            buildMaps (mp,mt) (Right (_,_,0)) = (mp,mt)
            buildMaps (mp,mt) (Right (p,t,w)) =
                       let mp' = M.insertWith addArc
                                    p ([],[(t,w)]) mp
                           mt' = M.insertWith addArc
                                    t ([(p,w)],[]) mt
                       in  (mp',mt')
            buildMaps (mp,mt) (Left (t,p,w)) =
                       let mt' = M.insertWith addArc
                                    t ([],[(p,w)]) mt
                           mp' = M.insertWith addArc
                                    p ([(t,w)],[]) mp
                       in  (mp',mt')
            addArc (lNew,rNew) (lOld,rOld) = (lNew ++ lOld,rNew ++ rOld)

makePetriNetFromStrings :: String -> [String] -> [String] ->
        [(String, String, Integer)] ->
        [(String, Integer)] -> [String] -> PetriNet
makePetriNetFromStrings name places transitions arcs initial gs =
            makePetriNet
                name
                (map Place (S.toAscList placeSet))
                (map Transition (S.toAscList transitionSet))
                (map toEitherArc arcs)
                (map (first Place) initial)
                (map Transition gs)
        where
            placeSet = S.fromList places
            transitionSet = S.fromList transitions
            toEitherArc (l,r,w) =
                let lp = l `S.member` placeSet
                    lt = l `S.member` transitionSet
                    rp = r `S.member` placeSet
                    rt = r `S.member` transitionSet
                in  case (lp,lt,rp,rt) of
                        (True,False,False,True) ->
                            Right (Place l, Transition r, w)
                        (False,True,True,False) ->
                            Left (Transition l, Place r, w)
                        (False,False,_,_) ->
                            error $ l ++ " not a declared place or transition "
                        (_,_,False,False) ->
                            error $ r ++ " not a declared place or transition "
                        (True,_,True,_) ->
                            error $ l ++ " and " ++ r ++ " both places"
                        (_,True,_,True) ->
                            error $ l ++ " and " ++ r ++ " both transitions"

makePetriNetWithTrans :: String -> [Place] ->
        [(Transition, ([(Place, Integer)], [(Place, Integer)]))] ->
        [(Place, Integer)] -> [Transition] -> PetriNet
makePetriNetWithTrans name places ts =
            makePetriNet name places (map fst ts) arcs
        where
            arcs = [ Right (p,t,w) | (t,(is,_)) <- ts, (p,w) <- is ] ++
                   [ Left  (t,p,w) | (t,(_,os)) <- ts, (p,w) <- os ]

makePetriNetWithTransFromStrings :: String -> [String] ->
        [(String, ([(String, Integer)], [(String, Integer)]))] ->
        [(String, Integer)] -> [String] -> PetriNet
makePetriNetWithTransFromStrings name places arcs initial gs =
            makePetriNetWithTrans
                name
                (map Place places)
                (map toTArc arcs)
                (map (first Place) initial)
                (map Transition gs)
        where
            toTArc (t, (is, os)) =
                (Transition t, (map (first Place) is, map (first Place) os))
