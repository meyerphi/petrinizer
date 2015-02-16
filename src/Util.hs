{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies #-}

module Util
    (elems,items,size,emap,prime,numPref,
     listSet,listMap,val,vals,mval,zeroVal,positiveVal,sumVal,
     makeVarMap,makeVarMapWith,buildVector,makeVector,getNames,
     Vector,Model,VarMap,SIMap,SBMap,IMap,BMap,showWeighted,
     OptIO,verbosePut,opt,putLine,parallelIO)
where

import Data.SBV
import qualified Data.Map as M
import Data.List
import Data.Ord
import Data.Function
import Control.Concurrent.ParallelIO
import Control.Monad
import Control.Monad.Reader
import System.IO

import Options

{-
- Various maps and functions on them
-}

newtype Vector a = Vector { getVector :: M.Map a Integer }
type Model a = M.Map String a
type VarMap a = M.Map a String
type SIMap a = M.Map a SInteger
type SBMap a = M.Map a SBool
type IMap a = M.Map a Integer
type BMap a = M.Map a Bool

class MapLike c a b | c -> a, c -> b where
        val :: c -> a -> b
        vals :: c -> [b]
        elems :: c -> [a]
        items :: c -> [(a,b)]
        size :: c -> Int

        mval :: c -> [a] -> [b]
        mval = map . val
        sumVal :: (Num b) => c -> b
        sumVal = sum . vals

instance (Ord a, Show a, Show b) => MapLike (M.Map a b) a b where
        val m x = M.findWithDefault
                    (error ("key " ++ show x ++ " not found in " ++ show m))
                    x m
        vals = M.elems
        items = M.toList
        elems = M.keys
        size = M.size

instance (Ord a, Show a) => MapLike (Vector a) a Integer where
        val (Vector v) x = M.findWithDefault 0 x v
        vals = vals . getVector
        items = M.toList . getVector
        elems = M.keys . getVector
        size = M.size . getVector

instance (Show a) => Show (Vector a) where
        show (Vector v) =
                "[" ++ intercalate "," (map showEntry (M.toList v)) ++ "]"
            where showEntry (i,x) =
                    show i ++ (if x /= 1 then "(" ++ show x ++ ")" else "")

emap :: (Ord a, Ord b) => (a -> b) -> Vector a -> Vector b
emap f = Vector . M.mapKeys f . getVector

zeroVal :: (Ord a, Show a) => M.Map a SInteger -> a -> SBool
zeroVal m x = val m x .== 0

positiveVal :: (Ord a, Show a) => M.Map a SInteger -> a -> SBool
positiveVal m x = val m x .> 0

makeVarMap :: (Show a, Ord a) => [a] -> VarMap a
makeVarMap = makeVarMapWith id

makeVarMapWith :: (Show a, Ord a) => (String -> String) -> [a] -> VarMap a
makeVarMapWith f xs = M.fromList $ xs `zip` map (f . show) xs

getNames :: VarMap a -> [String]
getNames = M.elems

buildVector :: (Ord a) => [(a, Integer)] -> Vector a
buildVector = makeVector . M.fromList

makeVector :: (Ord a) => M.Map a Integer -> Vector a
makeVector = Vector . M.filter (/=0)

{-
- List functions
-}

listSet :: (Ord a) => [a] -> [a]
listSet = map head . group . sort

listMap :: (Ord a, Num b) => [(a,b)] -> [(a,b)]
listMap = map (foldl1 (\(x1,y1) (_,y2) -> (x1,y1 + y2))) .
        groupBy ((==) `on` fst) .  sortBy (comparing fst)

{-
- IO functions
-}

type OptIO a = ReaderT Options IO a

opt :: (Options -> a) -> OptIO a
opt getOpt = liftM getOpt ask

verbosePut ::  Int -> String -> OptIO ()
verbosePut level str = do
        verbosity <- opt optVerbosity
        when (verbosity >= level) (putLine str)
        liftIO $ hFlush stdout -- TODO: remove again

putLine :: String -> OptIO ()
putLine = liftIO . putStrLn

parallelIO :: [OptIO a] -> OptIO [a]
parallelIO tasks = do
        opts <- ask
        liftIO $ parallel $ map (`runReaderT` opts) tasks

{-
- String functions
-}

prime :: String -> String
prime = ('\'':)

numPref :: String -> [String]
numPref s = map (\i -> s ++ show i) [(1::Integer)..]

showWeighted :: (Show a, Num b, Eq b, Show b) => (a, b) -> String
showWeighted (x, w) = (if w == 1 then "" else show w) ++ show x

