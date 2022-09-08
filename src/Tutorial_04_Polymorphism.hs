{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Tutorial_04_Polymorphism () where

import Prelude      hiding (head, abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (head, foldl')
import Data.Maybe   (fromJust)

-- absoluteSum'     :: Vector Int -> Int
-- dotProduct     :: Vector Int -> Vector Int -> Int
-- absoluteSum     :: Vector Int -> Int
-- sparseProduct, sparseProduct'  :: Vector Int -> [(Int, Int)] -> Int

-- {-@ fail eeks @-}
-- {-@ fail head @-}
-- {-@ fail unsafeLookup @-}
-- {-@ fail dotProduct @-}

{-@ type VectorN a N = {v: Vector a | vlen v == N } @-}
{-@ type Btwn Lo Hi = {v: Int | v >= Lo && v < Hi } @-}

-- {-@ twoLangs :: VectorN String 2 @-}
-- twoLangs :: Vector String
-- twoLangs  = fromList ["haskell", "javascript"]
-- eeks      = [ok, yup, nono]
--   where
--     ok    = twoLangs ! 0
--     yup   = twoLangs ! 1
--     nono  = twoLangs ! 3  

{-@ type NEVector a = {v: Vector a | vlen v > 0 } @-}
{-@ head' :: NEVector a -> a @-}
head' :: Vector a -> a
head' vs = vs ! 0

-- {-@ nonEmpty :: v: Vector a -> {r: Bool | r <=> (vlen v > 0) } @-}
-- nonEmpty :: Vector a -> Bool
-- nonEmpty v = length v /= 0

-- -- {-@ isEmpty :: v: Vector a -> {r: Bool | r <=> (vlen v == 0) } @-}
-- isEmpty :: Vector a -> Bool
-- isEmpty v = (length v) == 0

{-@ head'' :: Vector a -> Maybe a @-}
head'' :: Vector a -> Maybe a
head'' x = if length x == 0 then Nothing else Just (x ! 0)

{-@ isBetween :: hi: Int -> lo: Int -> x: Int -> {r: Bool | r <=> ((x >= lo) && (x < hi)) } @-}
isBetween :: Int -> Int -> Int ->Bool
isBetween hi lo x = x >= lo && x < hi

{-@ unsafeLookup :: i: Nat -> {v: Vector a | i < vlen v } -> a @-}
unsafeLookup :: Int -> Vector a -> a
unsafeLookup i v = v ! i

{-@ safeLookup :: Vector a -> Nat -> Maybe a @-}
safeLookup :: Vector a -> Int -> Maybe a
safeLookup x i
  | ok        = Just (x ! i)
  | otherwise = Nothing
  where
    ok        = isBetween 0 (length x) i

{-@ vectorSum :: Vector Int -> Int @-}
vectorSum     :: Vector Int -> Int
vectorSum vec     = go 0 0
  where go acc i
          | i < sz = go (acc + (vec ! i)) (i + 1)
          | otherwise = acc
        sz = length vec

{-@ abs' :: Int -> Nat @-}
abs'           :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n

{-@ absoluteSum :: Vector Int -> Nat @-}
absoluteSum :: Vector Int -> Int
absoluteSum vec = go 0 0
  where go acc i
          | i < sz = go (acc + abs' (vec ! i)) (i + 1)
          | otherwise = acc
        sz = length vec

{-@ loop :: lo: Nat -> hi: {Nat | lo <= hi } -> a -> (Btwn lo hi -> a -> a) -> a @-}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f =  go base lo
  where
    go acc i
      | i < hi    = go (f i acc) (i + 1)
      | otherwise = acc

{-@ vectorSum' :: Vector Int -> Int @-}
vectorSum' :: Vector Int -> Int
vectorSum' vec  = loop 0 n 0 body
  where
    body i acc  = acc + (vec ! i)
    n           = length vec

{-@ absoluteSum' :: Vector Int -> Nat @-}
absoluteSum' :: Vector Int -> Int
absoluteSum' vec = loop 0 n 0 body
  where
    body i acc   = acc + (abs' (vec ! i))
    n            = length vec

{-@ dotProduct :: x: Vector Int -> { y: Vector Int | vlen x == vlen y } -> Int @-}
dotProduct :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 (length x) 0 body
  where
    body i acc = acc + (x ! i)  *  (y ! i)

-- {-@ type SparseN a N = [(Btwn 0 N, a)] @-}

-- {-@ sparseProduct  :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
-- sparseProduct :: Vector Int -> [(Int, Int)] -> Int
-- sparseProduct x y   = go 0 y
--   where
--     go n []         = n
--     go n ((i,v):y') = go (n + (x!i) * v) y'

-- {-@ sparseProduct'  :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
-- sparseProduct' :: Vector Int -> [(Int, Int)] -> Int
-- sparseProduct' x y  = foldl' body 0 y
--   where
--     body sum (i, v) = sum + (x ! i) * v

-- 05. DataTypes


{-@ data Sparse a = SP { spDim :: Nat , spElems :: [(Btwn 0 spDim, a)]} @-}
data Sparse a = SP { spDim :: Int , spElems :: [(Int, a)] }

{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

{-@ dotProduct' :: x: Vector Int -> y: SparseN Int (vlen x) -> Int @-}
dotProduct' :: Vector Int -> Sparse Int -> Int
dotProduct' x (SP _ y) = go 0 y where 
  go acc ((i, n) : xs) = go (acc + x ! i + n) xs
  go acc [] = acc
  
{-@ dotProduct'' :: x: Vector Int -> y: SparseN Int (vlen x) -> Int @-}
dotProduct'' :: Vector Int -> Sparse Int -> Int
dotProduct'' x (SP _ y) = foldl' body 0 y where body acc (i, n) = acc + n + (x ! i)

-- {-@ fromList' :: dim: Int -> [(Int, a)] -> Maybe (SparseN a dim) @-}
{-@ fromList' :: dim: Nat -> [(Int, a)] -> Maybe (Sparse a) @-}
fromList' :: Int -> [(Int, a)] -> Maybe (Sparse a)
fromList' dim ins = 
  case ashkan dim ins of
    Just safe -> Just $ SP dim safe
    Nothing -> Nothing

{-@ ashkan :: dim: Nat -> [(Int, a)] -> Maybe [(Btwn 10 dim, a)] @-}
ashkan :: Int -> [(Int, a)] -> Maybe [(Int, a)]
ashkan dim ((i, _) : xs) = if i >= 0 && i < dim then ashkan (dim - 1) xs else Nothing 
ashkan _   []            = Just []

-- {-@ test1 :: SparseN String 2 @-}
-- test1 = fromJust $ fromList' 2 [(0, "cat"), (2, "mouse")]




