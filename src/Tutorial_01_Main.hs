{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--reflection"          @-}

module Tutorial_01_Main where
{- size  :: xs:[a] -> {v:Int | v = size xs} @-}

-- ax1 :: Int -> Bool
-- ax2 :: Int -> Bool
-- ax3 :: Int -> Int -> Bool
-- ax4 :: Int -> Int -> Bool
-- ax5 :: Int -> Int -> Int -> Bool
-- ax6 :: Int -> Int -> Bool

-- congruence :: (Int -> Int) -> Int -> Int -> Bool
-- fx1 :: (Int -> Int) -> Int -> Bool

infixr 9 ==>

-- {-@ invariant {v:[a] | size v >= 0} @-}

-- {-@ fail ex0' @-}
-- {-@ fail ex3' @-}
-- {-@ fail exDeMorgan2 @-}
-- {-@ fail ax0' @-}
-- {-@ fail ax6 @-}

{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False

{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = {v:Bool | not v} @-}

ex0 :: Bool
{-@ ex0 :: TRUE @-}
ex0 = True

-- ex0' :: Bool
-- {-@ ex0' :: TRUE @-}
-- ex0' = False

{-@ ex1 :: Bool -> TRUE @-}
ex1 b = b || not b

{-@ ex2 :: Bool -> FALSE @-}
ex2 b = b && not b

{-@ ext3 :: Bool -> Bool -> TRUE @-}
ext3 a b = (a && b) ==> a

{-@ ext4 :: Bool -> Bool -> TRUE @-}
ext4 a b = (a && b) ==> b

{-@ ex3' :: Bool -> Bool -> TRUE @-}
ex3' a b = (a || b) ==> not (not a && not b)

{-@ ex6 :: Bool -> Bool -> TRUE @-}
ex6 a b = (a && (a ==> b)) ==> b

{-@ ex7 :: Bool -> Bool -> TRUE @-}
ex7 a b = a ==> (a ==> b) ==> b

{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
False <=> False = True
False <=> True  = False
True  <=> True  = True
True  <=> False = False

{-@ exDeMorgan1 :: Bool -> Bool -> TRUE @-}
exDeMorgan1 a b = not (a || b) <=> (not a && not b)

{-@ exDeMorgan2 :: Bool -> Bool -> TRUE @-}
exDeMorgan2 a b = not (a && b) <=> (not a || not b)

{-@ ax0 :: TRUE @-}
ax0 = 1 + 1 == 2

-- {-@ ax0' :: TRUE @-}
-- ax0' = 1 + 1 == 3

{-@ ax1 :: Int -> TRUE @-}
ax1 :: Int -> Bool
ax1 x = x < x + 1

{-@ ax2 :: Int -> TRUE @-}
ax2 :: Int -> Bool
ax2 x = (x < 0) ==> (0 <= -x)

{-@ ax3 :: Int -> Int -> TRUE @-}
ax3 :: Int -> Int -> Bool
ax3 x y = (x >= 0) ==> (y >= 0) ==> (x + y >= 0)

{-@ ax4 :: Int -> Int -> TRUE @-}
ax4 :: Int -> Int -> Bool
ax4 x y = (x == y - 1) ==> (x + 2 == y +1)

{-@ ax5 :: Int -> Int -> Int -> TRUE @-}
ax5 :: Int -> Int -> Int -> Bool
ax5 x y z = (x <= 0 && x >= 0) ==>
            (y == x + z) ==>
            (y == z)

{-@ ax6 :: Int -> Int -> TRUE @-}
ax6 :: Int -> Int -> Bool
ax6 x y = (y >= 0) ==> (x <= x + y)     

{-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
congruence :: (Int -> Int) -> Int -> Int -> Bool
congruence f x y = (x == y) ==> (f x == f y)

{-@ fx1 :: (Int -> Int) -> Int -> TRUE @-}
fx1 :: (Int -> Int) -> Int -> Bool
fx1 f x =   (x == f (f (f x)))
        ==> (x == f (f (f (f (f x)))))
        ==> (x == f x)

-- {-@ measure size @-}
-- {-@ size :: [a] -> Nat @-}
-- size        :: [a] -> Int
-- size []     = 0
-- size (_:xs) = 1 + size xs        

-- {-@ fx0 :: [a] -> [a] -> TRUE @-}
-- fx0 :: [a] -> [a] -> Bool
-- fx0 xs ys = (xs == ys) ==> (size xs == size y)

{-@ fx2 :: a -> [a] -> TRUE @-}
fx2 :: a -> [a] -> Bool
fx2 x xs = 0 < length (x:xs)

-- 3. Refinement Types

{-@ type Zero = {v : Int | v == 0 } @-}
{-@ type NonZero = {v : Int | v /= 0 } @-}

{-@ zero :: Zero @-}
zero = 0 :: Int

{-@ one,two,three :: NonZero @-}
one = 1 :: Int
two = 2 :: Int
three = 3 :: Int

-- {-@ one' :: Zero @-}
-- one' = 1 :: Int

{-@ type Nat2 = {v: Int | v > 0 } @-}
{-@ type Even = {v: Int | v mod 2 == 0 } @-}
{-@ type Lt100 = {v: Int | v < 100 } @-}

{-@ die :: {v: String | false } -> a @-}
die msg = error msg

cannotDie = if 1 == 2 then die "Oops" else ()

-- divide' :: Int -> Int -> Int
-- divide' _ 0 = die "Can't divide by zero"
-- divide' x y = x `div` y

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "Can't divide by zero"
divide x y = x `div` y

avg2 x y   = divide (x + y) 2
avg3 x y z = divide (x + y + z) 3

{-@ type NonEmpty a = {v: [a] | len v /= 0 } @-}

{-@ avg :: NonEmpty Int -> Int @-}
avg       :: [Int] -> Int
avg xs    = divide total n
  where
    total = sum xs
    n     = length xs

{-@ abs' :: Int -> Nat @-}
abs'           :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n

calc = do putStrLn "Enter numerator"
          n <- readLn
          putStrLn "Enter denominator"
          d <- readLn
          putStrLn (result n d)
          calc

result n d
  | isPositive d = "Result = " ++ show (n `divide` d)
  | otherwise    = "Humph, please enter positive denominator!"            

{-@ isPositive :: Ord a => x: a -> {v: Bool | v <=> x > 0 } @-}
-- isPositive :: Int -> Bool
isPositive x = x > 0

{-@ lAssert  :: {v: Bool | v == True } -> a -> a @-}
lAssert :: Bool -> a -> a
lAssert True  x = x
lAssert False _ = die "yikes, assertion fails!"

yes = lAssert (1 + 1 == 2) ()
-- no  = lAssert (1 + 1 == 3) ()

truncate :: Int -> Int -> Int
truncate i max
  | i' <= max' = i -- i' > max' && max' >= 0 --> i' > 0
  | otherwise  = max' * (i `divide` i')
    where
      i'       = abs' i
      max'     = abs' max   