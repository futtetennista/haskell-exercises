{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Exercises where

import Control.Arrow



{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int
instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  CountableEmpty  :: CountableList
  CountableCons   :: Countable a => a -> CountableList -> CountableList

-- How is the previous GADTs desugared? Not like this but then how?!
-- data CountableList
--   = CountableEmpty
--   | CountableCons (forall a. Countable a => a) CountableList

-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList = \case
  CountableEmpty   -> 0
  CountableCons x xs -> count x + countList xs


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero = \case
  CountableEmpty     -> CountableEmpty
  CountableCons x xs -> if count x == 0
                        then dropZero xs
                        else CountableCons x (dropZero xs)


-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?

filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"

-- I know only that the values inside `CountableList` are `Countable` but I
-- cannot say anything more about them. Thus I have no idea about their types.



{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  AnyEmpty :: AnyList
  AnyCons  :: a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?

reverseAnyList :: AnyList -> AnyList
reverseAnyList = go id
  where
    go :: (AnyList -> AnyList) -> AnyList -> AnyList
    go f AnyEmpty = f AnyEmpty
    go f (AnyCons x xs) = go (AnyCons x . f) xs
  -- AnyEmpty     -> AnyEmpty
  -- AnyCons x xs -> reverseAnyList' (AnyCons x AnyEmpty) xs

  -- where
  --   reverseAnyList' anyList = \case
  --     AnyEmpty     -> anyList
  --     AnyCons x xs -> reverseAnyList' xs (AnyCons x anyList)

filterAnyList :: (a -> Bool) -> AnyList -> AnyList
filterAnyList = error "I don't know anything about the shape of the values in AnyList"

lengthAnyList :: AnyList -> Int
lengthAnyList = \case
  AnyEmpty     -> 0
  AnyCons _ xs -> 1 + lengthAnyList xs

foldAnyList :: Monoid m => AnyList -> m
foldAnyList = \case
  AnyEmpty     -> mempty
  AnyCons x xs -> error "Does x have a Monoid instance?"

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList = \case
  AnyEmpty -> True
  _        -> False

instance Show AnyList where
  show = \case
    AnyEmpty     -> "AnyEmpty"
    AnyCons x xs -> error "Do values in AnyList have a Show instance?!"





{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    -> input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?

-- input is existential, we can just transform it to an ouput

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?

instance Eq output => Eq (TransformableTo output) where
  TransformWith f x == TransformWith f' x'
    = f x == f' x'

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?

instance Functor TransformableTo where
  fmap f (TransformWith g x)
    = TransformWith f (g x)




{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?

isEq :: EqPair -> Bool
isEq (EqPair x y) = x == y

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)

data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?

-- with some help courtesy of -XExistentialQuantification
data EqPair'' a = Eq a => EqPair'' a a



{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ ibox) = getInt ibox

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers = \case
  EmptyBox         -> 0
  IntBox _ _       -> 1
  StringBox _ ibox -> 1 + countLayers ibox
  BoolBox _ sbox   -> 1 + countLayers sbox

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?

stripLayer :: MysteryBox a -> MysteryBox b
stripLayer = undefined
-- stripLayer (IntBox _ ebox) = ebox
-- stripLayer (StringBox _ ibox) = ibox




{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!

hHead :: HList (a, as) -> a
hHead (HCons x _) = x

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

-- patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe :: HList (Int, (String, (Bool, ()))) -> Int
patternMatchMe = \case
  HCons x (HCons _str (HCons _bool HNil)) -> x

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?
hCons :: HList a -> HList b -> HList ab
hCons = error "How can I 'inject' the second tuple into the first one?!"




{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HEmpty  :: HTree Empty
  HBranch :: HTree l -> HTree c -> HTree r -> HTree (Branch l c r)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?

deleteLeft :: HTree (Branch l c r) -> HTree (Branch Empty c r)
deleteLeft (HBranch _l c r) = HBranch HEmpty c r

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. Recursion is your friend here - you
-- shouldn't need to add a constraint to the GADT!

instance Eq (HTree Empty) where
  _ == _ = True

instance (Eq (HTree l), Eq (HTree c), Eq (HTree r))
  => Eq (HTree (Branch l c r)) where

  HBranch l c r == HBranch l' c' r' = l == l' && c == c' && r == r'




{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  ANil  :: AlternatingList a b
  ACons :: a -> AlternatingList b a -> AlternatingList a b

aList :: AlternatingList Bool Int
aList = ACons True (ACons 1 (ACons False (ACons 2 ANil)))

-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts = \case
  ANil       -> []
  ACons x xs -> x : getSeconds xs

getSeconds :: AlternatingList a b -> [b]
getSeconds = \case
  ANil       -> []
  ACons _ xs -> getFirsts xs

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues alist = (mconcat (getFirsts alist), mconcat (getSeconds alist))

foldValues' :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues'
  = foldFstValues (mempty, mempty)

  where
    foldFstValues (x, y) = \case
      ANil        -> (x, y)
      ACons x' xs -> foldSndValues (x' <> x, y) xs

    foldSndValues (x, y) = \case
      ANil        -> (x, y)
      ACons x' xs -> foldFstValues (x, x' <> y) xs

-- much neater trick recusively swapping tuple elems:
foldValues'' :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues'' = \case
  ANil       -> (mempty, mempty)
  ACons x xs -> let (b, a) = foldValues'' xs in (x <> a, b)




{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool
  -- BinOp     :: Expr (a -> b -> c) -> Expr a -> Expr b -> Expr c

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval = \case
  Equals x y  -> eval x == eval y
  Add x y     -> eval x + eval y
  If p x y    -> if eval p then eval x else eval y
  IntValue x  -> x
  BoolValue x -> x

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

parse :: DirtyExpr -> Maybe (Expr Int)
parse = \case
  DirtyAdd (DirtyIntValue x) (DirtyIntValue y) -> Just (IntValue (x + y))
  DirtyIntValue x                              -> Just (IntValue x)
  _                                            -> Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe'?

-- We could have a more general `BinOp` constructor to encode more binary ops
-- data Expr a where
--   ... BinOp :: Expr (a -> b -> c) -> Expr a -> Expr b -> Expr c




{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  TypeAlignedNil :: TypeAlignedList a a
  TypeAlignedCons :: (a -> c) -> TypeAlignedList c b -> TypeAlignedList a b

-- | b. Which types are existential?
-- `a -> c`, `TypeAlignedList c b` b/c `c` is existential

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs bcl abl = TypeAlignedCons (tof abl) bcl
  where
    tof :: TypeAlignedList a b -> (a -> b)
    tof TypeAlignedNil         = id
    tof (TypeAlignedCons f fs) = tof fs . f
