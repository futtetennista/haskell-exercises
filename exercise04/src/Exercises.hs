{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Exercises where

import           Data.Kind     (Constraint, Type)
import           Data.Function ((&))
import qualified GHC.TypeLits   as T
import           Prelude        hiding ((!!))



{- ONE -}

-- | One of the restrictions around classes that we occasionally hit is that we
-- can only have one instance for a type. There are, for example, two good
-- candidates for a monoid instance when we think about 'Integer':

data IntegerMonoid = Sum | Product

-- | a. Write a newtype around 'Integer' that lets us choose which instance we
-- want.

newtype Integer' (a ::IntegerMonoid) = Integer' Integer deriving (Eq, Show)

-- | b. Write the two monoid instances for 'Integer'.

instance Semigroup (Integer' Sum) where
  Integer' x <> Integer' y = Integer' (x + y)

instance Monoid (Integer' Sum) where
  mempty = Integer' 0

instance Semigroup (Integer' Product) where
  Integer' x <> Integer' y = Integer' (x * y)

instance Monoid (Integer' Product) where
  mempty = Integer' 1

-- | c. Why do we need @FlexibleInstances@ to do this?





{- TWO -}

-- | We can write a type that /is/ of kind 'Type', but has no value-level
-- members. We usually call this type 'Void':

data Void -- No constructors!

-- | a. If we promote this with DataKinds, can we produce any /types/ of kind
-- 'Void'?
-- Is 'undefined' allowed?

-- | b. What are the possible type-level values of kind 'Maybe Void'?
-- undefined

-- | c. Considering 'Maybe Void', and similar examples of kinds such as
-- 'Either Void Bool', why do you think 'Void' might be a useful kind?
-- It indicates that there cannot be any values in the `Left` ctor




{- THREE -}

-- | a. Write a GADT that holds strings or integers, and keeps track of how
-- many strings are present. Note that you might need more than 'Nil' and
-- 'Cons' this time...

data Nat = Z | S Nat

data StringAndIntList (stringCount :: Nat) where
  SAINil        :: StringAndIntList 'Z
  SAIIntCons    :: Int -> StringAndIntList n -> StringAndIntList n
  SAIStringCons :: String -> StringAndIntList n -> StringAndIntList ('S n)


-- | b. Update it to keep track of the count of strings /and/ integers.

data StringAndIntList' (stringCount :: Nat) (intCount :: Nat) where
  SAINil'        :: StringAndIntList' 'Z 'Z
  SAIIntCons'    :: Int -> StringAndIntList' n m -> StringAndIntList' n ('S m)
  SAIStringCons' :: String -> StringAndIntList' n m -> StringAndIntList' ('S n) m

-- | c. What would be the type of the 'head' function?
stringAndIntHead :: StringAndIntList n -> Maybe (Either String Int)
stringAndIntHead SAINil              = Nothing
stringAndIntHead (SAIStringCons x _) = Just (Left x)
stringAndIntHead (SAIIntCons x _)    = Just (Right x)

stringAndIntHead' :: StringAndIntList' (S n) (S m) -> Either String Int
stringAndIntHead' (SAIStringCons' x _) = Left x
stringAndIntHead' (SAIIntCons' x _)    = Right x




{- FOUR -}

-- | When we talked about GADTs, we discussed existentials, and how we could
-- only know something about our value if the context told us:

data Showable where
  Showable :: Show a => a -> Showable

-- | a. Write a GADT that holds something that may or may not be showable, and
-- stores this fact in the type-level.

data MaybeShowable (isShowable :: Bool) where
  JustShowable    :: Show a => a -> MaybeShowable 'True
  NothingShowable :: a -> MaybeShowable 'False
  -- ...

-- | b. Write a 'Show' instance for 'MaybeShowable'. Your instance should not
-- work unless the type is actually 'show'able.

instance Show (MaybeShowable 'True) where
  show (JustShowable x) = show x

-- | c. What if we wanted to generalise this to @Constrainable@, such that it
-- would work for any user-supplied constraint of kind 'Constraint'? How would
-- the type change? What would the constructor look like? Try to build this
-- type - GHC should tell you exactly which extension you're missing.

data MaybeC (c :: Constraint) where
  WithC :: c => a -> MaybeC c


{- FIVE -}

-- | Recall our list type:

data List a = Nil | Cons a (List a)

-- | a. Use this to write a better 'HList' type than we had in the @GADTs@
-- exercise. Bear in mind that, at the type-level, 'Nil' and 'Cons' should be
-- "ticked". Remember also that, at the type-level, there's nothing weird about
-- having a list of types!

data HList (types :: List Type) where
  HNil  :: HList 'Nil
  HCons :: a -> HList xs -> HList ('Cons a xs)

-- | b. Write a well-typed, 'Maybe'-less implementation for the 'tail' function
-- on 'HList'.
tail :: HList ('Cons a as) -> HList as
tail (HCons _ xs) = xs

-- | c. Could we write the 'take' function? What would its type be? What would
-- get in our way?
-- No info at the type level about the length of the HList

data Vector_ (n :: T.Nat) (a :: Type) = VNil_ | VCons_ a (Vector_ n a)

data HList_ (idx :: T.Nat) (types :: List Type) where
  HNil_  :: HList_ 0 'Nil
  HCons_ :: a -> HList_ n xs -> HList_ (n T.+ 1) ('Cons a xs)

data Fin (n :: T.Nat) where
  FinZ :: Fin (n T.+ 1)
  FinS :: Fin n -> Fin (n T.+ 1)

type family Foo (fin :: T.Nat) (n :: T.Nat) where
  Foo 1 n =   0
  -- Foo n n = n T.- 1

-- takeHList_ :: Fin n -> HList_ n ts -> HList_ (Foo n n) ts
-- takeHList_ FinZ HNil_ = HNil_
-- takeHList_ (FinS n) (HCons_ x xs) = HCons_ x (takeHList_ n xs)

-- class TakeHList_ a where
--   takeHList_
--     :: forall (n :: T.Nat) (m :: T.Nat) (ts :: List Type)
--     . (n T.<= m)
--     => HList_ m ts
--     -> HList_ (m T.- n) ts

-- instance TakeHList_ (HList_ 0 'Nil) where
--   -- takeHList_
--   --   :: forall (n :: T.Nat) m ts. (n T.<= m, n ~ 0, m ~ 0)
--   --   => HList_ m ts
--   --   -> HList_ m ts
--   takeHList_
--     :: forall (n :: T.Nat) (m :: T.Nat) (ts :: List Type)
--     .  (n ~ 0, m ~  0, n T.<= m)
--     => HList_ 0 ts
--     -> HList_ 0 ts
--   takeHList_ HNil_  = HNil_

-- instance TakeHList_ (HList_ m ts) where
--   -- takeHList_ :: forall (n :: T.Nat) m ts. (n T.<= m) => HList_ m ts -> HList_ (m T.- n) ts
--   takeHList_ (HCons_ x xs) = undefined


{- SIX -}

-- | Here's a boring data type:

data BlogAction
  = AddBlog
  | DeleteBlog
  | AddComment
  | DeleteComment

-- | a. Two of these actions, 'DeleteBlog' and 'DeleteComment', should be
-- admin-only. Extend the 'BlogAction' type (perhaps with a GADT...) to
-- express, at the type-level, whether the value is an admin-only operation.
-- Remember that, by switching on @DataKinds@, we have access to a promoted
-- version of 'Bool'!

data User = Admin | All

data BlogAction' (admin :: User) where
  AddBlog'       :: BlogAction' 'All
  AddComment'    :: BlogAction' 'All
  DeleteBlog'    :: BlogAction' 'Admin
  DeleteComment' :: BlogAction' 'Admin

-- | b. Write a 'BlogAction' list type that requires all its members to be
-- the same "access level": "admin" or "non-admin".

data BlogActionList (isSafe :: User) where
  BANil :: BlogActionList isSafe
  BACons :: BlogAction' isSafe -> BlogActionList isSafe -> BlogActionList isSafe

-- you got me Tom :)

-- | c. Let's imagine that our requirements change, and 'DeleteComment' is now
-- available to a third role: moderators. Could we use 'DataKinds' to introduce
-- the three roles at the type-level, and modify our type to keep track of
-- this?

data User_ = Admin_ | Moderator_ | Cust_

data BlogAction_ (users :: [User_]) where
  AddBlog_       :: BlogAction_ ['Cust_, 'Moderator_, 'Admin_]
  AddComment_    :: BlogAction_ ['Cust_, 'Moderator_, 'Admin_]
  DeleteBlog_    :: BlogAction_ ['Moderator_, 'Admin_]
  DeleteComment_ :: BlogAction_ ['Admin_, 'Moderator_]

data BlogActionList_ (isSafe :: [User_]) where
  BANil_  :: BlogActionList_ '[]
  BACons_ :: BlogAction_ us -> BlogActionList_ us' -> BlogActionList_ (AppendUsers_ us us')

type family AppendUsers_ (xs :: [User_]) (ys :: [User_]) where
  AppendUsers_ '[] xs = xs
  AppendUsers_ xs '[] = xs
  AppendUsers_ (x ': xs) (x ': ys) = x ': AppendUsers_ xs ys
  AppendUsers_ (x ': xs) ys = NoDups x ys xs ys

type family NoDups (x :: User_) (ys :: [User_]) (xs :: [User_]) (ys' :: [User_]) where
  NoDups x (x ': ys) xs ys' = AppendUsers_ xs ys'
  NoDups x (y ': ys) xs ys' = NoDups x ys xs ys'
  NoDups x '[]       xs ys' = x ': AppendUsers_ xs ys'

{- SEVEN -}

-- | When we start thinking about type-level Haskell, we inevitably end up
-- thinking about /singletons/. Singleton types have a one-to-one value-type
-- correspondence - only one value for each type, only one type for each value.
-- A simple example is '()', whose only value is '()'. 'Bool' is /not/ a
-- singleton, because it has multiple values.

-- We can, however, /build/ a singleton type for 'Bool':

data SBool (value :: Bool) where
  SFalse :: SBool 'False
  STrue  :: SBool 'True

-- | a. Write a singleton type for natural numbers:

data SNat (value :: Nat) where
  SZero :: SNat 'Z
  SSucc :: SNat n -> SNat ('S n)

-- | b. Write a function that extracts a vector's length at the type level:

vlength :: Vector n a -> SNat n
vlength VNil         = SZero
vlength (VCons _ xs) = SSucc (vlength xs)

-- | c. Is 'Proxy' a singleton type?

data Proxy a = Proxy

-- Nope. e.g. Proxy :: Proxy Int, Proxy :: Proxy String etc.




{- EIGHT -}

-- | Let's imagine we're writing some Industry Haskell™, and we need to read
-- and write to a file. To do this, we might write a data type to express our
-- intentions:

data Program                     result
  = OpenFile            (Program result)
  | WriteFile  String   (Program result)
  | ReadFile  (String -> Program result)
  | CloseFile (          Program result)
  | Exit                         result

-- | We could then write a program like this to use our language:

myApp :: Program Bool
myApp
  = OpenFile $ WriteFile "HEY" $ (ReadFile $ \contents ->
      if contents == "WHAT"
        then WriteFile "... bug?" $ Exit False
        else CloseFile            $ Exit True)

-- | ... but wait, there's a bug! If the contents of the file equal "WHAT", we
-- forget to close the file! Ideally, we would like the compiler to help us: we
-- could keep track of whether the file is open at the type level!
--
-- - We should /not/ be allowed to open a file if another file is currently
-- open.
--
-- - We should /not/ be allowed to close a file unless a file is open.
--
-- If we had this at the type level, the compiler should have been able to tell
-- us that the branches of the @if@ have different types, and this program
-- should never have made it into production. We should also have to say in the
-- type of 'myApp' that, once the program has completed, the file will be
-- closed.

-- | Improve the 'Program' type to keep track of whether a file is open.  Make
-- sure the constructors respect this flag: we shouldn't be able to read or
-- write to the file unless it's open. This exercise is a bit brain-bending;
-- why? How could we make it more intuitive to write?

-- | EXTRA: write an interpreter for this program. Nothing to do with data
-- kinds, but a nice little problem.

interpret :: Program {- ??? -} a -> IO a
interpret = error "Implement me?"





{- NINE -}

-- | Recall our vector type:

data Vector (n :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | Imagine we want to write the '(!!)' function for this vector. If we wanted
-- to make this type-safe, and avoid 'Maybe', we'd have to have a type that can
-- only hold numbers /smaller/ than some type-level value.

-- | a. Implement this type! This might seem scary at first, but break it down
-- into Z and S cases. That's all the hint you need :)

data SmallerThan (limit :: Nat) where
  SmallerThanZ :: SmallerThan ('S n)
  SmallerThanS :: SmallerThan n -> SmallerThan ('S n)

deriving instance (Eq (SmallerThan limit))
deriving instance (Show (SmallerThan limit))

-- | b. Write the '(!!)' function:

(!!) :: Vector n a -> SmallerThan n -> a
VCons x _  !! SmallerThanZ   = x
VCons _ xs !! SmallerThanS n = xs !! n

-- ex = VCons 0 (VCons 1 VNil) !! SmallerThanS (SmallerThanS (SmallerThanZ))

-- | c. Write a function that converts a @SmallerThan n@ into a 'Nat'.
toNat :: SmallerThan n -> Nat
toNat SmallerThanZ     = Z
toNat (SmallerThanS n) = S (toNat n)
