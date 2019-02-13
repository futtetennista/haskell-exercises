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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Exercises where

import           Data.Kind     (Constraint, Type)
import           Data.Function ((&))
import qualified GHC.TypeLits   as T
import           Prelude        hiding ((!!))
import           GHC.Exts       (Any)


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

data HList_ (n :: Nat) (types :: List Type) where
  HNil_  :: HList_ 'Z 'Nil
  HCons_ :: a -> HList_ n xs -> HList_ ('S n) ('Cons a xs)

-- take :: Int -> [a] -> [a]
-- take 0 _      = []
-- take _ []     = []
-- take n (x:xs) = x : take (n - 1) xs

type family Take (n :: Nat) (m :: Nat) (xs :: List Type) = (ys :: Type) where
  Take 'Z n list  = HList_ 'Z 'Nil
  Take n  'Z 'Nil = HList_ 'Z 'Nil
  Take n  m xs    = HList_  (Min n m) (TakeList n xs)

type family TakeList (n :: Nat) (types :: List Type) = (types' :: List Type) where
  TakeList 'Z     'Nil         = 'Nil
  TakeList 'Z     ('Cons t ts) = 'Nil
  TakeList ('S n) 'Nil         = 'Nil
  TakeList ('S n) ('Cons t ts) = 'Cons t (TakeList n ts)

type family Length (xs :: List Type) :: Nat where
  Length 'Nil        = 'Z
  Length (Cons _ xs) = 'S (Length xs)

type family Min (n :: Nat) (m :: Nat) :: Nat where
  Min 'Z     n      = 'Z
  Min n      'Z     = 'Z
  Min ('S n) ('S m) = Min n m

-- takeH' :: SNat n -> HList_ m ts -> Take n ts
-- takeH' SZero hlist = HNil_
-- takeH' _     HNil_ = HNil_
-- takeH' (SSucc n) (HCons_ x xs) = HCons_ x (takeH' n xs)

class TakeHList_ (n :: Nat) (ts :: List Type) where
  takeH :: SNat n -> HList_ m ts -> Take n m ts

instance TakeHList_ 'Z xs where
  takeH SZero _hlist = HNil_

instance TakeHList_ n 'Nil where
  takeH n HNil_ = HNil_

instance (TakeHList_ n xs) => TakeHList_ ('S n) ('Cons x xs) where
  takeH (SSucc n) (HCons_ x xs) = HCons_ x (takeH n xs)

-- data Fin (n :: T.Nat) where
--   FinZ :: Fin (n T.+ 1)
--   FinS :: Fin n -> Fin (n T.+ 1)

type family TakeMin (n :: Nat) (m :: Nat) :: Nat where
  TakeMin 'Z     n      = 'Z
  TakeMin n      'Z     = 'Z
  TakeMin ('S n) ('S m) = TakeMin n m

type family LessThan (n :: Nat) (m :: Nat) :: Bool where
  LessThan 'Z     ('S n) = 'True
  LessThan ('S n) 'Z     = 'False
  LessThan ('S n) ('S m) = LessThan n m

class SingE (a :: k) where
  type Demote a :: Type
  fromSing :: Sing a -> Demote (a' :: k)

data family Sing (a :: k)

instance SingE (a :: Nat) where
  type Demote a = Nat
  fromSing SZero     = Z
  fromSing (SSucc n) = S (fromSing n)


-- class TakeHList_ (n :: Nat) (ts :: List Type) (ts' :: List Type) | n ts -> ts' where
--   takeH :: (TakeList n ts ~ ts', TakeMin n m ~ n') => SNat n -> HList_ m ts -> HList_ n' ts'

-- instance TakeHList_ 'Z xs 'Nil where
--   takeH _ _ = HNil_

-- instance TakeHList_ n 'Nil 'Nil where
--   takeH _ HNil_ = HNil_

-- instance (TakeHList_ n xs xs', TakeList n xs ~ xs', SPred n n')
--   => TakeHList_ ('S n) (Cons x xs) (Cons x xs') where
--   takeH n (HCons_ x xs) = HCons_ x (takeH (spred n) xs)

class SPred (n :: Nat) (m :: Nat) | n -> m where
  spred :: SNat ('S n) -> SNat n


-- class SPred ('S n) n where
--   spred = const undefined

-- takeHList_
--   :: (TakeList n ts ~ ts', TakeMin n m ~ n')
--   => SNat n
--   -> HList_ m ts
--   -> HList_ n' ts'
-- takeHList_  n = takeHList_' (fromSing n)
--   where
--     takeHList_'
--       :: Nat
--       -> HList_ m ts
--       -> HList_ n' ts'
--     takeHList_' Z      hl            = _
    -- takeHList_' (S n) (HCons_ x xs) = HCons_ x (takeHList_' n xs)

-- class TakeHList_ a where
--   takeHList
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

type SNat (a :: Nat) = Sing a
data instance Sing (value :: Nat) where
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

data Program' (fh :: FileHandle) result where
  OpenFile'  :: Program' 'FileHandleOpened result -> Program' 'FileHandleClosed result
  WriteFile' :: String -> Program' 'FileHandleOpened result -> Program' 'FileHandleOpened result
  ReadFile'  :: Program' 'FileHandleOpened result -> (String -> Program' 'FileHandleOpened result)
  CloseFile' :: Program' 'FileHandleClosed result -> Program' 'FileHandleOpened result
  Exit'      :: result -> Program' 'FileHandleClosed result

data FileHandle
  = FileHandleOpened
  | FileHandleClosed

-- enter :: Program' 'Init res
-- enter = Enter'

-- openFile :: Program' 'Init res -> Program' 'FileHandleOpened res
-- openFile = OpenFile'

-- closeFile :: Program' 'FileHandleOpened res -> Program' 'FileHandleClosed res
-- closeFile = CloseFile'

-- readFile :: (String -> Program' 'FileHandleOpened res) -> Program' 'FileHandleOpened res
-- readFile = ReadFile'

-- writeFile :: String -> Program' 'FileHandleOpened res -> Program' 'FileHandleOpened res
-- writeFile str = WriteFile' str

-- exit :: Program' 'FileHandleClosed res -> Program' 'Exited res
-- exit = Exit'

-- | EXTRA: write an interpreter for this program. Nothing to do with data
-- kinds, but a nice little problem.

program' :: Program' 'FileHandleClosed Int
program' = OpenFile' $ WriteFile' "Foo" $ CloseFile' $ Exit' 0

interpret :: Program' st a -> IO a
interpret (OpenFile' next) = putStrLn "Opened file..." >> interpret next
interpret (CloseFile' next) = putStrLn "Closed file..." >> interpret next
interpret (Exit' result) = putStrLn "Session ended" >> pure result




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
