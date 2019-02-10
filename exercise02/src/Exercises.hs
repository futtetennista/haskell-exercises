module Exercises where

class PopQuiz a

-- | Which of the following instances require 'FlexibleInstances'? Don't cheat
-- :D This is a tricky one, but look out for nested concrete types!

instance PopQuiz Bool
-- instance PopQuiz [Bool] -- Need
instance PopQuiz [a]         -- Need => NOPE
instance PopQuiz (a, b)      -- Need => NOPE
-- instance PopQuiz [(a, b)] -- NEEDED: some tuple in the list could be the same
instance PopQuiz (IO a)   -- Need => NOPE

newtype RIO  r a = RIO (r -> IO a) -- Remember, this is a /new type/.
type    RIO' r a =      r -> IO a

-- instance PopQuiz (RIO Int a) -- Need
instance PopQuiz (RIO r a)
-- instance PopQuiz (RIO' r a) -- Need
-- instance PopQuiz (r -> IO a) -- Need
instance PopQuiz (a -> b) -- We can write (a -> b) as ((->) a b).
-- instance PopQuiz (a -> b -> c) -- Need
instance PopQuiz (a, b, c)
-- instance PopQuiz (a, (b, c)) -- NEEDED
instance PopQuiz ()
-- instance PopQuiz (a, b, c, a) -- Need

data Pair  a = Pair  a  a
type Pair' a =      (a, a)

-- instance PopQuiz (a, a) -- Need
-- instance PopQuiz (Pair a)
-- instance PopQuiz (Pair' a) -- Need
