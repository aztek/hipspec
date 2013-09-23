{-

              Instantiates the polymorphic FOL to monomorphic FOL

    The clauses need a 'Goal' to work, where everything is monomorphised from.

-}
module InstPolyFOL where

import Data.Set (Set)
import qualified Data.Set as S

type Trigger a = (a,[Type a])

-- Instantiates a function with a given type
type InstFn a = [Type a] -> Maybe ([Clause a],Set (Trigger a))

-- An instantiator, given /function/ name, it says all triggers it is
-- associated with.
--
-- Scheme: remember all types you have instantiated it at, then update the TypeSigs,
--
type Inst a = (a,InstFn a)

tryCombine :: Ord a => Inst a -> Inst a -> Maybe (Inst a)
tryCombine (f,fi) (g,gi) | f == g = Just (f,combInstFn fi gi)

combInstFn :: Ord a => InstFn a -> InstFn a -> InstFn a
combInstFn fi gi = \ xs -> fi xs `plus` gi xs
  where
    plus (Just (c1,t1)) (Just (c2,t2)) = Just (c1 ++ c2,t1 `S.union` t2)
    plus Nothing        r              = r
    plus r              Nothing        = r

mkInst :: Clause
