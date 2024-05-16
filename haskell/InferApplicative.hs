module InferApplicative where

import Control.Monad (guard)
import Data.Foldable (asum, find)

data N = Z | S !N deriving (Eq, Ord, Show)

instance Enum N where
  succ = S
  pred (S n) = n
  pred Z = Z
  toEnum n = iterate S Z !! n
  fromEnum Z = 0
  fromEnum (S n) = 1 + fromEnum n

instance Num N where
  fromInteger 0 = Z
  fromInteger n = S (fromInteger (n - 1))

  (+) = (.+)

infixl 6 ∸
infixl 6 .+

(∸) :: N -> N -> N
S n ∸ S m = n ∸ m
n ∸ Z = n
Z ∸ _ = Z

(.+) :: N -> N -> N
Z .+ m = m
(S n) .+ m = S (n .+ m)

data Base = Nat | Chr deriving (Eq, Ord, Show)

data BoxTree b where
  Boxes :: N -> BoxTreeNode b -> BoxTree b
  deriving (Eq, Ord, Show)

data BoxTreeNode b where
  Base :: b -> BoxTreeNode b
  (:->:) :: BoxTree b -> BoxTree b -> BoxTreeNode b
  deriving (Eq, Ord, Show)

box :: N -> BoxTree b -> BoxTree b
box n (Boxes m t) = Boxes (n + m) t

-- | Check if s <: t.
isSubtype :: Eq b => BoxTree b -> BoxTree b -> Bool
isSubtype s t = check s t == Just Z

-- | Return the smallest n such that removing n boxes from s allows
--   s <: t, or Nothing if it is impossible
check :: Eq b => BoxTree b -> BoxTree b -> Maybe N
check (Boxes m s) (Boxes n t) = checkN (m ∸ n) s t

-- | Check if []^n s <: t, return value is same as check
checkN :: Eq b => N -> BoxTreeNode b -> BoxTreeNode b -> Maybe N
checkN n (Base b1) (Base b2)
  | b1 == b2 = Just n
  | otherwise = Nothing
-- Find smallest k such that removing k boxes from LHS makes subtyping possible.
checkN n (s1 :->: s2) (t1 :->: t2) = find (checkArr s1 s2 t1 t2 . (n ∸)) [Z .. n]
checkN _ _ _ = Nothing

-- | pullBox t tries to "pull n boxes out" of a t in a negative
--   position.  If t already has enough boxes at the top level, just remove
--   them.  Otherwise, if t is an arrow, we can pull boxes out by
--   recursively pulling boxes out of its (negative) RHS, simply
--   creating boxes with pure at its positive LHS, and then pulling
--   the boxes up with ap.
pullBoxes :: N -> BoxTree b -> Maybe (BoxTree b)
pullBoxes n (Boxes m t)
  | n <= m = Just $ Boxes (m ∸ n) t
  | otherwise = Boxes Z <$> pullBoxesNode (n ∸ m) t

pullBoxesNode :: N -> BoxTreeNode b -> Maybe (BoxTreeNode b)
pullBoxesNode _ (Base _) = Nothing
pullBoxesNode n (s :->: t) = (s :->:) <$> pullBoxes n t

-- | Check if ([]^n (s1 -> s2) <: t1 -> t2).  Have to push n boxes
-- down through (s1 -> s2).
checkArr :: Eq b => BoxTree b -> BoxTree b -> BoxTree b -> BoxTree b -> N -> Bool
checkArr s1 s2 t1 t2 n = maybe False (const True) $ do
  n1 <- check t1 (box n s1)
  t2' <- pullBoxes n1 t2
  n2 <- check (box n s2) t2'
  guard (n2 == Z)
