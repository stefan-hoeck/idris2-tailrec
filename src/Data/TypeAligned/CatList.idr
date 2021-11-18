module Data.TypeAligned.CatList

import Data.TypeAligned.List
import Data.TypeAligned.Ops
import Data.TypeAligned.Queue
import Data.TypeAligned.Uncons
import Data.TypeAligned.Unsnoc

%default total

public export
data TCatList : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  CatNil  : TCatList arr a a
  CatCons : arr a b -> TCatQueue (TCatList arr) b c -> TCatList arr a c

public export
empty : TCatList arr a a
empty = CatNil

public export
singleton : arr a b -> TCatList arr a b
singleton v = CatCons v empty

public export
(++) : TCatList arr a b -> TCatList arr b c -> TCatList arr a c
CatNil        ++ x      = x
x             ++ CatNil = x
(CatCons h t) ++ x      =  CatCons h (snoc t x)

public export
cons : arr a b -> TCatList arr b c -> TCatList arr a c
cons f l = singleton f ++ l

public export
snoc : TCatList arr a b -> arr b c -> TCatList arr a c
snoc l f = l ++ singleton f

public export
uncons : TCatList arr a b -> Uncons TCatList arr a b
uncons CatNil = Empty
uncons (CatCons h t) = h :| go (uncons t)
  where go : Uncons TCatQueue (TCatList arr) x y -> TCatList arr x y
        go Empty              = CatNil
        go v@(CatNil    :| w) = go (assert_smaller v $ uncons w)
        go (CatCons z v :| w) = CatCons z (v ++ w)

public export
mapK : (forall u,v . r1 u v -> r2 u v) -> TCatList r1 a b -> TCatList r2 a b
mapK f CatNil        = CatNil
mapK f (CatCons x y) = assert_total $ CatCons (f x) $ mapK (mapK f) y

