module Data.TypeAligned.Queue

import Data.TypeAligned.List
import Data.TypeAligned.Ops
import Data.TypeAligned.Uncons
import Data.TypeAligned.Unsnoc

%default total

public export
record TCatQueue (arr : Type -> Type -> Type) (a,b : Type) where
  constructor MkCatQueue
  init : TList arr a x
  last : TSnocList arr x b

public export
empty : TCatQueue arr a a
empty = MkCatQueue Nil Lin

public export
singleton : arr a b -> TCatQueue arr a b
singleton = MkCatQueue Nil . singleton

public export
cons : arr a b -> TCatQueue arr b c -> TCatQueue arr a c
cons f (MkCatQueue init last) = MkCatQueue (f :: init) last

public export
snoc : TCatQueue arr a b -> arr b c -> TCatQueue arr a c
snoc (MkCatQueue init last) y = MkCatQueue init (last :< y)

public export
mapK : (forall u,v . r1 u v -> r2 u v) -> TCatQueue r1 a b -> TCatQueue r2 a b
mapK f (MkCatQueue init last) = MkCatQueue (mapK f init) (mapK f last)

public export
(++) : TCatQueue arr a b -> TCatQueue arr b c -> TCatQueue arr a c
MkCatQueue i1 l1 ++ MkCatQueue i2 l2 = MkCatQueue i1 (l1 <>< i2 ++ l2)

public export
uncons : TCatQueue arr a b -> Uncons TCatQueue arr a b
uncons (MkCatQueue (h :: t) last) = h :| MkCatQueue t last
uncons (MkCatQueue [] last) = case toList last of
  []       => Empty
  (h :: t) => h :| MkCatQueue t Lin

public export
unsnoc : TCatQueue arr a b -> Unsnoc TCatQueue arr a b
unsnoc (MkCatQueue init (x :< last)) = MkCatQueue init x :|< last
unsnoc (MkCatQueue init [<])         = case toSnocList init of
  [<]         => Empty
  (x :< last) => MkCatQueue Nil x :|< last
