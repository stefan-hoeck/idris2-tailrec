module Data.TypeAligned.List

import Data.TypeAligned.Ops
import Data.TypeAligned.Uncons
import Data.TypeAligned.Unsnoc

%default total

public export
data TList : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  Nil  : TList arr a a
  (::) : (h : arr a b) -> (t : TList arr b c) -> TList arr a c

public export
data TSnocList : (arr : Type -> Type -> Type) -> (a,b : Type) -> Type where
  Lin  : TSnocList arr a a
  (:<) : (init : TSnocList arr a b) -> (last : arr b c) -> TSnocList arr a c

public export
(<><) : TSnocList arr a b -> TList arr b c -> TSnocList arr a c
sx <>< []       = sx
sx <>< (h :: t) = sx :< h <>< t

public export
(<>>) : TSnocList arr a b -> TList arr b c -> TList arr a c
[<]            <>> l = l
(init :< last) <>> l = init <>> last :: l

public export %inline
toSnocList : TList arr a b -> TSnocList arr a b
toSnocList = (Lin <><)

public export %inline
toList : TSnocList arr a b -> TList arr a b
toList = (<>> Nil)

namespace TList
  public export %inline
  singleton : arr a b -> TList arr a b
  singleton f = [f]

  public export
  uncons : TList arr a b -> Uncons TList arr a b
  uncons []       = Empty
  uncons (h :: t) = h :| t

  public export
  unsnoc : TList arr a b -> Unsnoc TList arr a b
  unsnoc xs = case toSnocList xs of
    Lin    => Empty
    i :< l => toList i :|< l

  public export
  (++) : TList arr a b -> TList arr b c -> TList arr a c
  xs ++ ys = toSnocList xs <>> ys

  public export
  snoc : TList arr a b -> arr b c -> TList arr a c
  snoc xs f = xs ++ [f]

  public export
  mapK : (forall u,v . r1 u v -> r2 u v) -> TList r1 a b -> TList r2 a b
  mapK f = go Lin
    where go : TSnocList r2 x y -> TList r1 y z -> TList r2 x z
          go sl []       = toList sl
          go sl (h :: t) = go (sl :< f h) t

namespace TSnocList
  public export %inline
  singleton : arr a b -> TSnocList arr a b
  singleton f = Lin :< f

  public export
  uncons : TSnocList arr a b -> Uncons TSnocList arr a b
  uncons sx = case uncons (toList sx) of
    Empty  => Empty
    h :| t => h :| toSnocList t


  public export
  unsnoc : TSnocList arr a b -> Unsnoc TSnocList arr a b
  unsnoc [<]            = Empty
  unsnoc (init :< last) = init :|< last

  public export
  mapK : (forall u,v . r1 u v -> r2 u v) -> TSnocList r1 a b -> TSnocList r2 a b
  mapK f = go Nil
    where go : TList r2 y z -> TSnocList r1 x y -> TSnocList r2 x z
          go l [<]            = toSnocList l
          go l (init :< last) = go (f last :: l) init

  public export
  (++) : TSnocList arr a b -> TSnocList arr b c -> TSnocList arr a c
  sx ++ sy = sx <>< toList sy

  public export
  cons : arr a b -> TSnocList arr b c -> TSnocList arr a c
  cons f sx = [<f] ++ sx
