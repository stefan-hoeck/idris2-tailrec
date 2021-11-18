module Data.TypeAligned.Uncons

import Data.TypeAligned.Ops

%default total

public export
data Uncons :  (s : (Type -> Type -> Type) -> Type -> Type -> Type)
            -> (c : Type -> Type -> Type)
            -> (x : Type)
            -> (y : Type)
            -> Type where
   Empty : Uncons s c x x
   (:|)  : c x y -> s c y z -> Uncons s c x z
