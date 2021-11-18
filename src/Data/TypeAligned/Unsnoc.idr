module Data.TypeAligned.Unsnoc

import Data.TypeAligned.Ops

%default total

public export
data Unsnoc :  (s : (Type -> Type -> Type) -> Type -> Type -> Type)
            -> (c : Type -> Type -> Type)
            -> (x : Type)
            -> (y : Type)
            -> Type where
   Empty : Unsnoc s c x x
   (:|<) : s c x y -> c y z -> Unsnoc s c x z
