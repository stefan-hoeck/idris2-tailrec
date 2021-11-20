module Control.Monad.Free

import Control.MonadRec
import Data.Fuel
import Data.TypeAligned

%default total

mutual
  public export
  record Free (f : Type -> Type) (a : Type) where
    constructor MkFree
    view : FreeView f t
    arrs : Arrs f t a

  public export
  data FreeView : (f : Type -> Type) -> (a : Type) -> Type where
    Pure : (val : a) -> FreeView f a
    Bind : (f b) -> (b -> Free f a) -> FreeView f a

  public export
  0 Arr : (f : Type -> Type) -> (a,b : Type) -> Type
  Arr f a b = a -> Free f b

  public export
  0 Arrs : (f : Type -> Type) -> (a,b : Type) -> Type
  Arrs = TCatList . Arr

export %inline
fromView : FreeView f a -> Free f a
fromView f = MkFree f empty

concatF : Free f a -> Arrs f a b -> Free f b
concatF (MkFree v r) l = MkFree v (r ++ l)

export
toView : Free f a -> FreeView f a
toView (MkFree v s) = case v of
  Pure val => case uncons s of
    Empty    => Pure val
    (h :| t) => assert_total $ toView (concatF (h val) t)

  Bind x k => Bind x (\va => concatF (k va) s)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

bind : Free f a -> (a -> Free f b) -> Free f b
bind (MkFree v r) g = MkFree v $ snoc r g

public export
Functor (Free f) where
  map g fr = bind fr (fromView . Pure . g)

public export
Applicative (Free f) where
  pure = fromView . Pure
  f <*> v = bind f (\f => map (f $) v)

public export %inline
Monad (Free f) where
  (>>=) = bind

public export
MonadRec (Free f) where
  tailRecM seed vst (Access rec) step = do
    Cont s2 prf vst2 <- step seed vst
      | Done v => pure v
    tailRecM s2 vst2 (rec s2 prf) step

export
lift : m a -> Free m a
lift ma = fromView (Bind ma pure)

export
HasIO m => HasIO (Free m) where
  liftIO = lift . liftIO

--------------------------------------------------------------------------------
--          Running Computations
--------------------------------------------------------------------------------

export
wrap : f (Free f a) -> Free f a
wrap x = fromView (Bind x id)

export
substFree : (forall x . f x -> Free g x) -> Free f a -> Free g a
substFree k = go
  where go : Free f y -> Free g y
        go f = case toView f of
          Pure a   => pure a
          Bind g i => assert_total $ k g >>= go . i

||| Unwraps a single layer of `f`, providing the continuation.
export
resume' :  (forall b. f b -> (b -> Free f a) -> r)
        -> (a -> r)
        -> Free f a
        -> r
resume' k j f = case toView f of
  Pure a   => j a
  Bind g i => k g i

||| Unwraps a single layer of the functor `f`.
export
resume : Functor f => Free f a -> Either (f (Free f a)) a
resume = resume' (\g,i => Left (i <$> g)) Right

export
mapK : (f : forall t . m t -> n t) -> Free m a -> Free n a
mapK f = substFree (lift . f)

export
fold : MonadRec m => (forall x . f x -> m x) -> Free f a -> m a
fold k fr = assert_total $ trSized forever fr $ \fu,frm => case fu of
  More x => case toView frm of
    Pure val => Done <$> pure val
    Bind g i => Cont x (reflexive {rel = LTE}) . i <$> k g
  Dry    => idris_crash "Control.Monad.Free.foldFree: ran out of fuel"

export
run : Functor f => (f (Free f a) -> Free f a) -> Free f a -> a
run k = go
  where go : Free f a -> a
        go f = case toView f of
          Pure a   => a
          Bind g i => assert_total $ go (k (i <$> g))

export
runM : Functor m => MonadRec n =>
       (m (Free m a) -> n (Free m a)) -> Free m a -> n a
runM g free = assert_total $ trSized forever free $ \fu,fr => case fu of
  More x => case resume fr of
    Right va => pure (Done va)
    Left  ma => Cont x (reflexive {rel = LTE}) <$> g ma
  Dry    => idris_crash "Control.Monad.Free.runM: ran out of fuel"
