module Control.Monad.Free

import Control.MonadRec
import Data.Fuel
import Data.TypeAligned

%default total

public export
0 Bind : (m : Type -> Type) -> (a,b : Type) -> Type

public export
0 BindList : (m : Type -> Type) -> (a,b : Type) -> Type

public export
data Free : (m : Type -> Type) -> (a : Type) -> Type where
  Pure    : (val : a) -> Free m a
  Impure  : (ma  : m a) -> (q : BindList m a b) -> Free m b

Bind m a b = a -> Free m b

BindList = TCatList . Bind

export
lift : m a -> Free m a
lift ma = Impure ma CatNil

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

bind : Free m a -> (a -> Free m b) -> Free m b
bind (Pure val)    f = f val
bind (Impure ma q) f = Impure ma $ snoc q f

public export
Functor (Free m) where
  map f (Pure val)    = Pure $ f val
  map f (Impure ma q) = Impure ma $ snoc q (Pure . f)

public export
Applicative (Free m) where
  pure = Pure
  f <*> v = bind f (\f => map (f $) v)

public export %inline
Monad (Free m) where
  (>>=) = bind

public export
MonadRec (Free m) where
  tailRecM seed vst (Access rec) step = do
    Cont s2 prf vst2 <- step seed vst
      | Done v => pure v
    tailRecM s2 vst2 (rec s2 prf) step

export
HasIO m => HasIO (Free m) where
  liftIO = lift . liftIO

--------------------------------------------------------------------------------
--          Running Computations
--------------------------------------------------------------------------------

export
qApp : BindList m a b -> a -> Free m b
qApp q va = case uncons q of
  Empty    => Pure va
  (f :| r) => case f va of
     Pure val     => qApp (assert_smaller q r) val
     Impure ma q2 => Impure ma $ q2 ++ r

export
resume : Functor m => Free m a -> Either (m $ Free m a) a
resume (Pure val)    = Right val
resume (Impure ma q) = Left $ map (qApp q) ma

export
substFree : (forall x . m x -> Free  n x) -> Free m a -> Free n a
substFree _ (Pure val)    = Pure val
substFree f (Impure ma q) = assert_total $ f ma >>= (substFree f . qApp q)

export
mapK : (f : forall t . m t -> n t) -> Free m a -> Free n a
mapK f = substFree (lift . f)

export
goWhile :  Functor m
        => Fuel
        -> (m (Free m a) -> Free m a)
        -> Free m a
        -> Either (Free m a) a
goWhile fuel extract free = go fuel free
  where go : Fuel -> Free m a -> Either (Free m a) a
        go Dry y = Left y
        go (More x) y = case resume y of
          Right v => Right v
          Left y2 => go x (extract y2)

export
runM :  Functor m
     => MonadRec n
     => Fuel
     -> (m (Free m a) -> n (Free m a))
     -> Free m a
     -> n (Either (Free m a) a)
runM fuel g free = trSized fuel free $ \fu,fr => case fu of
  Dry    => pure (Done $ Left fr)
  More x => case resume fr of
    Right va => pure (Done $ Right va)
    Left  ma => Cont x (reflexive {rel = LTE}) <$> g ma

export
foldWhile :  MonadRec n
          => Fuel
          -> (forall x . m x -> n x)
          -> Free m a
          -> n (Either (Free n a) a)
foldWhile fuel f free = runM fuel id (mapK f free)
