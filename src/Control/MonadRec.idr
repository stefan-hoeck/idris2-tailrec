module Control.MonadRec

import Control.WellFounded
import Control.Monad.Either
import Control.Monad.Identity
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

import Data.List
import Data.Nat

%default total

--------------------------------------------------------------------------------
--          MonadRec
--------------------------------------------------------------------------------

||| Single step in a recursive computation. 
|||
||| A `Step` is either `Done`, in which case we return the
||| final result, or `Cont`, in which case we continue
||| iterating. In case of a `Cont`, we get a new seed for
||| the next iteration plus an updated state. In addition
||| we proof that the sequence of seeds is related via `rel`.
||| If `rel` is well-founded, the recursion will provably
||| come to an end in a finite number of steps.
public export
data Step :  (accum : Type)
          -> (res   : Type)
          -> (rel   : a -> a -> Type)
          -> (seed  : a) -> Type where

  ||| Keep iterating with a new `seed2`, which is
  ||| related to the current `seed` via `rel`.
  ||| `vst` is the accumulated state of the iteration.
  Cont :  (seed2 : a)
       -> (vst   : st)
       -> (0 prf : rel seed2 seed)
       -> Step st res rel seed

  ||| Stop iterating and return the given result.
  Done : (vres : res) -> Step st res rel v

||| Interface for tail-call optimized monadic recursion.
public export
interface Monad m => TailRecM m where
  ||| Implementers mus make sure they implement this function
  ||| in a tail recursive manner.
  ||| The general idea is to loop using the given `step` function
  ||| until it returns a `Done`.
  |||
  ||| To convey to the totality checker that the sequence
  ||| of seeds generated during recursion must come to an
  ||| end after a finite number of steps, this function
  ||| requires an erased proof of accessibility.
  total
  tailRecM :  {0 rel : a -> a -> Type}
           -> (step  : (seed2 : a) -> st -> m (Step st b rel seed2))
           -> (seed  : a)
           -> (ini   : st)
           -> (0 prf : Accessible rel seed)
           -> m b

public export %inline
||| Monadic tail recursion over a sized structure.
trSized :  TailRecM m
        => (0 _ : Sized a)
        => (step : (v : a) -> st -> m (Step st b Smaller v))
        -> (seed : a)
        -> (ini  : st)
        -> m b
trSized f x ini = tailRecM f x ini (sizeAccessible x)

--------------------------------------------------------------------------------
--          Base Implementations
--------------------------------------------------------------------------------

public export
TailRecM Identity where
  tailRecM f seed st1 (Access rec) = case f seed st1 of
    Id (Done b)         => Id b
    Id (Cont y st2 prf) => tailRecM f y st2 (rec y prf)

public export
TailRecM Maybe where
  tailRecM f seed st1 (Access rec) = case f seed st1 of
    Nothing               => Nothing
    Just (Done b)         => Just b
    Just (Cont y st2 prf) => tailRecM f y st2 (rec y prf)

public export
TailRecM (Either e) where
  tailRecM f seed st1 (Access rec) = case f seed st1 of
    Left e                 => Left e
    Right (Done b)         => Right b
    Right (Cont y st2 prf) => tailRecM f y st2 (rec y prf)

trIO :  (f : (v : a) -> st -> IO (Step st b rel v))
     -> (x : a)
     -> (ini : st)
     -> (0 _ : Accessible rel x)
     -> IO b
trIO f x ini acc = fromPrim $ run x ini acc
  where run :  (y : a) -> (st1 : st)
            -> (0 _ : Accessible rel y)
            -> (1 w : %World)
            -> IORes b
        run y st1 (Access rec) w = case toPrim (f y st1) w of
          MkIORes (Done b) w2          => MkIORes b w2
          MkIORes (Cont y2 st2 prf) w2 => run y2 st2 (rec y2 prf) w2

public export %inline
TailRecM IO where
  tailRecM = trIO

--------------------------------------------------------------------------------
--          Transformer Implementations
--------------------------------------------------------------------------------

---------------------------
-- StateT

convST :  Functor m
       => (f : (v : a) -> st -> StateT s m (Step st b rel v))
       -> (v : a)
       -> (st,s)
       -> m (Step (st,s) (s,b) rel v)
convST f v (st1,s1) = map conv $ runStateT s1 (f v st1)
  where conv : (s, Step st b rel v) -> Step (st,s) (s,b) rel v
        conv (s2,Done res)        = Done (s2, res)
        conv (s2,Cont v2 st2 prf) = Cont v2 (st2,s2) prf

public export
TailRecM m => TailRecM (StateT s m) where
  tailRecM f x ini acc =
    ST $ \s1 => tailRecM (convST f) x (ini,s1) acc

---------------------------
-- EitherT

convE :  Functor m
      => (f : (v : a) -> st -> EitherT e m (Step st b rel v))
      -> (v : a)
      -> (ini : st)
      -> m (Step st (Either e b) rel v)
convE f v s1 = map conv $ runEitherT (f v s1)
  where conv : Either e (Step st b rel v) -> Step st (Either e b) rel v
        conv (Left err)                = Done (Left err)
        conv (Right $ Done b)          = Done (Right b)
        conv (Right $ Cont v2 st2 prf) = Cont v2 st2 prf

public export
TailRecM m => TailRecM (EitherT e m) where
  tailRecM f x ini acc =
    MkEitherT $ tailRecM (convE f) x ini acc

---------------------------
-- MaybeT

convM :  Functor m
      => (f : (v : a) -> st -> MaybeT m (Step st b rel v))
      -> (v : a)
      -> (ini : st)
      -> m (Step st (Maybe b) rel v)
convM f v s1 = map conv $ runMaybeT (f v s1)
  where conv : Maybe (Step st b rel v) -> Step st (Maybe b) rel v
        conv Nothing                   = Done Nothing
        conv (Just $ Done b)          = Done (Just b)
        conv (Just $ Cont v2 st2 prf) = Cont v2 st2 prf

public export
TailRecM m => TailRecM (MaybeT m) where
  tailRecM f x ini acc =
    MkMaybeT $ tailRecM (convM f) x ini acc

---------------------------
-- ReaderT

convR :  (f : (v : a) -> st -> ReaderT e m (Step st b rel v))
      -> (env : e)
      -> (v : a)
      -> (ini : st)
      -> m (Step st b rel v)
convR f env v s1 = runReaderT env (f v s1)

public export
TailRecM m => TailRecM (ReaderT e m) where
  tailRecM f x ini acc =
    MkReaderT $ \env => tailRecM (convR f env) x ini acc

---------------------------
-- WriterT

convW :  Functor m
      => (f : (v : a) -> st -> WriterT w m (Step st b rel v))
      -> (v : a)
      -> (st,w)
      -> m (Step (st,w) (b,w) rel v)
convW f v (s1,w1) = conv <$> unWriterT (f v s1) w1
  where conv : (Step st b rel v, w) -> Step (st,w) (b,w) rel v
        conv (Done res, w2)        = Done (res, w2)
        conv (Cont v2 st2 prf, w2) = Cont v2 (st2,w2) prf

public export
TailRecM m => TailRecM (WriterT w m) where
  tailRecM f x ini acc =
    MkWriterT $ \w1 => tailRecM (convW f) x (ini,w1) acc

---------------------------
-- RWST

convRWS :  Functor m
        => (f : (v : a) -> st -> RWST r w s m (Step st b rel v))
        -> (env : r)
        -> (v : a)
        -> (st,s,w)
        -> m (Step (st,s,w) (b,s,w) rel v)
convRWS f env v (st1,s1,w1) = conv <$> unRWST (f v st1) env s1 w1
  where conv : (Step st b rel v, s, w) -> Step (st,s,w) (b,s,w) rel v
        conv (Done res, s2,w2)     = Done (res, s2, w2)
        conv (Cont v2 st2 prf, s2, w2) = Cont v2 (st2,s2,w2) prf

public export
TailRecM m => TailRecM (RWST r w s m) where
  tailRecM f x ini acc =
    MkRWST $ \r1,s1,w1 => tailRecM (convRWS f r1) x (ini,s1,w1) acc
