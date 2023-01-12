module Control.MonadRec

import public Control.WellFounded
import Control.Monad.Either
import Control.Monad.Identity
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

import Data.List
import Data.SnocList
import public Data.Fuel
import public Data.Nat

%default total

--------------------------------------------------------------------------------
--          Sized Implementations
--------------------------------------------------------------------------------

public export
Sized Fuel where
  size Dry      = 0
  size (More f) = S $ size f

public export
Sized (SnocList a) where
  size = length

--------------------------------------------------------------------------------
--          Step
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
data Step :  (rel   : a -> a -> Type)
          -> (seed  : a)
          -> (accum : Type)
          -> (res   : Type)
          -> Type where

  ||| Keep iterating with a new `seed2`, which is
  ||| related to the current `seed` via `rel`.
  ||| `vst` is the accumulated state of the iteration.
  Cont :  (seed2 : a)
       -> (0 prf : rel seed2 seed)
       -> (vst   : st)
       -> Step rel seed st res

  ||| Stop iterating and return the given result.
  Done : (vres : res) -> Step rel v st res

public export
Bifunctor (Step rel seed) where
  bimap f _ (Cont s2 prf st) = Cont s2 prf (f st)
  bimap _ g (Done res)       = Done (g res)

  mapFst f (Cont s2 prf st) = Cont s2 prf (f st)
  mapFst _ (Done res)       = Done res

  mapSnd _ (Cont s2 prf st) = Cont s2 prf st
  mapSnd g (Done res)       = Done (g res)

--------------------------------------------------------------------------------
--          MonadRec
--------------------------------------------------------------------------------

||| Interface for tail-call optimized monadic recursion.
public export
interface Monad m => MonadRec m where
  ||| Implementers must make sure they implement this function
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
           -> (seed  : a)
           -> (0 prf : Accessible rel seed)
           -> (ini   : st)
           -> (step  : (seed2 : a) -> st -> m (Step rel seed2 st b))
           -> m b

public export %inline
||| Monadic tail recursion over a sized structure.
trSized :  MonadRec m
        => (0 _ : Sized a)
        => (seed : a)
        -> (ini  : st)
        -> (step : (v : a) -> st -> m (Step Smaller v st b))
        -> m b
trSized x ini = tailRecM x (sizeAccessible x) ini

||| This is NOT a tail-recursive implementation, allowing any monad be used
||| with the same API as if it is tail-recursive. Avoid using it at all costs!
export
[NonStackSafe] Monad m => MonadRec m where
  tailRecM seed (Access acc) init step = step seed init >>= \case
    Cont seed2 prf vst => tailRecM seed2 (acc seed2 prf) vst step
    Done vres          => pure vres

--------------------------------------------------------------------------------
--          Base Implementations
--------------------------------------------------------------------------------

public export
MonadRec Identity where
  tailRecM seed (Access rec) st1 f = case f seed st1 of
    Id (Done b)         => Id b
    Id (Cont y prf st2) => tailRecM y (rec y prf) st2 f

public export
MonadRec Maybe where
  tailRecM seed (Access rec) st1 f = case f seed st1 of
    Nothing               => Nothing
    Just (Done b)         => Just b
    Just (Cont y prf st2) => tailRecM y (rec y prf) st2 f

public export
MonadRec (Either e) where
  tailRecM seed (Access rec) st1 f = case f seed st1 of
    Left e                 => Left e
    Right (Done b)         => Right b
    Right (Cont y prf st2) => tailRecM y (rec y prf) st2 f

trIO :  (x : a)
     -> (0 _ : Accessible rel x)
     -> (ini : st)
     -> (f : (v : a) -> st -> IO (Step rel v st b))
     -> IO b
trIO x acc ini f = fromPrim $ run x acc ini
  where run :  (y : a)
            -> (0 _ : Accessible rel y)
            -> (st1 : st)
            -> (1 w : %World)
            -> IORes b
        run y (Access rec) st1 w = case toPrim (f y st1) w of
          MkIORes (Done b) w2          => MkIORes b w2
          MkIORes (Cont y2 prf st2) w2 => run y2 (rec y2 prf) st2 w2

public export %inline
MonadRec IO where
  tailRecM = trIO

--------------------------------------------------------------------------------
--          Transformer Implementations
--------------------------------------------------------------------------------

---------------------------
-- StateT

%inline
convST :  Functor m
       => (f : (v : a) -> st -> StateT s m (Step rel v st b))
       -> (v : a)
       -> (st,s)
       -> m (Step rel v (st,s) (s,b))
convST f v (st1,s1) =   (\(s2,stp) => bimap (,s2) (s2,) stp)
                    <$> runStateT s1 (f v st1)

public export
MonadRec m => MonadRec (StateT s m) where
  tailRecM x acc ini f =
    ST $ \s1 => tailRecM x acc (ini,s1) (convST f)

---------------------------
-- EitherT

convE :  Functor m
      => (f : (v : a) -> st -> EitherT e m (Step rel v st b))
      -> (v : a)
      -> (ini : st)
      -> m (Step rel v st (Either e b))
convE f v s1 = map conv $ runEitherT (f v s1)
  where conv : Either e (Step rel v st b) -> Step rel v st (Either e b)
        conv (Left err)                = Done (Left err)
        conv (Right $ Done b)          = Done (Right b)
        conv (Right $ Cont v2 prf st2) = Cont v2 prf st2

public export
MonadRec m => MonadRec (EitherT e m) where
  tailRecM x acc ini f =
    MkEitherT $ tailRecM x acc ini (convE f)

---------------------------
-- MaybeT

convM :  Functor m
      => (f : (v : a) -> st -> MaybeT m (Step rel v st b))
      -> (v : a)
      -> (ini : st)
      -> m (Step rel v st (Maybe b))
convM f v s1 = map conv $ runMaybeT (f v s1)
  where conv : Maybe (Step rel v st b) -> Step rel v st (Maybe b)
        conv Nothing                  = Done Nothing
        conv (Just $ Done b)          = Done (Just b)
        conv (Just $ Cont v2 prf st2) = Cont v2 prf st2

public export
MonadRec m => MonadRec (MaybeT m) where
  tailRecM x acc ini f =
    MkMaybeT $ tailRecM x acc ini (convM f)

---------------------------
-- ReaderT

convR :  (f : (v : a) -> st -> ReaderT e m (Step rel v st b))
      -> (env : e)
      -> (v : a)
      -> (ini : st)
      -> m (Step rel v st b)
convR f env v s1 = runReaderT env (f v s1)

public export
MonadRec m => MonadRec (ReaderT e m) where
  tailRecM x acc ini f =
    MkReaderT $ \env => tailRecM x acc ini (convR f env)

---------------------------
-- WriterT

convW :  Functor m
      => (f : (v : a) -> st -> WriterT w m (Step rel v st b))
      -> (v : a)
      -> (st,w)
      -> m (Step rel v (st,w) (b,w))
convW f v (s1,w1) =   (\(stp,w2) => bimap (,w2) (,w2) stp)
                  <$> unWriterT (f v s1) w1

public export
MonadRec m => MonadRec (WriterT w m) where
  tailRecM x acc ini f =
    MkWriterT $ \w1 => tailRecM x acc (ini,w1) (convW f)

---------------------------
-- RWST

convRWS :  Functor m
        => (f : (v : a) -> st -> RWST r w s m (Step rel v st b))
        -> (env : r)
        -> (v : a)
        -> (st,s,w)
        -> m (Step rel v (st,s,w) (b,s,w))
convRWS f env v (st1,s1,w1) =   (\(stp,s2,w2) => bimap (,s2,w2) (,s2,w2) stp)
                            <$> unRWST (f v st1) env s1 w1

public export
MonadRec m => MonadRec (RWST r w s m) where
  tailRecM x acc ini f =
    MkRWST $ \r1,s1,w1 => tailRecM x acc (ini,s1,w1) (convRWS f r1)
