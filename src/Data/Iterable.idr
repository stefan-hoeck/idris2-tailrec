module Data.Iterable

import Data.List1
import Data.SnocList

import public Control.MonadRec

--------------------------------------------------------------------------------
--          Iterable
--------------------------------------------------------------------------------

refl : {k : Nat} -> LTE k k
refl = reflexive {x = k}

public export
interface Iterable container element | container where
  iterM :  MonadRec m
        => (accum : element -> st -> m st)
        -> (done  : st -> res)
        -> (ini   : st)
        -> (seed  : container)
        -> m res

export
forM_ :  Iterable container element
      => MonadRec m
      => (run  : element -> m ())
      -> (seed : container)
      -> m ()
forM_ run = iterM (\e,_ => run e) (const ()) ()

export
foldM :  Iterable container element
      => MonadRec m
      => Monoid mo
      => (calc : element -> m mo)
      -> (seed : container)
      -> m mo
foldM calc = iterM (\e,acc => (<+> acc) <$> calc e) id neutral

--------------------------------------------------------------------------------
--          Iterable Implementations
--------------------------------------------------------------------------------

export
Iterable Nat Nat where
  iterM accum done ini seed =
    trSized go seed ini
    where go : (n : Nat) -> st -> m (Step Smaller n st res)
          go Z st       = pure . Done $ done st
          go v@(S k) st = Cont k refl <$> accum v st

export
Iterable (List a) a where
  iterM accum done ini seed =
    trSized go seed ini
    where go : (as : List a) -> st -> m (Step Smaller as st res)
          go Nil st      = pure . Done $ done st
          go (h :: t) st = Cont t refl <$> accum h st

export
Iterable (List1 a) a where
  iterM accum done ini = iterM accum done ini . forget

export
Iterable Fuel () where
  iterM accum done ini seed =
    trSized go seed ini
    where go : (f : Fuel) -> st -> m (Step Smaller f st res)
          go Dry st      = pure . Done $ done st
          go (More f) st = Cont f refl <$> accum () st

export
Iterable (SnocList a) a where
  iterM accum done ini seed =
    trSized go seed ini
    where go : (as : SnocList a) -> st -> m (Step Smaller as st res)
          go [<]       st = pure . Done $ done st
          go (sx :< x) st = Cont sx refl <$> accum x st
