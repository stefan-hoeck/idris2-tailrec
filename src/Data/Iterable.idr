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
  iterM :
       {auto rec : MonadRec m}
    -> (accum : element -> st -> m st)
    -> (done  : st -> res)
    -> (ini   : st)
    -> (seed  : container)
    -> m res

export
forM_ :
     {auto _ : Iterable container element}
  -> {auto _ : MonadRec m}
  -> (run  : element -> m ())
  -> (seed : container)
  -> m ()
forM_ run = iterM (\e,_ => run e) (const ()) ()

export
foldM :
     {auto _ : Iterable container element}
  -> {auto _ : MonadRec m}
  -> {auto _ : Monoid mo}
  -> (calc : element -> m mo)
  -> (seed : container)
  -> m mo
foldM calc = iterM (\e,acc => (<+> acc) <$> calc e) id neutral

--------------------------------------------------------------------------------
--          Iterable Implementations
--------------------------------------------------------------------------------

export
Iterable Nat Nat where
  iterM accum done ini seed =
    trSized seed ini $
      \case Z       => pure . Done . done
            v@(S k) => map (Cont k refl) . accum v

export
Iterable (List a) a where
  iterM accum done ini seed =
    trSized seed ini $
      \case Nil    => pure . Done . done
            h :: t => map (Cont t refl) . accum h

export
Iterable (List1 a) a where
  iterM accum done ini = iterM accum done ini . forget

export
Iterable Fuel () where
  iterM accum done ini seed =
    trSized seed ini $
      \case Dry    => pure . Done . done
            More f => map (Cont f refl) . accum ()

export
Iterable (SnocList a) a where
  iterM accum done ini seed =
    trSized seed ini $
      \case [<]     => pure . Done . done
            sx :< x => map (Cont sx refl) . accum x
