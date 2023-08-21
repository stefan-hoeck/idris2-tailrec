module Data.List.TR

import Data.Iterable
import Data.List
import Control.MonadRec
import Control.Monad.Identity

export
replicateM : MonadRec m => Nat -> m a -> m (List a)
replicateM n ma = iterM (\_,as => (:: as) <$> ma) id Nil n

export
replicateTR : Nat -> a -> List a
replicateTR n va = run Nil n

  where
    run : List a -> Nat -> List a
    run xs 0     = xs
    run xs (S k) = run (va :: xs) k

export
iterateTR : Nat -> (a -> a) -> a -> List a
iterateTR n f = run Nil n

  where
    run : List a -> Nat -> a -> List a
    run xs 0     _  = reverse xs
    run xs (S k) va = run (va :: xs) k (f va)
