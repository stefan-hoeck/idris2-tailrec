module Data.List.TR

import Data.Iterable
import Data.List
import Control.MonadRec
import Control.Monad.Identity

export
replicateM : MonadRec m => Nat -> m a -> m (List a)
replicateM n ma = iterM (\_,as => (:: as) <$> ma) id Nil n

export
iterateM : MonadRec m => Nat -> (a -> m a) -> a -> m (List a)
iterateM n f ini = iterM next snd (ini,Nil) n
  where next : Nat -> (a,List a) -> m (a,List a)

export
replicateTR : Nat -> a -> List a
replicateTR n va = run Nil n
  where run : List a -> Nat -> List a
        run xs 0     = xs
        run xs (S k) = run (va :: xs) k

export
iterateTR : Nat -> (a -> a) -> a -> List a
iterateTR n f = run Nil n
  where run : List a -> Nat -> a -> List a
        run xs 0     _  = reverse xs
        run xs (S k) va = run (va :: xs) k (f va)

export
mapTR : (a -> b) -> List a -> List b
mapTR f = run Nil
  where run : List b -> List a -> List b
        run bs []       = reverse bs
        run bs (h :: t) = run (f h :: bs) t
