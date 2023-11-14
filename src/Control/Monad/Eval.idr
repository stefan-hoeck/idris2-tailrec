||| The simplest stack-safe monadic evaluation
module Control.Monad.Eval

import Control.MonadRec

%default total

||| The simplest monad of stack-safe pure computations
|||
||| This is effectively an `Identity` monad with stack-safe implementations
||| of standard combinators.
|||
||| It can be used as a simplest transformation of a pure functional
||| non-stack-safe code to stack-safe one with minimal changes in code.
|||
||| For example, consider the tree data type example and ordinary
||| non-stack-safe implementation of `Functor` for it:
|||
||| ```idris
||| data Tree a = Leaf a | Node a (List1 (Tree a))
|||
||| Functor Tree where
|||   map f (Leaf x)    = Leaf $ f x
|||   map f (Node x xs) = Node (f x) $ map @{Compose} f xs
||| ```
|||
||| Using the `Eval` monad, you can turn it do a stack-safe one
|||
||| ```idris
||| Functor Tree where
|||   map f = eval . go where
|||     go : Tree a -> Eval $ Tree b
|||     go (Leaf x)    = pure $ Leaf $ f x
|||     go (Node x xs) = defer $ Node (f x) <$> traverse go xs
|||
||| ```
export
data Eval : Type -> Type where
  Pure : a -> Eval a
  Bind : Eval s -> (s -> Eval a) -> Eval a

export %inline
lazy : Lazy a -> Eval a
lazy x = Pure () `Bind` \() => Pure x

||| Suspends a lazy evaluation into the `Eval` monad
|||
||| This can be used to suspend the recursive calls, or the whole expressions
||| containing the recursive calls, in order to provide stack-safety
export %inline
defer : Lazy (Eval a) -> Eval a
defer x = Pure () `Bind` \() => x

export %inline
Functor Eval where
  map f e = Bind e $ Pure . f

export %inline
Applicative Eval where
  pure = Pure
  f <*> x = Bind f (<$> x)

export %inline
Monad Eval where
  (>>=) = Bind

-- This implementation is indeed tail-recursive because it solely calls
-- a constructor and the recursive call is suspended in a function
export
MonadRec Eval where
  tailRecM x (Access acc) s next = next x s `Bind` \case
    Done x      => Pure x
    Cont y r s' => tailRecM y (acc y r) s' next

export
eval : Eval a -> a
eval = assert_total go [] where

  data FnStack : Type -> Type -> Type where
    Nil  : forall a. FnStack a a
    (::) : forall a, b. (a -> Eval b) -> FnStack b c -> FnStack a c

  covering
  go : forall a, b. FnStack a b -> Eval a -> b
  go []      $ Pure x   = x
  go (f::fs) $ Pure x   = go fs $ f x
  go fs      $ Bind x f = go (f::fs) x
