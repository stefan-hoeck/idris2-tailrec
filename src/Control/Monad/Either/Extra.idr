module Control.Monad.Either.Extra

import public Control.Monad.Error.Either
import Data.Vect

%default total

--------------------------------------------------------------------------------
--          List Traversal
--------------------------------------------------------------------------------

implList_ : (t -> EitherT e IO ()) -> List t -> PrimIO (Either e ())
implList_ f []        w = MkIORes (Right ()) w
implList_ f (x :: xs) w =
  let MkIORes (Right ()) w2 := toPrim (runEitherT (f x)) w
        | MkIORes (Left err) w2 => MkIORes (Left err) w2
   in implList_ f xs w2

implList :
     SnocList a
  -> (t -> EitherT e IO a)
  -> List t
  -> PrimIO (Either e $ List a)
implList sa f []        w = MkIORes (Right $ sa <>> []) w
implList sa f (x :: xs) w =
  let MkIORes (Right v) w2 := toPrim (runEitherT (f x)) w
        | MkIORes (Left err) w2 => MkIORes (Left err) w2
   in implList (sa :< v) f xs w2

||| Specialized, stack-safe list traversal.
export
traverseList_ : (t -> EitherT e IO ()) -> List t -> EitherT e IO ()
traverseList_ f xs = MkEitherT $ fromPrim $ implList_ f xs

||| Specialized, stack-safe list traversal.
export
traverseList : (t -> EitherT e IO a) -> List t -> EitherT e IO (List a)
traverseList f xs = MkEitherT $ fromPrim $ implList [<] f xs

||| Specialized, stack-safe list traversal.
export %inline
forList_ : List t -> (t -> EitherT e IO ()) -> EitherT e IO ()
forList_ as f = traverseList_ f as

||| Specialized, stack-safe list traversal.
export %inline
forList : List t -> (t -> EitherT e IO a) -> EitherT e IO (List a)
forList as f = traverseList f as

--------------------------------------------------------------------------------
--          SnocList Traversal
--------------------------------------------------------------------------------

implSnocList_ : (t -> EitherT e IO ()) -> SnocList t -> PrimIO (Either e ())
implSnocList_ f [<]       w = MkIORes (Right ()) w
implSnocList_ f (sx :< x) w =
  let MkIORes (Right ()) w2 := toPrim (runEitherT (f x)) w
        | MkIORes (Left err) w2 => MkIORes (Left err) w2
   in implSnocList_ f sx w2

implSnocList :
     List a
  -> (t -> EitherT e IO a)
  -> SnocList t
  -> PrimIO (Either e $ SnocList a)
implSnocList as f [<]       w = MkIORes (Right $ [<] <>< as) w
implSnocList as f (sx :< x) w =
  let MkIORes (Right v) w2 := toPrim (runEitherT (f x)) w
        | MkIORes (Left err) w2 => MkIORes (Left err) w2
   in implSnocList (v::as) f sx w2

||| Specialized, stack-safe list traversal.
export
traverseSnocList_ : (t -> EitherT e IO ()) -> SnocList t -> EitherT e IO ()
traverseSnocList_ f sx = MkEitherT $ fromPrim $ implSnocList_ f sx

||| Specialized, stack-safe list traversal.
export
traverseSnocList : (t -> EitherT e IO a) -> SnocList t -> EitherT e IO (SnocList a)
traverseSnocList f sx = MkEitherT $ fromPrim $ implSnocList [] f sx

||| Specialized, stack-safe list traversal.
export %inline
forSnocList_ : SnocList t -> (t -> EitherT e IO ()) -> EitherT e IO ()
forSnocList_ sa f = traverseSnocList_ f sa

||| Specialized, stack-safe list traversal.
export %inline
forSnocList : SnocList t -> (t -> EitherT e IO a) -> EitherT e IO (SnocList a)
forSnocList sa f = traverseSnocList f sa
