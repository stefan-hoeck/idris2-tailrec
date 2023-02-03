# idris2-tailrec : Total stack-safe monadic Recursion in Idris2

Writing recursive functions that do not overflow the stack
can be challenging. The JavaScript backends in Idris2
optimize mutually tail-recursive
functions into while loops, which makes them use constant stack space.
Chez scheme, the target of the default backend
performs tail-call optimization on its own.
In monadic code, however, the recursive call happens within
the bind operator `(>>=)`, and is therefore not
in tail position. The following program, for instance,
will overflow the stack on the Node backend (this README
is a literate Idris2 file, and the module imports will be
needed later on):

```idris
import Control.WellFounded
import Data.Nat

count : Nat -> IO ()
count Z     = putStrLn "Done"
count (S k) = do
  putStrLn #"Next is \#{show k}"#
  count k

main : IO ()
main = count 10000000
```

Other languages like PureScript or Scala
solve this by introducing a new type class
(see the [purescript-tailrec](https://github.com/purescript/purescript-tailrec)
library) or by adding support for stack safe recursion
directly to their monad interface
(see the [cats](https://github.com/typelevel/cats) library).
The solution is very similar in both cases. In the code
below, we look at how *purescript-tailrec* does it
(they use a dedicated `Step` type instead of `Either`
but the result is the same):

```idris
interface Monad m => MonadRec1 m where
  tailRecM1 : (step : a -> m (Either a b)) -> a -> m b

count2 : HasIO io => MonadRec1 io => Nat -> io ()
count2 = tailRecM1 go
  where go : Nat -> io (Either Nat ())
        go Z     = putStrLn "Done" $> Right ()
        go (S k) = putStrLn #"Next is \#{show k}"# $> Left k
```

Implementers of `MonadRec1` must make sure to write `tailRecM`
in a tail recursive manner. If they do so, `count2` will use constant
stack space. Problem solved.

Well, in PureScript and Scala, yes, but not so in Idris.
Let's implement `MonadRec1` for `Maybe`:

```idris
MonadRec1 Maybe where
  tailRecM1 f a = case f a of
    Nothing        => Nothing
    Just (Right b) => Just b
    Just (Left a)  => tailRecM1 f a
```

This will not be accepted by the totality checker
and for good reasons. The following program will loop
forever:

```idris
forever : Maybe Nat
forever = tailRecM1 go ()
  where go : () -> Maybe (Either () Nat)
        go () = Just $ Left ()
```

What we are lacking is a way to convince Idris, that the
values of type `a` are getting smaller in every recursive
step, and that's the core contribution of this library:
We enhance `tailRecM1` with such a proof, thus rendering
implementations provably total. While this will lead
to slightly more complex types and some manual proof
passing, the result is well worth it: We get total
stack-safe monadic recursion!

## Well-founded Relations

The first thing to do is to enhance the passed `step` function with
a dependent type:

```idris
||| Step function with a proof that in case of a continuation
||| returning `v2`, `rel v2 v` holds. We can use this as part of a proof
||| that the seed for the next iterations is getting strictly smaller.
data Step : (st, res : Type) -> (rel : a -> a -> Type) -> (v : a) -> Type where
  Cont : (v2 : a) -> (state : st) -> (0 prf : rel v2 v) -> Step st res rel v
  Done : (result : res) -> Step st res rel v
```

I will explain below, why there is an additional accumulator of type `st`.
A concrete instance might look as follows:
We use an internal state of type `List Bool`, a result type `String`,
and we iterate over `Nat`. In the following example
we guarantee, that in case of a `Cont`, the next natural number will
be less than `10`.

```idris
NatStep : Step (List Bool) String LT 10
NatStep = Cont 0 [] (LTESucc LTEZero)
```
Interface `MonadRec` together with an implementation for
`Maybe` would now look like so:

```idris
interface Monad m => MonadRec2 m where
  tailRecM2 :  (seed : a)
            -> (initialState : st)
            -> (step : (seed : a) -> st -> m (Step st b rel seed))
            -> m b

MonadRec2 Maybe where
  tailRecM2 seed ini f = case f seed ini of
    Nothing              => Nothing
    Just (Done b)        => Just b
    Just (Cont s2 st2 _) => tailRecM2 s2 st2 f
```

The interesting part is the `step` function we pass to `tailRecM2`.
Its type can be interpreted as follows: For every value `seed`, I tell
you what to do in the next recursive step, and in case we are not yet done,
I'll give you a new seed (let's call it `seed2` here),
so that `rel seed2 seed` holds. For
instance, if `rel` is `LT` for natural numbers, `seed2` will be a new
natural number strictly smaller than `seed`.

However, this will (of course) still not convince the
totality checker and rightfully so:

```idris
forever2 : Maybe Nat
forever2 = tailRecM2 () () go
  where go : (seed : ()) -> () -> Maybe (Step () Nat Equal seed)
        go () () = Just $ Cont () () Refl
```

There is one piece still missing: A proof that our `seed` values
will eventually come to an end, and hence, function `step` *must*
eventually return a `Done`. This doesn't work, when `Equal`
is our relation, as the seed can stay forever the same.
What we are looking for are
[*well-founded* relations](https://en.wikipedia.org/wiki/Well-founded_relation).
There are several definitions for this, but for us, the most important
one is the following: Assume `<` is a relation over type `A`.
Given a starting value `a0` of type `A`, we want to make sure that
every sequence `a0, a1, a2, ..., an, ...`
with `... < an < ... < a2 < a1 < a0` is finite. If this holds for `a0`,
we say that `a0` is *accessible* with respect to `<`.
If all values of type `A` are accessible w.r.t. `<`, `<` is
called *well-founded* on `A`.

There is module `Control.WellFounded`, providing us with the
ingredients for this. We will now do two things: First, we
use a proof of accessibility to write a total implementation
of `tailRecM` that is accepted by Idris, second, we construct
some values of type `Accessible` manually to get a feel for
how this works. Note: Our proofs of accessibility
will be erased at runtime,
so we need not care if they are constructed in a tail recursive
manner or not.

```idris
interface Monad m => MonadRec m where
  total
  tailRecM :  (seed : a)
           -> (0 acc : Accessible rel seed)
           -> (initialState : st)
           -> (step : (seed : a) -> st -> m (Step st b rel seed))
           -> m b

MonadRec Maybe where
  tailRecM seed (Access rec) ini f = case f seed ini of
    Nothing                => Nothing
    Just (Done b)          => Just b
    Just (Cont s2 st2 rel) => tailRecM s2 (rec s2 rel) st2 f
```

That was not too hard. The only constructor of `Accessible rel v1` provides
a function returning a new `Accessible rel v2` for all values `v2`,
for which `rel v2 v1` holds.

But can we be sure about this? Let's come up with some values
of type `Accessible`. First, the correct case with `Nat` and `LT`:

```idris
total
natAcc : (n : Nat) -> Accessible LT n
natAcc n = Access (acc n)
  where acc : (u : Nat) -> (v : Nat) -> (prf : v `LT` u) -> Accessible LT v
        acc (S u') v (LTESucc vLTEu') =
          Access $ \w, wLTv => acc u' w (transitive {rel = LTE} wLTv vLTEu')
        acc Z _ _ impossible
```

As you can see, the base case is `impossible`: There is no
natural number strictly smaller than zero. This will always
be the case if we come up with a value of type `Accessible`, the
creation of which satisfies the totality checker.
In the recursive case, we have `v < u`, hence `S v <= u`, hence `S v <= S u'`
hence `v <= u'`, which is the type of `vLTEu'`.
But if we now get a `w` with
`w < v`, and therefore `S w <= v`, then `S w <= u'` by the law of
transitivity, and we can recursively invoke `acc` with `u'`, a value strictly
smaller than `u`.
Idris is totally happy with this. Not so, with the following:

```idris
strAcc : (s : String) -> Accessible Equal s
strAcc s = Access (acc s)
  where
    acc : (u : String) -> (v : String) -> (prf : v = u) -> Accessible Equal v
    acc u v vEQu =
      Access $ \w,wEQv => acc u w (trans wEQv vEQu)
```

If we annotate the above with `total`, Idris will rightfully shout
at us.

## Why `st` then?

When I was experimenting with this for the first time,
I found that during recursion we often need some form of
accumulator, and, contrary to the data structure or
value, over which we iterate, the accumulator typically
gets larger instead of smaller. We could of course just
pair the accumulator with the seed value and use
the well-founded relation on the first (or second) value
of the resulting pair. While this works perfectly fine, I
felt it to be rather more cumbersome than necessary, so
I added an additional state argument to `Cont` and
`tailRecM`, which we can use as an internal accumulator.
