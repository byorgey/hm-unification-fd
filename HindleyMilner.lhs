---
title: "Implementing Hindley-Milner with the unification-fd library"
---

    [BLOpts]
    profile = wp
    postid = 2393
    publish = true
    tags = unification, Hindley-Milner, types, inference
    categories = Haskell, teaching

For a current project, I needed to implement type inference for a
[Hindley-Milner](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)-based
type system. (More about that project in an upcoming post!)  If you
don't know, Hindley-Milner is what you get when you add polymorphism
to the simply typed lambda calculus, but only allow $\forall$ to show
up at the very outermost layer of a type.  This is the fundamental
basis for many real-world type systems (*e.g.* OCaml or Haskell without
`RankNTypes` enabled).

One of the core operations in any Hindley-Milner type inference
algorithm is *unification*, where we take two types that might contain
*unification variables* (think "named holes") and try to make them
equal, which might fail, or might provide more information about the
values that the unification variables should take.  For example, if we
try to unify `a -> Int` and `Char -> b`, we will learn that `a = Char`
and `b = Int`; on the other hand, trying to unify `a -> Int` and `(b,
Char)` will fail, because there is no way to make those two types
equal (the first is a function type whereas the second is a pair).

I've implemented this from scratch before, and it was a great learning
experience, but I wasn't looking forward to implementing it again.
But then I remembered the [`unification-fd`
library](https://hackage.haskell.org/package/unification-fd) and
wondered whether I could use it to simplify the implementation.  Long
story short, although the documentation for `unification-fd` claims it
can be used to implement Hindley-Milner, I couldn't find any examples
online, and apparently [neither could anyone
else](https://github.com/wrengr/unification-fd/issues/17).  So I set
out to make my own example, and you're reading it.  It turns out that
`unification-fd` is incredibly powerful, but using it can be a bit
finicky, so I hope this example can be helpful to others who wish to
use it.  Along the way, resources I found especially helpful include
[this basic unification-fd
tutorial](https://winterkoninkje.dreamwidth.org/100478.html) by the
author, Wren Romano, as well as a [blog post by Roman
Cheplyaka](https://ro-che.info/articles/2017-06-17-generic-unification),
and the [unification-fd Haddock
documentation](https://hackage.haskell.org/package/unification-fd)
itself.  I also referred to the [Wikipedia page on
Hindley-Milner](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system),
which is extremely thorough.

This blog post is rendered automatically from a literate Haskell file;
you can [find the complete working source code and blog post on
GitHub](https://github.com/byorgey/hm-unification-fd).  I'm always
happy to receive comments, fixes, or suggestions for improvement.

Prelude: A Bunch of Extensions and Imports
------------------------------------------

We will make GHC and other people's libraries work very hard for us.
You know the drill.

> {-# LANGUAGE DeriveAnyClass        #-}
> {-# LANGUAGE DeriveFoldable        #-}
> {-# LANGUAGE DeriveFunctor         #-}
> {-# LANGUAGE DeriveGeneric         #-}
> {-# LANGUAGE DeriveTraversable     #-}
> {-# LANGUAGE FlexibleContexts      #-}
> {-# LANGUAGE FlexibleInstances     #-}
> {-# LANGUAGE GADTs                 #-}
> {-# LANGUAGE LambdaCase            #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE PatternSynonyms       #-}
> {-# LANGUAGE StandaloneDeriving    #-}
> {-# LANGUAGE UndecidableInstances  #-}
>
> import           Control.Category ((>>>))
> import           Control.Monad.Except
> import           Control.Monad.Reader
> import           Data.Foldable              (fold)
> import           Data.Functor.Identity
> import           Data.List                  (intercalate)
> import           Data.Map                   (Map)
> import qualified Data.Map                   as M
> import           Data.Maybe
> import           Data.Set                   (Set, (\\))
> import qualified Data.Set                   as S
> import           Prelude                    hiding (lookup)
> import           Text.Printf
>
> import           Text.Parsec
> import           Text.Parsec.Expr
> import           Text.Parsec.Language       (emptyDef)
> import           Text.Parsec.String
> import qualified Text.Parsec.Token          as L
>
> import           Control.Unification        hiding ((=:=), applyBindings)
> import qualified Control.Unification        as U
> import           Control.Unification.IntVar
> import           Data.Functor.Fixedpoint
>
> import           GHC.Generics               (Generic1)
>
> import           System.Console.Repline

Representing our types
----------------------

We'll be implementing a language with lambas, application, and
let-expressions---as well as natural numbers with an addition
operation, just to give us a base type and something to do with it. So
we will have a natural number type and function types, along with
polymorphism, *i.e.* type variables and `forall`.  (Adding more
features like sum and product types, additional base types, recursion,
*etc.* is left as an exercise for the reader!)

So notionally, we want something like this:

``` {.haskell}
type Var = String
data Type = TyVar Var | TyNat | TyFun Type Type
```

However, when using `unification-fd`, we have to encode our `Type`
data type (*i.e.* the thing we want to do unification on) using a
"two-level type" (see [Tim Sheard's original
paper](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.83.500)).

> type Var = String
> data TypeF a = TyVarF Var | TyNatF | TyFunF a a
>   deriving (Show, Eq, Functor, Foldable, Traversable, Generic1, Unifiable)
>
> type Type = Fix TypeF

`TypeF` is a "structure functor" that just defines a single level of
structure; notice `TypeF` is not recursive at all, but uses the
type parameter `a` to mark the places where a recursive instance would
usually be.  `unification-fd` provides a `Fix` type to "tie the knot"
and make it recursive. (I'm not sure why `unification-fd`
defines its own `Fix` type instead of using the one from `Data.Fix`,
but perhaps the reason is that it was written before `Data.Fix`
existed---`unification-fd` was first published in 2007!)

We have to derive a whole bunch of instances for `TypeF` which
fortunately we get for free.  Note in particular `Generic1` and
`Unifiable`: `Unifiable` is a type class from `unification-fd` which
describes how to match up values of our type.  Thanks to the [work of
Roman
Cheplyaka](https://ro-che.info/articles/2017-06-17-generic-unification),
there is a default implementation for `Unifiable` based on a
`Generic1` instance---which GHC derives for us in turn---and the
default implementation works great for our purposes.

`unification-fd` also provides a second type for tying the knot,
called `UTerm`, defined like so:

``` {.haskell}
data UTerm t v
  = UVar  !v               -- ^ A unification variable.
  | UTerm !(t (UTerm t v)) -- ^ Some structure containing subterms.
```

It's similar to `Fix`, except it also adds unification variables of
some type `v`.  (If it means anything to you, note that `UTerm` is
actually the *free monad* over `t`.)  We also define a version of
`Type` using `UTerm`, which we will use during type inference:

> type UType = UTerm TypeF IntVar

`IntVar` is a type provided by `unification-fd` representing variables
as `Int` values, with a mapping from variables to bindings stored in
an `IntMap`. `unification-fd` also provies an `STVar` type which
implements variables via `STRef`s; I presume using `STVar`s would be
faster (since no intermediate lookups in an `IntMap` are required) but
forces us to work in the `ST` monad.  For now I will just stick with
`IntVar`, which makes things simpler.

At this point you might wonder: why do we have type variables in our
definition of `TypeF`, but *also* use `UTerm` to add unification
variables?  Can't we just get rid of the `TyVarF` constructor, and let
`UTerm` provide the variables?  Well, type variables and unification
variables are subtly different, though intimately related.  A type
variable is actually part of a type, whereas a unification variable is
not itself a type, but only *stands for* some type which is (as yet)
unknown.  After we are completely done with type inference, we won't
have a `UTerm` any more, but we might have a type like `forall a. a ->
a` which still contains type variables, so we need a way to represent
them.  We could only get rid of the `TyVarF` constructor if we were
doing type inference for a language without polymorphism (and yes,
unification could still be helpful in such a situation---for example,
to do full type reconstruction for the simply typed lambda calculus,
where lambdas do not have type annotations).

`Polytype` represents a polymorphic type, with a `forall` at the front
and a list of bound type variables (note that regular monomorphic
types can be represented as `Forall [] ty`).  We don't need to make an
instance of `Unifiable` for `Polytype`, since we never unify
polytypes, only (mono)types.  However, we can have polytypes with
unification variables in them, so we need two versions, one containing a
`Type` and one containing a `UType`.

> data Poly t = Forall [Var] t
>   deriving (Eq, Show, Functor)
> type Polytype  = Poly Type
> type UPolytype = Poly UType

Finally, for convenience, we can make a bunch of pattern synonyms that
let us work with `Type` and `UType` just as if they were directly
recursive types.  This isn't required; I just like not having to write
`Fix` and `UTerm` everywhere.

> pattern TyVar :: Var -> Type
> pattern TyVar v = Fix (TyVarF v)
>
> pattern TyNat :: Type
> pattern TyNat = Fix TyNatF
>
> pattern TyFun :: Type -> Type -> Type
> pattern TyFun t1 t2 = Fix (TyFunF t1 t2)
>
> pattern UTyNat :: UType
> pattern UTyNat = UTerm TyNatF
>
> pattern UTyFun :: UType -> UType -> UType
> pattern UTyFun t1 t2 = UTerm (TyFunF t1 t2)
>
> pattern UTyVar :: Var -> UType
> pattern UTyVar v = UTerm (TyVarF v)

Expressions
-----------

Here's a data type to represent expressions.  There's nothing much
interesting to see here, since we don't need to do anything fancy with
expressions.  Note that lambdas don't have type annotations, but
`let`-expressions can have an optional polytype annotation, which will
let us talk about *checking* polymorphic types in addition to
inferring them (a lot of presentations of Hindley-Milner don't talk
about this).

> data Expr where
>   EVar  :: Var -> Expr
>   EInt  :: Integer -> Expr
>   EPlus :: Expr -> Expr -> Expr
>   ELam  :: Var -> Expr -> Expr
>   EApp  :: Expr -> Expr -> Expr
>   ELet  :: Var -> Maybe Polytype -> Expr -> Expr -> Expr

Normally at this point we would write parsers and pretty-printers for
types and expressions, but that's boring and has very little to do
with `unification-fd`, so I've left those to the end.  Let's get on
with the interesting bits!

Type inference infrastructure
-----------------------------

Before we get to the type inference algorithm proper, we'll need to
develop a bunch of infrastructure.  First, here's the concrete monad
we will be using for type inference.  The `ReaderT Ctx` will keep
track of variables and their types; `ExceptT TypeError` of course allows
us to fail with type errors; and `IntBindingT` is a monad transformer
provided by `unification-fd` which supports various operations such as
generating fresh variables and unifying things.  Note, for reasons
that will become clear later, it's very important that the
`IntBindingT` is on the bottom of the stack, and the `ExceptT` comes
right above it.  Beyond that we can add whatever we like on top.

> type Infer = ReaderT Ctx (ExceptT TypeError (IntBindingT TypeF Identity))

Normally, I would prefer to write everything in a "capability style"
where the code is polymorphic in the monad, and just specifies what
capabilites/effects it needs (either just using `mtl` classes
directly, or using an effects library like `polysemy` or
`fused-effects`), but the way the `unification-fd` API is designed
seems to make that a bit tricky.

A type context is a mapping from variable names to polytypes; we also
have a function for looking up the type of a variable in the context,
and a function for running a local subcomputation in an extended
context.

> type Ctx = Map Var UPolytype
>
> lookup :: Var -> Infer UType
> lookup x = do
>   ctx <- ask
>   maybe (throwError $ UnboundVar x) instantiate (M.lookup x ctx)
>
> withBinding :: MonadReader Ctx m => Var -> UPolytype -> m a -> m a
> withBinding x ty = local (M.insert x ty)

The `lookup` function throws an error if the variable is not in the
context, and otherwise returns a `UType`. Conversion from the
`UPolytype` stored in the context to a `UType` happens via a function
called `instantiate`, which opens up the `UPolytype` and replaces each
of the variables bound by the `forall` with a fresh unification
variable.  We will see the implementation of `instantiate` later.

We will often need to recurse over `UType`s.  We could just write
directly recursive functions ourselves, but there is a better way.
Although the `unification-fd` library provides a function `cata` for
doing a fold over a term built with `Fix`, it doesn't provide a
counterpart for `UTerm`; but no matter, we can write one ourselves,
like so:

> ucata :: Functor t => (v -> a) -> (t a -> a) -> UTerm t v -> a
> ucata f _ (UVar v) = f v
> ucata f g (UTerm t) = g (fmap (ucata f g) t)

Now, we can write some utilities for finding free variables.
Inexplicably, `IntVar` does not have an `Ord` instance (even though it
is literally just a `newtype` over `Int`), so we have to derive one if
we want to store them in a `Set`.  Note that our `freeVars` function
finds only free unification variables; a previous version of this
document claimed that we need it to return both unification and type
variables, but this turns out to be unnecessary.  The only reason it
needed to find free type variables was so we could generalize over
Skolem variables, which is wrong (more on this later).

> deriving instance Ord IntVar
>
> class FreeVars a where
>   freeVars :: a -> Infer (Set IntVar)

To find the free unification variables in a `UType`, we just use the
`getFreeVars` function provided by `unification-fd` and massage the
output into the right form.

> instance FreeVars UType where
>   freeVars ut = fmap S.fromList . lift . lift $ getFreeVars ut

Now we can leverage the above instance to find free varaibles in
`UPolytype`s and type contexts.  For a `UPolytype`, note that we don't
have to subtract off any variables bound by the `forall`, since a
`forall` can't bind unification variables.

> instance FreeVars UPolytype where
>   freeVars (Forall _ ut) = freeVars ut
>
> instance FreeVars Ctx where
>   freeVars = fmap S.unions . mapM freeVars . M.elems

And here's a simple utility function to generate fresh unification
variables, built on top of the `freeVar` function provided by `unification-fd`:

> fresh :: Infer UType
> fresh = UVar <$> lift (lift freeVar)

One thing to note is the annoying calls to `lift` we have to do in the
definition of `FreeVars` for `UType`, and in the definition of
`fresh`.  The `getFreeVars` and `freeVar` functions provided by
`unification-fv` have to run in a monad which is an instance of
`BindingMonad`, and the `BindingMonad` class does not provide
instances for `mtl` transformers.  We could write our own instances so
that these functions would work in our `Infer` monad automatically,
but honestly that sounds like a lot of work.  Sprinkling a few `lift`s
here and there isn't so bad.

Next, a data type to represent type errors, and an instance of the
`Fallible` class, needed so that `unification-fd` can inject errors
into our error type when it encounters unification errors.  Basically
we just need to provide two specific constructors to represent an
"occurs check" failure (*i.e.* an infinite type), or a unification
mismatch failure.

> data TypeError where
>   UnboundVar    :: String -> TypeError
>   EscapedSkolem :: Var -> TypeError
>   Infinite      :: IntVar -> UType -> TypeError
>   Mismatch      :: TypeF UType -> TypeF UType -> TypeError
>
> instance Fallible TypeF IntVar TypeError where
>   occursFailure   = Infinite
>   mismatchFailure = Mismatch

The `=:=` operator provided by `unification-fd` is how we unify two
types.  It has a kind of bizarre type:

``` {.haskell}
(=:=) :: ( BindingMonad t v m, Fallible t v e
         , MonadTrans em, Functor (em m), MonadError e (em m))
      => UTerm t v -> UTerm t v -> em m (UTerm t v)
```

(Apparently I am not the only one who thinks this type is bizarre; the
`unification-fd` source code contains the comment `-- TODO: what was
the reason for the MonadTrans madness?`)

I had to stare at this for a while to understand it.  It says that the
output will be in some `BindingMonad` (such as `IntBindingT`), and
there must be a single error monad transformer on top of it, with an
error type that implements `Fallible`.  So `=:=` can return `ExceptT
TypeError (IntBindingT Identity) UType`, but it cannot be used
directly in our `Infer` monad, because that has a `ReaderT` on top of
the `ExceptT`.  So I just made my own version with an extra `lift` to
get it to work directly in the `Infer` monad.  While we're at it,
we'll make a lifted version of `applyBindings`, which has the same
issue.

> (=:=) :: UType -> UType -> Infer UType
> s =:= t = lift $ s U.=:= t
>
> applyBindings :: UType -> Infer UType
> applyBindings = lift . U.applyBindings

Converting between mono- and polytypes
--------------------------------------

Central to the way Hindley-Milner works is the way we move back and
forth between polytypes and monotypes. First, let's see how to turn
`UPolytype`s into `UType`s, hinted at earlier in the definition of the
`lookup` function.  To `instantiate` a `UPolytype`, we generate a
fresh unification variable for each variable bound by the `Forall`,
and then substitute them throughout the type.

> instantiate :: UPolytype -> Infer UType
> instantiate (Forall xs uty) = do
>   xs' <- mapM (const fresh) xs
>   return $ substU (M.fromList (zip (map Left xs) xs')) uty

The `substU` function can substitute for either kind of variable in a
`UType` (right now we only need it to substitute for type variables,
but we will need it to substitute for unification variables later).
Of course, it is implemented via `ucata`.  In the variable cases we
make sure to leave the variable alone if it is not a key in the given
substitution mapping.  In the recursive non-variable case, we just
roll up the `TypeF UType` into a `UType` by applying `UTerm`.  This is
the power of `ucata`: we can deal with all the boring recursive cases
in one fell swoop.  This function won't have to change if we add new
types to the language in the future.

> substU :: Map (Either Var IntVar) UType -> UType -> UType
> substU m = ucata
>   (\v -> fromMaybe (UVar v) (M.lookup (Right v) m))
>   (\case
>       TyVarF v -> fromMaybe (UTyVar v) (M.lookup (Left v) m)
>       f -> UTerm f
>   )

There is one other way to convert a `UPolytype` to a `UType`, which
happens when we want to *check* that an expression has a polymorphic
type specified by the user.  For example, `let foo : forall a. a -> a
= \x.3 in ...` should be a type error, because the user specified that
`foo` should have type `forall a. a -> a`, but then gave the
implementation `\x.3` which is too specific.  In this situation we
can't just `instantiate` the polytype---that would create a
unification variable for `a`, and while typechecking `\x.3` it would
unify `a` with `nat`.  But in this case we *don't* want `a` to unify
with `nat`---it has to be held entirely abstract, because the user's
claim is that this function will work for *any* type `a`.

Instead of generating unification variables, we instead want to
generate what are known as *Skolem* variables.  Skolem variables do
not unify with anything other than themselves.  So how can we get
`unification-fd` to do that?  It does not have any built-in notion of
Skolem variables.  What we can do instead is to just embed the
variables within the `UType` as `UTyVar`s instead of `UVar`s!
`unification-fd` does not even know those are variables; it just sees
them as another rigid part of the structure that must be matched
exactly, just as a `TyFun` has to match another `TyFun`.  The one
remaining issue is that we need to generate *fresh* Skolem variables;
it certainly would not do to have them collide with Skolem variables
from some other `forall`.  We could carry around our own supply of
unique names in the `Infer` monad for this purpose, which would
probably be the "proper" way to do things; but for now I did something
more expedient: just get `unification-fd` to generate fresh
unification variables, then rip the (unique! fresh!) `Int`s out of
them and use those to make our Skolem variables.

> skolemize :: UPolytype -> Infer UType
> skolemize (Forall xs uty) = do
>   xs' <- mapM (const fresh) xs
>   return $ substU (M.fromList (zip (map Left xs) (map toSkolem xs'))) uty
>   where
>     toSkolem (UVar v) = UTyVar (mkVarName "s" v)

When `unification-fd` generates fresh `IntVars` it seems that it
starts at `minBound :: Int` and increments, so we can add `maxBound +
1` to get numbers that look reasonable.  Again, this is not very
principled, but for this toy example, who cares?

> mkVarName :: String -> IntVar -> Var
> mkVarName nm (IntVar v) = nm ++ show (v + (maxBound :: Int) + 1)

Next, how do we convert from a `UType` back to a `UPolytype`? This
happens when we have inferred the type of a `let`-bound variable and
go to put it in the context; typically, Hindley-Milner systems
*generalize* the inferred type to a polytype.  If a unification
variable still occurs free in a type, it means it was not constrained
at all, so we can universally quantify over it.  However, we have to
be careful: unification variables that occur in some type that is
already in the context do not count as free, because we might later
discover that they need to be constrained.

Also, just before we do the generalization, it's very important that
we use `applyBindings`.  `unification-fd` has been collecting a
substitution from unification variables to types, but for efficiency's
sake it does not actually apply the substitution until we ask it to,
by calling `applyBindings`.  Any unification variables which still
remain after `applyBindings` really are unconstrained so far.  So
after `applyBindings`, we get the free unification variables from the
type, subtract off any unification variables which are free in the
context, and close over the remaining variables with a `forall`,
substituting normal type variables for them.  It does not particularly
matter if these type variables are fresh (so long as they are
distinct).

> generalize :: UType -> Infer UPolytype
> generalize uty = do
>   uty' <- applyBindings uty
>   ctx <- ask
>   tmfvs  <- freeVars uty'
>   ctxfvs <- freeVars ctx
>   let fvs = S.toList $ tmfvs \\ ctxfvs
>       xs  = map (mkVarName "a") fvs
>   return $ Forall xs (substU (M.fromList (zip (map Right fvs) (map UTyVar xs))) uty')

A previous version of this post claimed that we should *also*
generalize over Skolem variables, but that was actually wrong.  Many
thanks to Ilya Smirnov for [pointing out the
error](https://byorgey.wordpress.com/2021/09/08/implementing-hindley-milner-with-the-unification-fd-library/#comment-40016).
There *should never* be any Skolem variables remaining in a type we
are generalizing over (unless we intend to [implement a system with
higher-rank
types](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/putting.pdf)!).
At this point we simply take this as an invariant, meaning the code
above does not have to worry about Skolem variables at all; the code
to enforce this invariant is later, in the `infer` function.

Finally, we need a way to convert `Polytype`s entered by the user into
`UPolytypes`, and a way to convert the final `UPolytype` back into a
`Polytype`.  `unification-fd` provides functions `unfreeze : Fix t ->
UTerm t v` and `freeze : UTerm t v -> Maybe (Fix t)` to convert
between terms built with `UTerm` (with unification variables) and
`Fix` (without unification variables).  Converting to `UPolytype` is
easy: we just use `unfreeze` to convert the underlying `Type` to a
`UType`.

> toUPolytype :: Polytype -> UPolytype
> toUPolytype = fmap unfreeze

When converting back, notice that `freeze` returns a `Maybe`; it fails
if there are any unification variables remaining.  So we must be
careful to only use `fromUPolytype` when we know there are no
unification variables remaining in a polytype.  In fact, we will use
this only at the very top level, after generalizing the type that
results from inference over a top-level term.  Since at the top level
we only perform inference on closed terms, in an empty type
context, the final `generalize` step will generalize over all the
remaining free unification variables, since there will be no free
variables in the context.

> fromUPolytype :: UPolytype -> Polytype
> fromUPolytype = fmap (fromJust . freeze)

Type inference
--------------

Finally, the type inference algorithm proper!  First, to `check` that
an expression has a given type, we `infer` the type of the expression
and then demand (via `=:=`) that the inferred type must be equal to
the given one.  Note that `=:=` actually returns a `UType`, and it can
apparently be more efficient to use the result of `=:=` in preference
to either of the arguments to it (although they will all give
equivalent results).  However, in our case this doesn't seem to make
much difference.

> check :: Expr -> UType -> Infer ()
> check e ty = do
>   ty' <- infer e
>   _ <- ty =:= ty'
>   return ()

And now for the `infer` function.  The `EVar`, `EInt`, and `EPlus`
cases are straightforward.

> infer :: Expr -> Infer UType
> infer (EVar x)      = lookup x
> infer (EInt _)      = return UTyNat
> infer (EPlus e1 e2) = do
>   check e1 UTyNat
>   check e2 UTyNat
>   return UTyNat

For an application `EApp e1 e2`, we infer the types `funTy` and
`argTy` of `e1` and `e2` respectively, then demand that `funTy =:=
UTyFun argTy resTy` for a fresh unification variable `resTy`.  Again,
`=:=` returns a more efficient `UType` which is equivalent to `funTy`,
but we don't need to use that type directly (we return `resTy`
instead), so we just discard the result.

> infer (EApp e1 e2) = do
>   funTy <- infer e1
>   argTy <- infer e2
>   resTy <- fresh
>   _ <- funTy =:= UTyFun argTy resTy
>   return resTy

For a lambda, we make up a fresh unification variable for the type of
the argument, then infer the type of the body under an extended
context. Notice how we promote the freshly generated unification
variable to a `UPolytype` by wrapping it in `Forall []`; we do
**not** `generalize` it, since that would turn it into `forall a. a`!
We just want the lambda argument to have the bare unification variable
as its type.

> infer (ELam x body) = do
>   argTy <- fresh
>   withBinding x (Forall [] argTy) $ do
>     resTy <- infer body
>     return $ UTyFun argTy resTy

For a `let` expression without a type annotation, we infer the type of
the definition, then generalize it and add it to the context to infer
the type of the body.  It is traditional for Hindley-Milner systems to
generalize `let`-bound things this way (although note that GHC [does
not generalize `let`-bound
things](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tldi10-vytiniotis.pdf)
with `-XMonoLocalBinds` enabled, which is automatically implied by
`-XGADTs` or `-XTypeFamilies`).

> infer (ELet x Nothing xdef body) = do
>   ty <- infer xdef
>   pty <- generalize ty
>   withBinding x pty $ infer body

For a `let` expression with a type annotation, we `skolemize` it and
`check` the definition with the skolemized type.  We also have to be
careful to ensure that the skolem variables don't "escape": if a
skolem variable unifies with something from outside the context of the
`let`, it indicates that some kind of higher-rank type would be
needed.  A previous version of this post gave the example `\y. let x :
forall a. a -> a = y in x 3`, which is actually a perfect example of a
term that should *not* type check.  Since `x` is supposed to have type
`forall a. a -> a` and is assigned the definition `y`, then `y` must
also have the same type; meaning the whole thing must have type
`(forall a. a -> a) -> nat`, which is a rank-2 type.  However, in this
case we can tell that something goes wrong when we notice that
something involving the skolem variable generated for the type of `x`
unifies with the type of `y` in the outer context.

> infer (ELet x (Just pty) xdef body) = do
>   let upty = toUPolytype pty
>   upty' <- skolemize upty
>   check xdef upty'
>   guardSkolems
>   withBinding x upty $ infer body

The `guardSkolems` function ensures that after checking the definition
of `x`, there are no skolem variables which have leaked into the
outer context via unification.

> guardSkolems :: Infer ()
> guardSkolems = ask >>= mapM_ noSkolems

`noSkolems` ensures there are no Skolem variables, *i.e.* free type
variables, in a `UPolytype`.  We first call `applyBindings` to make
sure that Skolem variables aren't hiding behind a substitution.  Then
we find the free type variables in `upty` using `ucata`: we ignore
unification variables, capture a singleton set in the `TyVarF` case,
and in the recursive case we call `fold`, which will turn a `TypeF
(Set ...)` into a `Set ...` using the `Monoid` instance for `Set`,
*i.e.* `union`.  We then subtract off any variables which are bound by
the `Forall`.  We throw an error if there are any free variables left.

> noSkolems :: UPolytype -> Infer ()
> noSkolems (Forall xs upty) = do
>   upty' <- applyBindings upty
>   let tyvs = ucata (const S.empty)
>                    (\case {TyVarF x -> S.singleton x; f -> fold f})
>                    upty'
>       ftyvs = tyvs `S.difference` S.fromList xs
>   unless (S.null ftyvs) $
>     throwError $ EscapedSkolem (head (S.toList ftyvs))

Running the `Infer` monad
-------------------------

We need a way to run computations in the `Infer` monad.  This is a bit
fiddly, and it took me a long time to put all the pieces together.
(But [typed
holes](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/exts/typed_holes.html)
are sooooo great! It would have taken me way longer without them...)
I've written the definition of `runInfer` using the backwards function
composition operator, `(>>>)`, so that the pipeline flows from top to
bottom and I can intersperse it with explanation.

> runInfer :: Infer UType -> Either TypeError Polytype
> runInfer

The first thing we do is use `applyBindings` to make sure that we
substitute for any unification variables that we know about.  This
results in another `Infer UType`.

>   =   (>>= applyBindings)

We can now generalize over any unification variables that are left,
and then convert from `UPolytype` to `Polytype`.  Again, this
conversion is safe because at this top level we know we will be in an
empty context, so the generalization step will definitely get rid of
all the remaining unification variables.

>   >>> (>>= (generalize >>> fmap fromUPolytype))

Now all that's left is to interpret the layers of our `Infer` monad
one by one.  As promised, we start with an empty type context.

>   >>> flip runReaderT M.empty
>   >>> runExceptT
>   >>> evalIntBindingT
>   >>> runIdentity

Finally, we can make a top-level function to infer a polytype for an
expression, just by composing `infer` and `runInfer`.

> inferPolytype :: Expr -> Either TypeError Polytype
> inferPolytype = runInfer . infer

REPL
----

To be able to test things out, we can make a very simple REPL that
takes input from the user and tries to parse, typecheck, and interpret
it, printing either the results or an appropriate error message.

> eval :: String -> IO ()
> eval s = case parse expr "" s of
>   Left err -> print err
>   Right e -> case inferPolytype e of
>     Left tyerr -> putStrLn $ pretty tyerr
>     Right ty   -> do
>       putStrLn $ pretty e ++ " : " ++ pretty ty
>       when (ty == Forall [] TyNat) $ putStrLn $ pretty (interp e)
>
> main :: IO ()
> main = evalRepl (const (pure "HM> ")) (liftIO . eval) [] Nothing Nothing (Word (const (return []))) (return ()) (return Exit)

Here are a few examples to try out:

```
HM> 2 + 3
2 + 3 : nat
5
HM> \x. x
\x. x : forall a0. a0 -> a0
HM> \x.3
\x. 3 : forall a0. a0 -> nat
HM> \x. x + 1
\x. x + 1 : nat -> nat
HM> (\x. 3) (\y.y)
(\x. 3) (\y. y) : nat
3
HM> \x. y
Unbound variable y
HM> \x. x x
Infinite type u0 = u0 -> u1
HM> 3 3
Can't unify nat and nat -> u0
HM> let foo : forall a. a -> a = \x.3 in foo 5
Can't unify s0 and nat
HM> \f.\g.\x. f (g x)
\f. \g. \x. f (g x) : forall a2 a3 a4. (a3 -> a4) -> (a2 -> a3) -> a2 -> a4
HM> let f : forall a. a -> a = \x.x in let y : forall b. b -> b -> b = \z.\q. f z in y 2 3
let f : forall a. a -> a = \x. x in let y : forall b. b -> b -> b = \z. \q. f z in y 2 3 : nat
2
HM> \y. let x : forall a. a -> a = y in x 3
Escaped skolem s1
HM> (\x. let y = x in y) (\z. \q. z)
(\x. let y = x in y) (\z. \q. z) : forall a1 a2. a1 -> a2 -> a1
```

And that's it!  Feel free to play around with this yourself, and adapt
the code for your own projects if it's helpful.  And please do report
any typos or bugs that you find.

Below, for completeness, you will find a simple, recursive,
environment-passing interpreter, along with code for parsing and
pretty-printing.  I don't give any commentary on them because, for the
most part, they are straightforward and have nothing to do with
`unification-fd`.  But you are certainly welcome to look at them if
you want to see how they work.  The one interesting thing to say about
the parser for types is that it checks that types entered by the user
do not contain any free variables, and fails if they do.  The parser
is not really the right place to do this check, but again, it was
expedient for this toy example.  Also, I tend to use `megaparsec` for
serious projects, but I had some `parsec` code for parsing something
similar to this toy language lying around, so I just reused that.

Interpreter
-----------

> data Value where
>   VInt :: Integer -> Value
>   VClo :: Var -> Expr -> Env -> Value
>
> type Env = Map Var Value
>
> interp :: Expr -> Value
> interp = interp' M.empty
>
> interp' :: Env -> Expr -> Value
> interp' env (EVar x) = fromJust $ M.lookup x env
> interp' _   (EInt n) = VInt n
> interp' env (EPlus ea eb)   =
>   case (interp' env ea, interp' env eb) of
>     (VInt va, VInt vb) -> VInt (va + vb)
>     _ -> error "Impossible! interp' EPlus on non-Ints"
> interp' env (ELam x body) = VClo x body env
> interp' env (EApp fun arg) =
>   case interp' env fun of
>     VClo x body env' ->
>       interp' (M.insert x (interp' env arg) env') body
>     _ -> error "Impossible! interp' EApp on non-closure"
> interp' env (ELet x _ xdef body) =
>   let xval = interp' env xdef
>   in  interp' (M.insert x xval env) body

Parsing
-------

> lexer :: L.TokenParser u
> lexer = L.makeTokenParser emptyDef
>   { L.reservedNames = ["let", "in", "forall", "nat"] }
>
> parens :: Parser a -> Parser a
> parens = L.parens lexer
>
> identifier :: Parser String
> identifier = L.identifier lexer
>
> reserved :: String -> Parser ()
> reserved = L.reserved lexer
>
> reservedOp :: String -> Parser ()
> reservedOp = L.reservedOp lexer
>
> symbol :: String -> Parser String
> symbol = L.symbol lexer
>
> integer :: Parser Integer
> integer = L.natural lexer
>
> parseAtom :: Parser Expr
> parseAtom
>   =   EVar  <$> identifier
>   <|> EInt  <$> integer
>   <|> ELam  <$> (symbol "\\" *> identifier)
>             <*> (symbol "." *> parseExpr)
>   <|> ELet  <$> (reserved "let" *> identifier)
>             <*> optionMaybe (symbol ":" *> parsePolytype)
>             <*> (symbol "=" *> parseExpr)
>             <*> (reserved "in" *> parseExpr)
>   <|> parens parseExpr
>
> parseApp :: Parser Expr
> parseApp = chainl1 parseAtom (return EApp)
>
> parseExpr :: Parser Expr
> parseExpr = buildExpressionParser table parseApp
>   where
>     table = [ [ Infix (EPlus <$ reservedOp "+") AssocLeft ]
>             ]
>
> parsePolytype :: Parser Polytype
> parsePolytype = do
>   pty@(Forall xs ty) <- parsePolytype'
>   let fvs :: Set Var
>       fvs = flip cata ty $ \case
>         TyVarF x       -> S.singleton x
>         TyNatF         -> S.empty
>         TyFunF xs1 xs2 -> xs1 `S.union` xs2
>       unbound = fvs \\ S.fromList xs
>   unless (S.null unbound) $ fail $ "Unbound type variables: " ++ unwords (S.toList unbound)
>   return pty
>
> parsePolytype' :: Parser Polytype
> parsePolytype' =
>   Forall <$> (fromMaybe [] <$> optionMaybe (reserved "forall" *> many identifier <* symbol "."))
>           <*> parseType
>
> parseTypeAtom :: Parser Type
> parseTypeAtom =
>   (TyNat <$ reserved "nat") <|> (TyVar <$> identifier) <|> parens parseType
>
> parseType :: Parser Type
> parseType = buildExpressionParser table parseTypeAtom
>   where
>     table = [ [ Infix (TyFun <$ symbol "->") AssocRight ] ]
>
> expr :: Parser Expr
> expr = spaces *> parseExpr <* eof

Pretty printing
---------------

> type Prec = Int
>
> class Pretty p where
>   pretty :: p -> String
>   pretty = prettyPrec 0
>
>   prettyPrec :: Prec -> p -> String
>   prettyPrec _ = pretty
>
> instance Pretty (t (Fix t)) => Pretty (Fix t) where
>   prettyPrec p = prettyPrec p . unFix
>
> instance Pretty t => Pretty (TypeF t) where
>   prettyPrec _ (TyVarF v) = v
>   prettyPrec _ TyNatF = "nat"
>   prettyPrec p (TyFunF ty1 ty2) =
>     mparens (p > 0) $ prettyPrec 1 ty1 ++ " -> " ++ prettyPrec 0 ty2
>
> instance (Pretty (t (UTerm t v)), Pretty v) => Pretty (UTerm t v) where
>   pretty (UTerm t) = pretty t
>   pretty (UVar v)  = pretty v
>
> instance Pretty Polytype where
>   pretty (Forall [] t) = pretty t
>   pretty (Forall xs t) = unwords ("forall" : xs) ++ ". " ++ pretty t
>
> mparens :: Bool -> String -> String
> mparens True  = ("("++) . (++")")
> mparens False = id
>
> instance Pretty Expr where
>   prettyPrec _ (EVar x) = x
>   prettyPrec _ (EInt i) = show i
>   prettyPrec p (EPlus e1 e2) =
>     mparens (p>1) $
>       prettyPrec 1 e1 ++ " + " ++ prettyPrec 2 e2
>   prettyPrec p (ELam x body) =
>     mparens (p>0) $
>       "\\" ++ x ++ ". " ++ prettyPrec 0 body
>   prettyPrec p (ELet x mty xdef body) =
>     mparens (p>0) $
>       "let " ++ x ++ maybe "" (\ty -> " : " ++ pretty ty) mty
>             ++ " = " ++ prettyPrec 0 xdef
>             ++ " in " ++ prettyPrec 0 body
>   prettyPrec p (EApp e1 e2) =
>     mparens (p>2) $
>       prettyPrec 2 e1 ++ " " ++ prettyPrec 3 e2
>
> instance Pretty IntVar where
>   pretty = mkVarName "u"
>
> instance Pretty TypeError where
>   pretty (UnboundVar x)     = printf "Unbound variable %s" x
>   pretty (EscapedSkolem x)  = printf "Escaped skolem %s" x
>   pretty (Infinite x ty)    = printf "Infinite type %s = %s" (pretty x) (pretty ty)
>   pretty (Mismatch ty1 ty2) = printf "Can't unify %s and %s" (pretty ty1) (pretty ty2)
>
> instance Pretty Value where
>   pretty (VInt n) = show n
>   pretty (VClo x body env)
>     = printf "<%s: %s %s>"
>       x (pretty body) (pretty env)
>
> instance Pretty Env where
>   pretty env = "[" ++ intercalate ", " bindings ++ "]"
>     where
>       bindings = map prettyBinding (M.assocs env)
>       prettyBinding (x, v) = x ++ " -> " ++ pretty v
