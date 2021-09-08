---
title: "Implementing Hindley-Milner with the unification-fd library"
---

    [BLOpts]
    profile = wp
    postid = 2393
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
out to make my own example, and you're reading it.  Along the way,
things I found especially helpful include [this basic unification-fd
tutorial](https://winterkoninkje.dreamwidth.org/100478.html) by the
author, Wren Romano, as well as a [blog post by Roman
Cheplyaka](https://ro-che.info/articles/2017-06-17-generic-unification),
and the [unification-fd Haddock
documentation](https://hackage.haskell.org/package/unification-fd)
itself.

This blog post is rendered automatically from a literate Haskell file;
you can [find the complete working source code and blog post on
GitHub](https://github.com/byorgey/hm-unification-fd).  I'm always
happy to receive comments, fixes, or suggestions for improvement.

Without further ado, let's get on with it!

A Bunch of Extensions and Imports
---------------------------------

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
> {-# LANGUAGE TemplateHaskell       #-}
> {-# LANGUAGE TypeSynonymInstances  #-}
> {-# LANGUAGE UndecidableInstances  #-}
>
> import           Control.Monad.Except
> import           Control.Monad.Reader
> import           Control.Monad.State
> import           Data.Functor.Identity
> import           Data.List                  ((\\))
> import           Data.Map                   (Map, (!))
> import qualified Data.Map                   as M
> import           Data.Maybe
> import           Data.Set                   (Set)
> import qualified Data.Set                   as S
> import           Data.Void
> import           Prelude                    hiding (lookup)
> import           System.IO                  (getLine)
> import           Text.Printf
>
> import           Text.Parsec
> import           Text.Parsec.Expr
> import           Text.Parsec.Language       (emptyDef)
> import           Text.Parsec.String
> import qualified Text.Parsec.Token          as L
>
> import           Control.Unification        hiding ((=:=))
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
let-expressions, as well as natural numbers with an addition operation
just to give us a base type and something to do with it. So we will
have a natural number type and function types, along with
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
structure; notice `TypeF` is not recursive at all, but just has the
type parameter `a` marking the places where a recursive instance would
usually be.  `unification-fd` provides a `Fix` type to "tie the knot"
and make it recursive. (I'm not really sure why `unification-fd`
defines its own `Fix` type instead of using the one from `Data.Fix`,
but perhaps the reason is that it was written before `Data.Fix`
existed---`unification-fd` was first published in 2007!)

We have to derive a whole bunch of instances for `TypeF` which
fortunately we get for free.  Note in particular `Generic1` and
`Unifiable`: `Unifiable` is a type class from `unification-fd` which
describes how to match up values of our type.  Thanks to the
[work of Roman
Cheplyaka](https://ro-che.info/articles/2017-06-17-generic-unification),
there is a default implementation for `Unifiable` based on a
`Generic1` instance, which GHC derives for us, and the default
implementation works just great for our purposes.

`unification-fd` also provides a different type for tying the knot,
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
forces us to work in the `ST` monad.  For now I just stuck with
`IntVar` which makes some things simpler.

At this point you might wonder: why do we have type variables in our
definition of `TypeF`, but *also* use `UTerm` to add unification
variables?  Well, type variables and unification variables are subtly
different, though intimately related.  A type variable is actually
part of a type, whereas a unification variable only *stands for* some
type which is (as yet) unknown.

`Polytype` represents a polymorphic type, with a `forall` at the front
and a list of bound type variables (note that regular monomorphic
types can be represented as `Forall [] ty`).  We don't need to make an
instance of `Unifiable` for `Polytype`, since we never unify
polytypes, only (mono)types.  However, we can have polytypes with
unification variables in them, so we need two versions, one containing a
`Type` and one containing a `UType`.

> data Poly t = Forall [Var] t
> type Polytype  = Poly Type
> type UPolytype = Poly UType

Finally, for convenience, we can make a bunch of pattern synonyms that
let us work with `Type` and `UType` as if they were just defined as
directly recursive types.  This isn't required; I just like not having
to write `Fix` and `UTerm` everywhere.

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
let me talk about *checking* polymorphic types.

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
track of the types of variables; `ExceptT TypeError` of course allows
us to fail with type errors; and `IntBindingT` is a monad transformer
provided by `unification-fd` which supports various operations such as
generating fresh variables and unifying things.  Note, for reasons
that will become clear later, it's very important that the
`IntBindingT` is on the bottom of the stack, and the `ExceptT` comes
right above it.  Beyond that we can add whatever we like.

> type Infer = ReaderT Ctx (ExceptT TypeError (IntBindingT TypeF Identity))

Normally, I would prefer to write everything in a "capability style"
where the code is polymorphic in the monad, and just specifies what
capabilites/effects it needs (either just using `mtl` directly, or
using an effects library like `polysemy` or `fused-effects`), but the
way the `unification-fd` API is designed seems to make that a bit
tricky.

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

XXXXX rewrite this
Notice that variables actually map to `Either UPolytype UType`.  In a
typical presentation of Hindley-Milner, the type context just stores
polytypes, and polytypes are defined as being either a monotype or a
`forall` quantifier followed by a monotype, so we can stick monotypes
in the context just as well as polytypes.  But when you carefully
consider where things in the type context come from, you realize that
putting a monotype in the context happens when we have just generated
a unification variable for the type of something, and want to record
it in the context.  In that case what we actually have is a `UType`,
not a `Type`, and converting the `UType` to a `Polytype` just to store
it in the context (and just to convert it back when we take it out
again later) seems silly and wasteful, especially since converting
from `UType` to `Type` actually requires traversing the entire
structure.

The `lookup` function throws an error if the variable is not in the
context, and otherwise returns a `UType`. Conversion from `UPolytype`
to `UType` happens via a function called `instantiate`, which
essentially opens up the `Polytype` and replaces each of the variables
bound by the `forall` with a fresh unification variable.  We will see
the implementation of `instantiate` later.

Next, some utilities for finding free unification variables, and a
function for generating fresh ones.  Inexplicably, `IntVar` does not
have an `Ord` instance (even though it is literally just a `newtype`
over `Int`), so we have to derive one if we want to store them in a
`Set`.

> deriving instance Ord IntVar
>
> class FreeVars a where
>   freeVars :: a -> Infer (Set IntVar)
>
> instance FreeVars UType where
>   freeVars = fmap S.fromList . lift . lift . getFreeVars
>
> instance FreeVars UPolytype where
>   freeVars (Forall _ ut) = freeVars ut
>
> instance FreeVars Ctx where
>   freeVars = fmap S.unions . mapM freeVars . M.elems
>
> fresh :: Infer UType
> fresh = UVar <$> lift (lift freeVar)

Note also the annoying calls to `lift` we have to do in the definition
of `FreeVars` for `UType`, and in the definition of `fresh`.  The
`getFreeVars` and `freeVar` functions provided by `unification-fv`
have to run in a monad which is an instance of `BindingMonad`, and the
`BindingMonad` class does not provide instances for `mtl`
transformers.  We could write our own instances so that these
functions would work in our `Infer` monad automatically, but honestly
that sounds like a lot of work.  Sprinkling a few `lift`s here and
there isn't so bad.

Next, a data type to represent type errors, and an instance of the
`Fallible` class, needed so that `unification-fd` can inject errors
into our error type when it encounters unification errors.  Basically
we just need to provide two specific constructors to represent an
"occurs check" failure (*i.e.* an infinite type), or a unification
mismatch failure.

> data TypeError where
>   UnboundVar   :: String -> TypeError
>   Infinite     :: IntVar -> UType -> TypeError
>   Mismatch     :: TypeF UType -> TypeF UType -> TypeError
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

I had to stare at this for a while to understand it.  It says that the
output will be in some `BindingMonad` (such as `IntBindingT`), and
there must be a single error monad transformer on top of it, with an
error type that implements `Fallible`.  So `=:=` can have type
`ExceptT TypeError (IntBindingT Identity) UType`, but it cannot be
used directly in our `Infer` monad, because that has a `ReaderT` on
top of the `ExceptT`.  So I just made my own version with an extra
`lift` to get it to work directly in the `Infer` monad.

> (=:=) :: UType -> UType -> Infer UType
> s =:= t = lift $ s U.=:= t

Converting between mono- and polytypes
--------------------------------------

Central to the way Hindley-Milner works is the way we move back and
forth between polytypes and monotypes. First, let's see how to turn
`UPolytype`s into `UType`s, hinted at earlier in the definition of the
`lookup` function.  To `instantiate` a `UPolytype`, we generate a
fresh unification variable for each variable bound by the `Forall`,
and then substitute them throughout the type, using

XXX the `substU`
function. The `substU` function substitutes `UTyVar`s for unification
variables in the `UType`, using the fact that `UTerm` is the free
monad over `TypeF`, which means that the bind operation is
substitution!

> instantiate :: UPolytype -> Infer UType
> instantiate (Forall xs uty) = do
>   xs' <- mapM (const fresh) xs
>   return $ substU (M.fromList (zip xs xs')) uty

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
>   return $ substU (M.fromList (zip xs (map toSkolem xs'))) uty
>   where
>     toSkolem (UVar v) = UTyVar (mkVar "s" v)

When `unification-fd` generates fresh `IntVars` it seems that it
starts at `minBound :: Int` and increments, so we can add `maxBound +
1` to get numbers that look reasonable.  Again, this is not very
principled, but for this toy example, who cares?

> mkVar :: String -> IntVar -> String
> mkVar nm (IntVar v) = nm ++ show (v + (maxBound :: Int) + 1)

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
context, and close over the remaining unification variables with a
`forall`, substituting normal type variables for them.  It does not
particularly matter if these type variables are fresh (so long as they
are distinct), but we just generate them from the numbers in the
unification vars, again using `mkVar`.

> gen :: UType -> Infer UPolytype
> gen uty = do
>   uty' <- lift $ applyBindings uty
>   ctx <- ask
>   fvs    <- S.toList <$> freeVars uty'
>   ctxfvs <- S.toList <$> freeVars ctx
>   let xs = map (mkVar "a") $ fvs \\ ctxfvs
>   return $ Forall xs (substU (M.fromList (zip fvs xs)) uty')

Type inference
--------------

Finally, the type inference algorithm proper!  The `EVar`, `EInt`, and
`EPlus` cases are straightforward.

> infer :: Expr -> Infer UType
> infer (EVar x)      = lookup x
> infer (EInt _)      = return UTyNat
> infer (EPlus e1 e2) = do
>   check e1 UTyNat
>   check e2 UTyNat
>   return UTyNat

The `check` function just calls `infer` on its argument and then
demands (via `=:=`) that the inferred type must be equal to the given
one.

For an application `EApp e1 e2`, we infer the types `funTy` and
`argTy` of `e1` and `e2` respectively, then demand that `funTy =:=
UTyFun argTy resTy` for a fresh unification variable `resTy`.

> infer (EApp e1 e2) = do
>   funTy <- infer e1
>   argTy <- infer e2
>
>   resTy <- fresh
>   funTy =:= UTyFun argTy resTy
>   return resTy

For a lambda, we make up a fresh unification variable for the type of
the argument, then infer the type of the body under an extended
context.  Notice how in this scenario we are putting a `UType` into
the context.

> infer (ELam x body) = do
>   argTy <- fresh
>   withBinding x (Forall [] argTy) $ do
>     resTy <- infer body
>     return $ UTyFun argTy resTy

For a `let` expression without a type annotation, we infer the type of
the definition, then generalize it and add it to the context (here, we
are putting a `Polytype` into the context) to infer the type of the body.

> infer (ELet x Nothing xdef body) = do
>   ty <- infer xdef
>   pty <- gen ty
>   withBinding x pty $ infer body

For a `let` expression with a type annotation, we skolemize it and
`check` the definition with the skolemized type; the rest is the same
as the previous case.

> infer (ELet x (Just pty) xdef body) = do
>   let upty = unfreezePolytype pty
>   upty' <- skolemize upty
>   check xdef upty'
>   withBinding x upty $ infer body

Here's the `check` function.

> check :: Expr -> UType -> Infer ()
> check e ty = do
>   ty' <- infer e
>   ty =:= ty'
>   return ()

Running the `Infer` monad
-------------------------

> freezePolytype :: UPolytype -> Polytype
> freezePolytype (Forall xs uty) = Forall xs (fromJust (freeze uty))

> unfreezePolytype :: Polytype -> UPolytype
> unfreezePolytype (Forall xs ty) = Forall xs (unfreeze ty)

> runInfer :: Infer UType -> Either TypeError Polytype
> runInfer
>   = fmap freezePolytype
>   . runIdentity
>   . evalIntBindingT
>   . runExceptT
>   . flip runReaderT M.empty
>   . (>>= gen)
>   . (>>= lift . applyBindings)

Finally, we can make a top-level function to infer a polytype for an
expression, just by composing `infer` and `runInfer`.

> inferPolytype :: Expr -> Either TypeError Polytype
> inferPolytype = runInfer . infer

REPL
----

Just to be able to test it out, we can make a very simple REPL that
takes input from the user and tries to parse and then typecheck it,
printing either the resulting inferred polytype or an appropriate
error message.

> eval :: String -> IO ()
> eval s = case parse expr "" s of
>   Left err -> print err
>   Right e -> case inferPolytype e of
>     Left tyerr -> putStrLn $ pretty tyerr
>     Right ty   -> putStrLn $ pretty e ++ " : " ++ pretty ty
>
> type Repl a = HaskelineT IO a
>
> main :: IO ()
> main = evalRepl (const (pure "HM> ")) (liftIO . eval) [] Nothing Nothing (Word (const (return []))) (return ()) (return Exit)
>

Parsing and pretty-printing
---------------------------

For completeness, the code for parsing and pretty-printing is below.
The only interesting thing to say about the parser is that it checks
that types entered by the user do not contain any free variables, and
fails if they do.  The parser is not really the right place to do this
check, but again, it was expedient for this toy example.  Also, I tend
to use `megaparsec` for serious projects, but I had some `parsec` code
for parsing something similar to this toy language lying around, so I
just reused that.

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
>       unbound = fvs `S.difference` (S.fromList xs)
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
>   pretty = mkVar "u"
>
> instance Pretty TypeError where
>   pretty (UnboundVar x)     = printf "Unbound variable %s" x
>   pretty (Infinite x ty)    = printf "Infinite type %s = %s" (pretty x) (pretty ty)
>   pretty (Mismatch ty1 ty2) = printf "Can't unify %s and %s" (pretty ty1) (pretty ty2)



`openVars` is just a catamorphism over `Type = Fix TypeF` which
outputs a `UType`; all we have to do is define an algebra of type
`TypeF UType -> UType`.  In the case of a `TyVarF` we look up the new
variable; in any other case we can just use `UTerm` to roll up the
`TypeF UType` into a `UType`.  Of course using `cata` is a bit fancy,
and we could have easily written this code via straightforward
recursion over types, but it's nice that this code won't have to be
updated even if we add more features to the language later!

-- >
-- > openVars :: Map Var UType -> Type -> UType
-- > openVars m = cata (\case {TyVarF x -> m!x; f -> UTerm f})



 Then we call `freeze`, which converts any `UTerm t v`
into a `Maybe (Fix t)`, failing if there are any `UVars` left.

XXX I actually had a bug here at first.  

-- > closeVars :: Map IntVar Var -> UType -> UType
-- > closeVars m uty = fromJust $ freeze (uty >>= (UTyVar . (m!)))


substU :: Map Var UType -> UType -> UType
substU m = (>>= (m!))
