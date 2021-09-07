{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

-- Hindley-Milner + natural numbers and addition, implemented via the
-- unification-fd library.

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Functor.Identity
import           Data.List                  ((\\))
import           Data.Map                   (Map, (!))
import qualified Data.Map                   as M
import           Data.Maybe
import           Data.Set                   (Set)
import qualified Data.Set                   as S
import           Data.Void
import           Prelude                    hiding (lookup)
import           System.IO                  (getLine)
import           Text.Printf

import           Text.Parsec
import           Text.Parsec.Expr
import           Text.Parsec.Language       (emptyDef)
import           Text.Parsec.String
import qualified Text.Parsec.Token          as L

import           Control.Unification        hiding ((<:=), (=:=))
import qualified Control.Unification        as U
import           Control.Unification.IntVar
import           Data.Functor.Fixedpoint

import           GHC.Generics               (Generic1)

import           System.Console.Repline

------------------------------------------------------------
-- Types
------------------------------------------------------------

type Var = String

-- We have to encode our types (whatever we want to do unification on)
-- using a "two-level type" (Sheard,
-- http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.83.500).
-- TypeF is a "structure functor" that just defines a single level of
-- structure; notice TypeF is not recursive at all, but just has the
-- type parameter 'a' marking the places where a recursive instance
-- would usually be.
--
-- We have to derive a whole lot of instances which fortunately we get
-- for free.  Note in particular Generic1 and Unifiable.  We could write our own Unifiable instances
data TypeF a = TyVarF Var | TyNatF | TyFunF a a
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic1, Unifiable)

type Type = Fix TypeF
type UType = UTerm TypeF IntVar

data Polytype = Forall [Var] Type

pattern TyVar :: Var -> Type
pattern TyVar v = Fix (TyVarF v)

pattern TyNat :: Type
pattern TyNat = Fix TyNatF

pattern TyFun :: Type -> Type -> Type
pattern TyFun t1 t2 = Fix (TyFunF t1 t2)

pattern UTyNat :: UType
pattern UTyNat = UTerm TyNatF

pattern UTyFun :: UType -> UType -> UType
pattern UTyFun t1 t2 = UTerm (TyFunF t1 t2)

pattern UTyVar :: Var -> UType
pattern UTyVar v = UTerm (TyVarF v)

------------------------------------------------------------
-- Expressions
------------------------------------------------------------

data Expr where
  EVar  :: Var -> Expr
  EInt  :: Integer -> Expr
  EPlus :: Expr -> Expr -> Expr
  ELam  :: Var -> Expr -> Expr
  ELet  :: Var -> Maybe Polytype -> Expr -> Expr -> Expr
  EApp  :: Expr -> Expr -> Expr

------------------------------------------------------------
-- Parser
------------------------------------------------------------

lexer :: L.TokenParser u
lexer = L.makeTokenParser emptyDef
  { L.reservedNames = ["let", "in", "forall", "nat"] }

parens :: Parser a -> Parser a
parens = L.parens lexer

identifier :: Parser String
identifier = L.identifier lexer

reserved :: String -> Parser ()
reserved = L.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = L.reservedOp lexer

symbol :: String -> Parser String
symbol = L.symbol lexer

integer :: Parser Integer
integer = L.natural lexer

parseAtom :: Parser Expr
parseAtom
  =   EVar  <$> identifier
  <|> EInt  <$> integer
  <|> ELam  <$> (symbol "\\" *> identifier)
            <*> (symbol "." *> parseExpr)
  <|> ELet  <$> (reserved "let" *> identifier)
            <*> optionMaybe (symbol ":" *> parsePolytype)
            <*> (symbol "=" *> parseExpr)
            <*> (reserved "in" *> parseExpr)
  <|> parens parseExpr

parseApp :: Parser Expr
parseApp = chainl1 parseAtom (return EApp)

parseExpr :: Parser Expr
parseExpr = buildExpressionParser table parseApp
  where
    table = [ [ Infix (EPlus <$ reservedOp "+") AssocLeft ]
            ]

parsePolytype :: Parser Polytype
parsePolytype = do
  pty@(Forall xs ty) <- parsePolytype'
  let fvs :: Set Var
      fvs = flip cata ty $ \case
        TyVarF x       -> S.singleton x
        TyNatF         -> S.empty
        TyFunF xs1 xs2 -> xs1 `S.union` xs2
      unbound = fvs `S.difference` (S.fromList xs)
  unless (S.null unbound) $ fail $ "Unbound type variables: " ++ unwords (S.toList unbound)
  return pty

parsePolytype' :: Parser Polytype
parsePolytype' =
  Forall <$> (fromMaybe [] <$> optionMaybe (reserved "forall" *> many identifier <* symbol "."))
          <*> parseType

parseTypeAtom :: Parser Type
parseTypeAtom =
  (TyNat <$ reserved "nat") <|> (TyVar <$> identifier) <|> parens parseType

parseType :: Parser Type
parseType = buildExpressionParser table parseTypeAtom
  where
    table = [ [ Infix (TyFun <$ symbol "->") AssocRight ] ]

expr :: Parser Expr
expr = spaces *> parseExpr <* eof

tm :: String -> Expr
tm s = case parse expr "" s of
  Left err -> error (show err)
  Right e  -> e

------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------

type Prec = Int

class Pretty p where
  pretty :: p -> String
  pretty = prettyPrec 0

  prettyPrec :: Prec -> p -> String
  prettyPrec _ = pretty

instance Pretty (t (Fix t)) => Pretty (Fix t) where
  prettyPrec p = prettyPrec p . unFix

instance Pretty t => Pretty (TypeF t) where
  prettyPrec _ (TyVarF v) = v
  prettyPrec _ TyNatF = "nat"
  prettyPrec p (TyFunF ty1 ty2) =
    mparens (p > 0) $ prettyPrec 1 ty1 ++ " -> " ++ prettyPrec 0 ty2

instance (Pretty (t (UTerm t v)), Pretty v) => Pretty (UTerm t v) where
  pretty (UTerm t) = pretty t
  pretty (UVar v)  = pretty v

instance Pretty Polytype where
  pretty (Forall [] t) = pretty t
  pretty (Forall xs t) = unwords ("forall" : xs) ++ ". " ++ pretty t

mparens :: Bool -> String -> String
mparens True  = ("("++) . (++")")
mparens False = id

instance Pretty Expr where
  prettyPrec _ (EVar x) = x
  prettyPrec _ (EInt i) = show i
  prettyPrec p (EPlus e1 e2) =
    mparens (p>1) $
      prettyPrec 1 e1 ++ " + " ++ prettyPrec 2 e2
  prettyPrec p (ELam x body) =
    mparens (p>0) $
      "\\" ++ x ++ ". " ++ prettyPrec 0 body
  prettyPrec p (ELet x mty xdef body) =
    mparens (p>0) $
      "let " ++ x ++ maybe "" (\ty -> " : " ++ pretty ty) mty
            ++ " = " ++ prettyPrec 0 xdef
            ++ " in " ++ prettyPrec 0 body
  prettyPrec p (EApp e1 e2) =
    mparens (p>2) $
      prettyPrec 2 e1 ++ " " ++ prettyPrec 3 e2

------------------------------------------------------------
-- Type checker
------------------------------------------------------------

type Ctx = Map String (Either Polytype UType)

freeVars :: UType -> InferM [IntVar]
freeVars = lift. lift . getFreeVars

freeCtx :: Ctx -> InferM [IntVar]
freeCtx = fmap concat . mapM (either (\_ -> return []) freeVars) . M.elems

lookup :: Var -> InferM (Maybe UType)
lookup x = do
  ctx <- ask
  mapM (either inst return) (M.lookup x ctx)

data TypeError where
  UnboundVar   :: String -> TypeError
  Infinite     :: IntVar -> UType -> TypeError
  Mismatch     :: TypeF UType -> TypeF UType -> TypeError
  NotInst      :: UType -> Polytype -> TypeError

instance Fallible TypeF IntVar TypeError where
  occursFailure   = Infinite
  mismatchFailure = Mismatch

instance Pretty IntVar where
  pretty (IntVar v) = "a" ++ show (v + (maxBound :: Int) + 1)

instance Pretty TypeError where
  pretty (UnboundVar x)     = printf "Unbound variable %s" x
  pretty (Infinite x ty)    = printf "Infinite type %s = %s" (pretty x) (pretty ty)
  pretty (Mismatch ty1 ty2) = printf "Can't unify %s and %s" (pretty ty1) (pretty ty2)
  pretty (NotInst ty1 ty2)  = printf "%s is not an instance of %s" (pretty ty1) (pretty ty2)

(=:=) :: UType -> UType -> InferM UType
s =:= t = lift $ s U.=:= t

(<:=) :: UType -> UType -> InferM Bool
s <:= t = lift $ s U.<:= t

type InferM = ReaderT Ctx (ExceptT TypeError (IntBindingT TypeF Identity))

runInferM :: InferM UType -> Either TypeError Polytype
runInferM
  = runIdentity
  . evalIntBindingT
  . runExceptT
  . flip runReaderT M.empty
  . (>>= gen)
  . (>>= lift . applyBindings)

withBinding :: MonadReader Ctx m => Var -> Either Polytype UType -> m a -> m a
withBinding x ty = local (M.insert x ty)

-- This needs to go in case for let, and in runInferM
gen :: UType -> InferM Polytype
gen uty = do
  ctx <- ask
  uty' <- lift $ applyBindings uty
  fvs <- freeVars uty'
  ctxfvs <- freeCtx ctx
  let xs = map mkVar (fvs \\ ctxfvs)
  return $ Forall xs (closeVars (M.fromList (zip fvs xs)) uty')

deriving instance Ord IntVar

mkVar (IntVar v) = "a" ++ show (v + (maxBound :: Int) + 1)

(!!!) :: Map Var a -> Var -> a
e !!! x = case M.lookup x e of
  Nothing -> error $ x ++ " is not a key in the environment!"
  Just v  -> v

closeVars :: Map IntVar Var -> UType -> Type
closeVars m uty = fromJust $ freeze (uty >>= (UTyVar . (m!)))

inst :: Polytype -> InferM UType
inst (Forall xs ty) = do
  xs' <- mapM (const fresh) xs
  return $ openVars (M.fromList (zip xs xs')) ty

skolemize :: Polytype -> InferM UType
skolemize (Forall xs ty) = do
  xs' <- mapM (const fresh) xs
  return $ openVars (M.fromList (zip xs (map toSkolem xs'))) ty
  where
    toSkolem (UVar (IntVar v)) = UTyVar ("s" ++ show (v + (maxBound :: Int) + 1))

openVars :: Map Var UType -> Type -> UType
openVars m = cata (\case {TyVarF x -> m!!!x; f -> UTerm f})

fresh :: InferM UType
fresh = UVar <$> lift (lift freeVar)

infer :: Expr -> InferM UType
infer (EVar x)      = lookup x >>= maybe (throwError $ UnboundVar x) return
infer (EInt _)      = return UTyNat
infer (EPlus e1 e2) = do
  check e1 UTyNat
  check e2 UTyNat
  return UTyNat
infer (EApp e1 e2) = do
  funTy <- infer e1
  argTy <- infer e2

  resTy <- fresh
  funTy =:= UTyFun argTy resTy
  return resTy
infer (ELam x body) = do
  argTy <- fresh
  withBinding x (Right argTy) $ do
    resTy <- infer body
    return $ UTyFun argTy resTy
infer (ELet x (Just pty) xdef body) = do
  pty' <- skolemize pty
  check xdef pty'
  withBinding x (Left pty) $ infer body
infer (ELet x Nothing xdef body) = do
  ty <- infer xdef
  pty <- gen ty
  withBinding x (Left pty) $ infer body

check :: Expr -> UType -> InferM ()
check e ty = do
  ty' <- infer e
  ty =:= ty'
  return ()

recon :: Expr -> Either TypeError Polytype
recon = runInferM . infer

------------------------------------------------------------
-- Evaluation + REPL
------------------------------------------------------------

eval :: String -> IO ()
eval s = case parse expr "" s of
  Left err -> print err
  Right e -> case recon e of
    Left tyerr -> putStrLn $ pretty tyerr
    Right ty   -> putStrLn $ pretty e ++ " : " ++ pretty ty

type Repl a = HaskelineT IO a

main :: IO ()
main = evalRepl (const (pure "HM> ")) (liftIO . eval) [] Nothing Nothing (Word (const (return []))) (return ()) (return Exit)
