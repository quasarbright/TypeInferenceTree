module AST where

import Latex
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
  
data Expr = Var String
          | Lambda String Expr
          | App Expr Expr
          | Let String Expr Expr
          | Int Integer
          deriving(Eq, Ord, Show)

data Type = TVar String
          | TInt
          | TArr Type Type
          deriving(Eq, Ord, Show)

data Scheme = SForall String Scheme
            | SMono Type
            deriving(Eq, Ord, Show)

type Context = Map String Scheme

-- | A proposition which is incomplete and needs further computation (Judgement is waiting for type)
data InProp = InJudgement Context Expr
            | InNewvar String
            | InUnify Type Type
            | InInst Type Scheme
            | InIn String Scheme Context
            deriving(Eq, Ord, Show)

-- | A proposition which is complete and requires no further computation (Judgement has type)
data OutProp = OutJudgement Context Expr Type
             | OutNewvar String
             | OutUnify Type Type
             | OutInst Type Scheme
             | OutIn String Scheme Context
             deriving(Eq, Ord, Show)

-- | a whole derivation/proof tree of an expression's type inference
data InferenceTree =
    InferenceTree
        OutProp -- | Root proposition (usually a judgment)
        (Maybe String) -- | name of typing rule if it's a judgment, Nothing otherwise
        [InferenceTree] -- | Required propositions
    deriving(Eq, Ord, Show)

-- | A proof tree with just one axiomatic proposition
pureTree :: OutProp -> InferenceTree
pureTree prop = InferenceTree prop Nothing []

instance Latex Expr where
    latexsPrec prec = \case
        Var x -> showString x
        Int n -> shows n
        Lambda x body -> showParen (prec > 1) $ showString "\\lambda " . showString x . showString " . " . latexsPrec 3 body
        App f x -> showParen (prec > 2) $ latexsPrec 2 f . showString "\\ " . latexsPrec 3 x
        Let x rhs body -> showParen (prec > 1) $
            showString "\\textrm{let }"
            . showString x
            . showString " = "
            . latexsPrec 0 rhs
            . showString "\\textrm{ in }"
            . latexsPrec 0 body

instance Latex Type where
    latexsPrec prec = \case
        TVar x -> showString x
        TInt -> showString "nat"
        TArr arg ret -> showParen (prec > 1) $ latexsPrec 2 arg . showString " \\rightarrow " . latexsPrec 1 ret

instance Latex Scheme where
    latex = \case
        SForall x s -> "\\forall " ++ x ++ " . " ++ latex s
        SMono t -> latex t

latexContext :: Latex a => Map String a -> String
latexContext ctx =
    let pairs = Map.toList ctx
        latexPair (x,t) = "("++x ++ " : "++ latex t++")"
    in intercalateS ", " (fmap latexPair pairs) ""

instance Latex OutProp where
    latex = \case
        OutJudgement ctx e t ->
            latexContext ctx ++ "\\ \\vdash\\ " ++ latex e ++ " : " ++ latex t
        OutNewvar x -> x++" = newvar "
        OutUnify a b -> " unify("++latex a++" , "++latex b++")"
        OutInst t s -> latex t++" = instantiate("++latex s++")"
        OutIn x s ctx -> "("++x++" : "++latex s++") \\in "++latexContext ctx
    latexList xs = intercalateS "\\quad" (fmap latex xs)

instance Latex InferenceTree where
    latex = \case
        InferenceTree prop Nothing _ -> latex prop
        InferenceTree prop (Just name) requirements ->
            "\\frac{\\displaystyle "++latex requirements++"}{\\displaystyle "++latex prop++"} "++name
    latexList xs = intercalateS " \\quad " (fmap latex xs)

freeMonoVars :: Type -> Set String
freeMonoVars = \case
    TVar x -> Set.singleton x
    TInt -> mempty
    TArr arg ret -> Set.union (freeMonoVars arg) (freeMonoVars ret)

freeSchemeVars :: Scheme -> Set String
freeSchemeVars = \case
    SForall x s -> Set.delete x (freeSchemeVars s)
    SMono t -> freeMonoVars t

freeCtxVars :: Context -> Set String
freeCtxVars ctx = mconcat (fmap freeSchemeVars (Map.elems ctx))

subsMono :: Map String Type -> Type -> Type
subsMono subs = \case
    TVar x -> fromMaybe (TVar x) (Map.lookup x subs)
    TInt -> TInt
    TArr arg ret -> TArr (subsMono subs arg) (subsMono subs ret)

subMono :: String -> Type -> Type -> Type
subMono target replacement = \case
    TVar x
        | x == target -> replacement
        | otherwise -> TVar x
    TInt -> TInt
    TArr arg ret -> TArr (subMono target replacement arg) (subMono target replacement ret)

subsScheme :: Map String Type -> Scheme -> Scheme
subsScheme subs = \case
    SForall x s -> SForall x $ subsScheme subs' s
        where subs' = Map.delete x subs
    SMono t -> SMono $ subsMono subs t

subScheme :: String -> Type -> Scheme -> Scheme
subScheme target replacement = \case
    SForall x s
        | x == target -> SForall x s
        | otherwise -> SForall x (subScheme target replacement s)
    SMono t -> SMono $ subMono target replacement t