module AST where

import Latex
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
  
data Expr = Var String
          | Lambda String Expr
          | App Expr Expr
          | Let String Expr Expr
          deriving(Eq, Ord)

data Type = TVar String
          | TArr Type Type
          deriving(Eq, Ord)

data Scheme = SForall String Scheme
            | SMono Type
            deriving(Eq, Ord)

type Context = Map String Scheme

-- | A proposition which is incomplete and needs further computation (Judgement is waiting for type)
data InProp = InJudgement Context Expr
            | InNewvar String
            | InUnify Type Type
            | InInst Type Scheme
            | InIn String Scheme Context
            deriving(Eq, Ord)

-- | A proposition which is complete and requires no further computation (Judgement has type)
data OutProp = OutJudgement Context Expr Type
             | OutNewvar String
             | OutUnify Type Type
             | OutInst Type Scheme
             | OutIn String Scheme Context
             deriving(Eq, Ord)

-- | a whole derivation/proof tree of an expression's type inference
data InferenceTree =
    InferenceTree
        OutProp -- | Root proposition (usually a judgment)
        (Maybe String) -- | name of typing rule if it's a judgment, Nothing otherwise
        [InferenceTree] -- | Required propositions

-- | A proof tree with just one axiomatic proposition
pureTree :: OutProp -> InferenceTree
pureTree prop = InferenceTree prop Nothing []

instance Latex Expr where
    latexsPrec prec = \case
        Var x -> showString x
        Lambda x body -> showParen (prec > 3) $ showString "\\lambda. " . showString x . latexsPrec 3 body
        App f x -> showParen (prec > 2) $ latexsPrec 2 f . showString " " . latexsPrec 3 x
        Let x rhs body -> showParen (prec > 3) $
            showString "\textrm{let }"
            . showString x
            . showString " = "
            . latexsPrec 0 rhs
            . showString "\textrm{ in }"
            . latexsPrec 0 body

instance Latex Type where
    latexsPrec prec = \case
        TVar x -> showString x
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
        OutInst t s -> latex t++" = inst("++latex s++")"
        OutIn x s ctx -> "("++x++" : "++latex s++") \\in "++latexContext ctx
    latexList xs = intercalateS "\\quad" (fmap latex xs)

instance Latex InferenceTree where
    latex = \case
        InferenceTree prop Nothing _ -> latex prop
        InferenceTree prop (Just name) requirements ->
            "\\frac{\\displaystyle "++latex requirements++"}{\\displaystyle "++latex prop++"} "++name

freeMonoVars :: Type -> Set String
freeMonoVars = \case
    TVar x -> Set.singleton x
    TArr arg ret -> Set.union (freeMonoVars arg) (freeMonoVars ret)