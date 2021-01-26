module Typing where

import UnionFind
import AST
import Latex
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Control.Monad.State
import Data.Functor (($>))

-- maybe error should just stop, but don't trash the tree bc you want to see
-- where it errored in the tree

type M a = State (UnionFind Type, Integer) a

unify :: Type -> Type -> M ()
unify a b = do
    (uf,n) <- get
    let a' = find uf a
        b' = find uf b
    case (a',b') of
        _ | a' == b' -> return ()
        (TArr arg ret, TArr arg' ret') ->
            zipWithM_ unify [arg,ret] [arg',ret']
        (TInt, TInt) -> return ()
        (TVar x, t)
            | x `elem` freeMonoVars t -> undefined -- TODO
            | otherwise -> put (union uf b' a',n)
        (t, TVar x)
            | x `elem` freeMonoVars t -> undefined -- TODO
            | otherwise -> put (union uf a' b',n)
        (TArr{},_) -> undefined -- TODO
        (TInt,_) -> undefined -- TODO

newvar :: M String
newvar = do
    (uf,n) <- get
    put (uf,succ n)
    return ("t"++show n)

instantiate :: Scheme -> M Type
instantiate = \case
    SForall x s -> do
        t <- TVar <$> newvar
        let s' = subScheme x t s
        instantiate s'
    SMono t -> return t

generalize :: Context -> Type -> Scheme
generalize ctx t = s
    where monoFrees = freeMonoVars t
          ctxFrees = freeCtxVars ctx
          frees = monoFrees `Set.difference` ctxFrees
          s = foldr SForall (SMono t) frees

-- | Assuming an inference tree is rooted with a typing judgement, get its inferred type.
getTreeType :: InferenceTree -> Type
getTreeType = \case
    InferenceTree (OutJudgement _ _ t) _ _ -> t
    _ -> error "expected a judgement"

infer :: InProp -> M InferenceTree
infer = \case
    InJudgement ctx e -> case e of
        Var x -> case Map.lookup x ctx of
            Nothing -> undefined -- TODO
            Just s -> do
                t <- instantiate s
                InferenceTree (OutJudgement ctx e t) (Just "Var") <$> mapM infer [InIn x s ctx, InInst t s]
        Int{} -> return $ InferenceTree (OutJudgement ctx e TInt) (Just "Nat") []
        Lambda x body -> do
            x' <- newvar
            let tX = TVar x'
                ctx' = Map.insert x (SMono tX) ctx
            bodyTree <- infer (InJudgement ctx' body)
            let tBody = getTreeType bodyTree
                tLambda = TArr tX tBody
            nvTree <- infer (InNewvar x')
            return $ InferenceTree (OutJudgement ctx e tLambda) (Just "Abs") [nvTree, bodyTree]
        Let x rhs body -> do
            rhsTree <- infer (InJudgement ctx rhs)
            let tRhs = getTreeType rhsTree
                sRhs = generalize ctx tRhs
                ctx' = Map.insert x sRhs ctx
            bodyTree <- infer (InJudgement ctx' body)
            let tBody = getTreeType bodyTree
            return $ InferenceTree (OutJudgement ctx e tBody) (Just "Let") [rhsTree, bodyTree]
        App f x -> do
            fTree <- infer (InJudgement ctx f)
            xTree <- infer (InJudgement ctx x)
            t_ <- newvar
            nvTree <- infer (InNewvar t_)
            let tRet = TVar t_
                tF = getTreeType fTree
                tX = getTreeType xTree
            unifyTree <- infer (InUnify (TArr tX tRet) tF)
            return $ InferenceTree (OutJudgement ctx e tRet) (Just "App") [fTree, xTree, nvTree, unifyTree]
    InNewvar x -> return $ pureTree (OutNewvar x)
    InUnify a b -> unify a b $> pureTree (OutUnify a b)
    InInst t s -> return . pureTree $ OutInst t s
    InIn x s ctx
        | Map.member x ctx -> return . pureTree $ OutIn x s ctx
        | otherwise -> undefined -- TODO

runInfer :: M a -> a
runInfer m = evalState m (mempty,1)

inferExpr :: Expr -> Type
inferExpr e = getTreeType (runInfer (infer (InJudgement mempty e)))

renderInference :: Expr -> String
renderInference e = latex $ runInfer (infer (InJudgement mempty e))