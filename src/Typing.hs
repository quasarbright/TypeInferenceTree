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

type M a = State (UnionFind Type) a

unify :: Type -> Type -> M ()
unify a b = do
    uf <- get
    let a' = find uf a
        b' = find uf b
    case (a',b') of
        _ | a' == b' -> return ()
        (TArr arg ret, TArr arg' ret') ->
            zipWithM_ unify [arg,ret] [arg',ret']
        (TVar x, t)
            | x `elem` freeMonoVars t -> undefined -- TODO
            | otherwise -> put (union uf b' a')
        (t, TVar x)
            | x `elem` freeMonoVars t -> undefined -- TODO
            | otherwise -> put (union uf a' b')




step :: InProp -> M (OutProp, Maybe String, [InProp])
step = \case
    InJudgement ctx e -> case e of
        _ -> undefined
    InNewvar x -> return (OutNewvar x, Nothing, [])
    InUnify a b -> unify a b $> (OutUnify a b, Nothing, [])
    InInst t s -> return (OutInst t s, Nothing, [])
    InIn x s ctx
        | Map.member x ctx -> return (OutIn x s ctx, Nothing, [])
        | otherwise -> undefined -- TODO
