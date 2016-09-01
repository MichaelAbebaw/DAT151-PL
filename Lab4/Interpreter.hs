module Interpreter where

import Prelude hiding (lookup)
import qualified Data.Map as Map

import AbsFun

-- * Entry point

-- | Program computes a number.

interpret :: Program -> Strategy -> Integer
interpret (Prog defs) strategy = i
  where VClos cxt _ = lookup (Ident "main") env
        env = makeGlobal defs
        v = evalExp env cxt strategy
        i = case v of
                VInt j           -> j
                VClos (EInt j) _ -> j

-- | Evaluation strategy.

data Strategy 
    = CallByName 
    | CallByValue 
    deriving (Eq)

data Env = Env 
    {
      functions :: Map.Map Ident Value,
      variables :: Map.Map Ident Value
    } 
    deriving (Show, Eq)

data Value 
    = VInt Integer
    | VClos Exp Env 
    deriving (Show, Eq)

evalExp :: Env -> Exp -> Strategy -> Value
evalExp env e strategy = case e of
    EVar i  -> let VClos exp2 env2 = lookup i env
             in evalExp (Env (functions env) (variables env2)) exp2 strategy

    EAbs _ _ -> VClos e (Env Map.empty $ variables env)         

    EInt _ -> VClos e emptyEnv

    EApp e1 e2 -> let VClos (EAbs x exp2) env2 = evalExp env e1 strategy
                      u = case strategy of
                              CallByName -> VClos e2 (Env Map.empty $ variables env)
                              CallByValue -> evalExp env e2 strategy
                      newEnv = updateVar (Env (functions env) (variables env2)) x u
                  in evalExp newEnv exp2 strategy

    EAdd e1 e2 -> let u = value $ evalExp env e1 strategy
                      v = value $ evalExp env e2 strategy
                  in VClos (EInt (u + v)) emptyEnv

    ESub e1 e2 -> let u = value $ evalExp env e1 strategy
                      v = value $ evalExp env e2 strategy
                  in VClos (EInt (u - v)) emptyEnv

    ELt e1 e2 -> let u = value $ evalExp env e1 strategy
                     v = value $ evalExp env e2 strategy
                 in VInt (if u < v then 1 else 0)

    EIf e1 x y -> let u = evalExp env e1 strategy
                 in if u == VInt 1
                     then evalExp env x strategy
                     else evalExp env y strategy
  where
  updateVar env' i' v' = env' { variables = Map.insert i' v' (variables env') }

makeGlobal :: [Def] -> Env
makeGlobal = foldl (\env (DDef i args exp) -> updateFun env i (emptyVClos exp args)) emptyEnv
    where
    updateFun env' i' v' = env' { functions = Map.insert i' v' (functions env') }     

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty

emptyVClos :: Exp -> [Ident] -> Value
emptyVClos exp args = VClos (conv exp args) emptyEnv
      where conv e [] = e
            conv e args = conv (EAbs (last args) e) (init args)


value :: Value -> Integer
value (VInt int) = int
value (VClos (EInt int) _) = int
value _ = error "impossible to get integer value."

lookup :: Ident -> Env -> Value
lookup id@(Ident s) e =
    case lookupVar id e of
        Nothing -> case lookupFun id e of
                       Nothing -> error $ "Variable " ++ s ++ " not found was not found!"
                       Just v  -> v
        Just v  -> v
  where
  lookupFun i env = Map.lookup i (functions env)
  lookupVar i' env' = Map.lookup i' (variables env')

