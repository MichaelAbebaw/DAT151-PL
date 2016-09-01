module Interpreter where

import AbsCPP
import PrintCPP
import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe


-- | Values
data Val
  = VInt Integer
  | VDouble Double
  | VBool Bool
  | VVoid
  | VUndefined
  deriving (Eq, Show)

instance Ord Val where
    compare (VInt i) (VInt j)        = compare i j
    compare (VDouble i) (VDouble j)  = compare i j
    compare (VInt i) (VDouble j)     = compare (fromIntegral i) j
    compare (VDouble i) (VInt j)     = compare i (fromIntegral j)

-- | Environment
data Env = Env
  { envSig :: Sig
  , envCxt :: Cxt
  }

-- | Function signature
type Sig = Map Id Def

-- | Context of local variables
type Cxt = [Block]
type Block = Map Id Val


interpret :: Program -> IO ()
interpret (PDefs defs) = do
  -- Build initial environment with all function definitions.
  let env = foldl extendSig emptyEnv defs
  let DFun _t _f _args ss = lookupDef env (Id "main")
  foldM_ execStm env ss

execDef :: Env -> Def -> IO (Val, Env)
execDef env (DFun _ _ _ ((SReturn e):_)) = eval env e
execDef env (DFun t i args (s:ss)) = do
    env' <- execStm env s
    execDef env' (DFun t i args ss)
execDef env (DFun _ _ _ ([])) = return (VVoid, env)

execStms :: Env -> [Stm] -> IO Env
execStms env [] = return env
execStms env (s:stms) = do
    env' <- execStm env s
    execStms env' stms

execStm :: Env -> Stm -> IO Env
execStm env s = do
  case s of
   -- SExp e           -> eval env e >>= return . snd
    SExp e -> do
      (v, env') <- eval env e
      return env'
    SInit t x e      -> do
      let env' = addVar env x
      (value, env'') <- eval env' e
      return $ setVar env'' x value
    SDecls _ xs      -> return $ foldl (addVar) env xs
    SReturn _        -> return env
    SWhile e s1      -> do
      (val, env') <- eval env e
      if val == VBool True
          then do 
            env'' <- execStm env' s1
            execStm env'' s
      else return env' 
    SBlock xs        -> do
      env' <- execStms (newBlock env) xs
      return (exitBlock env')
    SIfElse e s1 s2  -> do
      (val, env') <- eval env e
      if val == VBool True
        then execStm env' s1
      else execStm env' s2

eval :: Env -> Exp -> IO (Val,Env)
eval env e = case e of
    EInt i     -> return (VInt i, env)
    EId x      -> return (lookupVar env x, env)
    EDouble d  -> return (VDouble d, env)
    ETrue      -> return (VBool True, env)
    EFalse     -> return (VBool False, env)

-- Built-in funcitons printInt, printDouble, readInt, readDouble
    EApp (Id "printInt") e' -> do
            (VInt i, env') <- eval env (head e')
            putStrLn $ show i
            return (VVoid, env')

    EApp (Id "printDouble") e' -> do
            (VDouble d, env') <- eval env (head e')
            putStrLn $ show d
            return (VVoid, env')

    EApp (Id "readInt") _ -> do
            i <- getLine
            return (VInt (read i), env)

    EApp (Id "readDouble") _ -> do
            d <- getLine
            return (VDouble (read d), env)


    EApp i es     -> do
            (vals, env') <- foldM foldE ([], env) es
            let def@(DFun _ _ args _) = lookupDef env' i
            let argsNames = map (\(ADecl _ it) -> it) args

            let env'' = newBlock env'
            let a = zip argsNames vals

            let env''' = foldl (\e' (arg,val) -> setVar (addVar e' arg) arg val) env'' a
            (resVal, resEnv) <- execDef env''' def
            return (resVal, exitBlock resEnv)
-- Post increment, post decrement and increment, decrement            
    EPostIncr (EId i) -> do
            (val, env') <- eval env (EId i)
            let newVal = case val of
                            VInt i -> VInt $ i + 1
                            VDouble d -> VDouble $ d + 1

            let env'' = setVar env' i (newVal)
            return (val, env'')
    EPostDecr (EId i) -> do
            (val, env') <- eval env (EId i)
            let newVal = case val of
                            VInt i -> VInt $ i - 1
                            VDouble d -> VDouble $ d - 1

            let env'' = setVar env' i (newVal)
            return (val, env'')
    EPreIncr (EId i) -> do
            (val, env') <- eval env (EId i)
            let newVal = case val of
                            VInt i -> VInt $ i + 1
                            VDouble d -> VDouble $ d + 1

            let env'' = setVar env' i (newVal)
            return (newVal, env'')
    EPreDecr (EId i) -> do
            (val, env') <- eval env (EId i)
            let newVal = case val of
                            VInt i -> VInt $ i - 1
                            VDouble d -> VDouble $ d - 1

            let env'' = setVar env' i (newVal)
            return (newVal, env'')
 -- Binary operations           
    EPlus e1 e2   -> do
            (v1, env')  <- eval env e1
            (v2, env'') <- eval env' e2
            case (v1,v2) of
                (VInt i1, VInt i2)       -> return (VInt (i1+i2), env'')
                (VDouble d1, VDouble d2) -> return (VDouble (d1+d2), env'')
    EMinus e1 e2   -> do
            (v1, env')  <- eval env e1
            (v2, env'') <- eval env' e2
            case (v1,v2) of
                (VInt i1, VInt i2)       -> return (VInt (i1-i2), env'')
                (VDouble d1, VDouble d2) -> return (VDouble (d1-d2), env'')
    ETimes e1 e2   -> do
            (v1, env')  <- eval env e1
            (v2, env'') <- eval env' e2
            case (v1,v2) of
                (VInt i1, VInt i2)       -> return (VInt (i1*i2), env'')
                (VDouble d1, VDouble d2) -> return (VDouble (d1*d2), env'')
    EDiv e1 e2   -> do
            (v1, env')  <- eval env e1
            (v2, env'') <- eval env' e2
            case (v1,v2) of
                (VInt i1, VInt i2)       -> return (VInt (div i1 i2), env'')
                (VDouble d1, VDouble d2) -> return (VDouble (d1/d2), env'')
    ELt   e1 e2   -> comparision (<)  e1 e2
    EGt   e1 e2   -> comparision (>)  e1 e2
    ELtEq e1 e2   -> comparision (<=) e1 e2
    EGtEq e1 e2   -> comparision (>=) e1 e2
    EEq   e1 e2   -> comparision (==) e1 e2
    ENEq  e1 e2   -> comparision (/=) e1 e2
    EAnd e1 e2    -> do
            (v1, env') <- eval env e1
            if v1 == VBool True
                then eval env' e2
                else return (VBool False, env')
    EOr e1 e2    -> do
            (v1, env') <- eval env e1
            if v1 == VBool False
                then eval env' e2
                else return (VBool True, env')
-- Assignment
    EAss (EId i) e2    -> do
            (val, env')  <- eval env e2
            return (val, setVar env' i val)

  where foldE (val, env) e = do
            (val', env') <- eval env e
            return (val ++ [val'], env')
        comparision op e1 e2 = do
            (v1, env')  <- eval env e1
            (v2, env'') <- eval env' e2
            if v1 `op` v2
                then return (VBool True, env'')
                else return (VBool False, env'')

lookupDef :: Env -> Id -> Def
lookupDef (Env s _) f = case Map.lookup f s of
        Nothing -> error $ "undefined function " ++ printTree f
        Just d -> d 

lookupVar :: Env -> Id -> Val
lookupVar env x = case catMaybes $ map (Map.lookup x) (envCxt env) of
  []      -> error $ "unbound variable " ++ printTree x
  (v : _) -> v

extendSig :: Env -> Def -> Env
extendSig env def@(DFun _t f _args _ss) = env { envSig = Map.insert f def (envSig env) }

-- | Change value of an existing variable.
setVar :: Env -> Id -> Val -> Env
setVar env@Env{ envCxt = bs } x v = env { envCxt = loop bs } where
  loop []       = error $ "unbound variable " ++ printTree x
  loop (b : bs) = case Map.lookup x b of
    Nothing -> b : loop bs
    Just{}  -> Map.insert x v b : bs

addVar :: Env -> Id -> Env
addVar (Env s (c:cs)) i = Env s (Map.insert i VUndefined c:cs)

newBlock :: Env -> Env
newBlock env = env { envCxt = Map.empty : (envCxt env) }

exitBlock :: Env -> Env
exitBlock env@Env { envCxt = b : bs } = env { envCxt = bs }

emptyEnv :: Env
emptyEnv = Env Map.empty ([Map.empty])