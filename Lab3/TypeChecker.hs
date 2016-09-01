module TypeChecker where

import qualified Data.Map as Map
import Control.Monad

import AbsCPP
import PrintCPP
import ErrM

-- | Environment
data Env = Env { envSig :: Sig
               	, envCxt :: Cxt
		, returnType :: Type
               } 

-- | Function signature
type Sig = Map.Map Id ([Type], Type)

-- | Context of local variables
type Cxt = [Block]
type Block = Map.Map Id Type

emptyEnv :: Env
emptyEnv = Env Map.empty [Map.empty] Type_void

newBlock :: Env -> Env
newBlock (Env s c r) = Env s (Map.empty:c) r

typecheck :: Program -> Err Program
typecheck (PDefs def) = do
    env <- buildTable emptyEnv
    env' <- smbTable env def
    (env'', defs') <- checkDefs env' def 
    return (PDefs defs')
	where 
		buildTable env = do
		    env <- updateFun env (Id "printInt") ([Type_int], Type_void)
		    env <- updateFun env (Id "printDouble") ([Type_double], Type_void)
		    env <- updateFun env (Id "readInt") ([], Type_int)
		    env <- updateFun env (Id "readDouble") ([], Type_int)
		    return env
		smbTable env [] = return env
		smbTable env ((DFun tp id args stms):xs) = do
		    env' <- updateFun env id (map findType args, tp)
		    smbTable env' xs
		findType (ADecl x _) = x

updateFun :: Env -> Id -> ([Type], Type) -> Err Env
updateFun (Env sig x ret) i s = do
    case Map.lookup i sig of
        Nothing -> do
            let sig' = Map.insert i s sig 
	    return $ Env sig' x ret
        Just _  -> fail $ "Function already existed."
    
checkDefs :: Env -> [Def] -> Err (Env, [Def])
checkDefs e d = foldM foldTws (e,[]) d
    where 
	foldTws (envTws, defsTws) dTws = do
              (envTws',dTws') <- checkInd envTws dTws
              return (envTws', defsTws ++ [dTws'])
	checkInd env (DFun r a args stms) = do
	    env' <- foldM addArg (newBlock env) args
	    (env'', stms') <- checkStms (newEnv env') stms
	    return (env'', DFun r a args stms')
  	addArg e (ADecl t i) = addVar e i t
        newEnv (Env s c r) = Env s c r

checkStms :: Env -> [Stm] -> Err (Env, [Stm])
checkStms env stms = foldM twice (env, []) stms
	where twice (env, stms') stm = do
		(env',stm') <- checkStm env stm
		return (env', stms' ++ [stm'])

checkStm :: Env -> Stm -> Err (Env, Stm)
checkStm env s =
    case s of
        SExp e -> do
	    inferExp env e >>= \e' -> return (env,(SExp e'))
        SDecls t xs -> do
            foldM (twice t) env xs >>= \env' -> return (env', s)
        SInit t x e -> do 
            checkExp env e t >>= \e' -> addVar env x t >>= \env' -> return (env', (SInit t x e'))
        SReturn e -> do
            inferExp env e >>= \(ETyped t e') -> if (returnType env) == t
                					then return (env, SReturn (ETyped t e'))
               						else fail $ "Expected return type " ++ show (returnType env)
        SWhile ev st -> do 
            checkExp env ev Type_bool >>= \ env' -> checkStm env st >>= \(env,st') -> return (env, SWhile env' st')
        SBlock stms -> do 
            checkStms (newBlock env) stms >>= \(env', stms') -> return (env, (SBlock stms'))
        SIfElse e s1 s2 -> do
            checkExp env e Type_bool >>= \env' -> checkStm env s1 >>= \(e1,s1') -> checkStm env s2 >>= \(e2,s2') -> return (env, (SIfElse env' s1' s2'))
  where twice t a b = addVar a b t

checkExp :: Env -> Exp -> Type -> Err Exp
checkExp env e t = do
	ETyped t' e'<- inferExp env e
	if t' /= t
		then fail (printTree e ++ " has type " ++ printTree t' ++ " expected " ++ printTree t)
		else return (ETyped t' e')

inferExp :: Env -> Exp -> Err Exp
inferExp env exp = case exp of
		ETrue     -> return (ETyped Type_bool exp)
		EFalse    -> return (ETyped Type_bool exp)				
		EDouble _ -> return (ETyped Type_double exp)
		EInt _    -> return (ETyped Type_int exp)
		EId id    -> do
			     lookupVar env id >>= \id' -> return (ETyped id' exp)
		EApp x xs -> do
		    (arg, r) <- lookupFun env x
		    xs' <- mapM (inferExp env) xs
		    let a = map (\(ETyped t e') -> t) xs'
		    if arg == a
		        then return (ETyped r (EApp x xs'))
		        else fail ( "Wrong number of arguments for " ++ printTree x ++ ": expected " ++ show arg)
		EPostIncr x  -> do
		    unaryInf [Type_int, Type_double] env x >>= \e'@(ETyped t _)  -> return (ETyped t (EPostIncr e'))
		EPostDecr x  -> do
		    unaryInf [Type_int, Type_double] env x >>= \e'@(ETyped t _) -> return (ETyped t (EPostDecr e'))
		EPreIncr x  -> do
		    unaryInf [Type_int, Type_double] env x >>= \e'@(ETyped t _) -> return (ETyped t (EPreIncr e'))
		EPreDecr x  -> do
		    unaryInf [Type_int, Type_double] env x >>= \e'@(ETyped t _) -> return (ETyped t (EPreDecr e'))
		ETimes x1 x2 -> do
		    compare x1 x2 >>= \t -> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped t (ETimes e1 e2))
		EDiv x1 x2 -> do
		    compare x1 x2 >>= \t -> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped t (EDiv e1 e2))
		EPlus x1 x2 -> do
		    binaryInf [Type_int, Type_double] env x1 x2 >>= \(e1, e2) -> return (ETyped (selType e1) (EPlus e1 e2))
		EMinus x1 x2 -> do
		    binaryInf [Type_int, Type_double] env x1 x2 >>= \(e1, e2) -> return (ETyped (selType e1) (EMinus e1 e2))
		ELt x1 x2 -> do
		    compare x1 x2 >> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped Type_bool (ELt e1 e2))
		EGt x1 x2 -> do
		    compare x1 x2 >> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped Type_bool (EGt e1 e2))
		ELtEq x1 x2 -> do
		    compare x1 x2 >> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped Type_bool (ELtEq e1 e2))
		EGtEq x1 x2 -> do
		    compare x1 x2 >> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped Type_bool (EGtEq e1 e2))
		EEq x1 x2 -> do
		    compare x1 x2 >> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped Type_bool (EEq e1 e2))
		ENEq x1 x2 -> do
		    compare x1 x2 >> inferExp env x1 >>= \e1 -> inferExp env x2 >>= \e2 -> return (ETyped Type_bool (ENEq e1 e2))
		EAnd x1 x2 -> do
		    inferExp env x1 >>= \e1@(ETyped t1 _) -> inferExp env x2 >>= \e2@(ETyped t2 _) -> if t1 == Type_bool && t2 == Type_bool
													then return (ETyped t1 (EAnd e1 e2))
													else fail $ "Arguments are not boolean types."
		EOr x1 x2 -> do
		    inferExp env x1 >>= \e1@(ETyped t1 _) -> inferExp env x2 >>= \e2@(ETyped t2 _) -> if t1 == Type_bool && t2 == Type_bool
													then return (ETyped t1 (EOr e1 e2))
													else fail $ "Arguments are not boolean types."
		EAss (EId x1) x2 -> do
		    compare (EId x1) x2
		    inferExp env (EId x1) >>= \ (ETyped t _) -> inferExp env x2 >>= \e1 -> return (ETyped t (EAss (ETyped t (EId x1)) e1))
  		where 
		compare e1 e2 = do 
			(ETyped t1 _) <- inferExp env e1
                        (ETyped t2 _) <- inferExp env e2
                        if t1 == t2
				  then return t1
				  else fail $ "Different types used for comparing."
		lookupFun (Env s _ _) i = do
		    case Map.lookup i s of
			Nothing -> fail $ "Function not found."
			Just x  -> return x        	
		unaryInf types env e = do
		    (ETyped typ x) <- inferExp env e
		    if elem typ types
			then return (ETyped typ x)
			else fail $ "Wrong type of expression" ++ printTree e		
		binaryInf types env e1 e2 = do
		    e1'@(ETyped typ _) <- inferExp env e1
		    e2'@(ETyped typ' _) <- inferExp env e2
		    if elem typ types && typ == typ'
			then return (e1', e2')
			else fail $ "Wrong type of expression" ++ printTree e1
		selType (ETyped t _) = t

addVar :: Env -> Id -> Type -> Err Env
addVar (Env sig (c:cs) ret) x t = do
				    if x `Map.notMember` c
					then return $ Env sig (Map.insert x t c:cs) ret
					else fail $ "Variable " ++ show x ++ " already declared."

lookupVar :: Env -> Id -> Err Type
lookupVar (Env _ c _) i = context c i
	where
	context [] i = fail $ "Variable not found in context"
	context (x:xs) i = do
	    case Map.lookup i x of
		Nothing -> context xs i
		Just t  -> return t
