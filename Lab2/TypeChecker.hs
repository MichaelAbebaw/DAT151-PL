module TypeChecker where

import AbsCPP
import PrintCPP
import ErrM
import Control.Monad

import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

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

typecheck :: Program -> Err ()
typecheck (PDefs def) = do
    env <- buildTable emptyEnv
    env' <- smbTable env def
    checkDefs env' def 
    return ()
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
		  where findType (ADecl x _) = x
 

checkDefs :: Env -> [Def] -> Err Env
checkDefs = foldM check 
	where
	check env (DFun j _ args stms) = do
					    env' <- foldM addArg (newBlock env) args
					    checkStms (newEnv env' j) stms
	addArg e (ADecl t i) = addVar e i t
	newEnv (Env s c _) j = Env s c j		
  
checkStms :: Env -> [Stm] -> Err Env
checkStms = foldM checkStm

checkStm :: Env -> Stm -> Err Env
checkStm env s =
    case s of
        SExp e -> do
			inferExp env e 
			return env
        SDecls t xs -> foldM (twice t) env xs
        SInit t x e -> do 
			checkExp env e t
			addVar env x t
        SReturn e -> do
		    t <- inferExp env e
		    if (returnType env) == t
			then return env
			else fail $ "Expected return type " ++ show (returnType env)
        SWhile e s1 -> do 
			checkExp env e Type_bool
			checkStm env s1
        SBlock stms -> do 
			checkStms (newBlock env) stms
			return env
        SIfElse e s1 s2 -> do
			    checkExp env e Type_bool
			    checkStm env s1
			    checkStm env s2
			    return env
  where twice t a b = addVar a b t
  
checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = do
		t' <- inferExp env e
		if t' /= t
			then fail (printTree e ++ " has type " ++ printTree t' ++ " expected " ++ printTree t)
			else return ()

inferExp :: Env -> Exp -> Err Type
inferExp env exp = case exp of
					ETrue     -> return Type_bool
					EFalse    -> return Type_bool					
					EDouble _ -> return Type_double
					EInt _    -> return Type_int
					EId x     -> lookupVar env x
					EApp x xs -> do
						(argTypes, ret) <- lookupDef env x
						xs' <- mapM (inferExp env) xs
						if argTypes == xs'
							then return ret
							else fail ( "Wrong number of arguments for " ++ printTree x ++ ": expected " ++ show argTypes ++ ": given " ++show xs)
					EPostIncr x  -> inferNumber [Type_int, Type_double] env x
					EPostDecr x  -> inferNumber [Type_int, Type_double] env x
					EPreIncr x   -> inferNumber [Type_int, Type_double] env x
					EPreDecr x   -> inferNumber [Type_int, Type_double] env x
					ETimes e1 e2 -> compareExp e1 e2
					EDiv e1 e2   -> compareExp e1 e2
					EPlus e1 e2  -> inferNumbers [Type_int, Type_double] env e1 e2
					EMinus e1 e2 -> inferNumbers [Type_int, Type_double] env e1 e2
					ELt e1 e2    -> do 
							compareExp e1 e2
							return Type_bool
					EGt e1 e2 -> do 
							compareExp e1 e2
							return Type_bool
					ELtEq e1 e2 -> do 
							compareExp e1 e2 
							return Type_bool
					EGtEq e1 e2 -> do 
							compareExp e1 e2
							return Type_bool
					EEq e1 e2 -> do 
							compareExp e1 e2
							return Type_bool
					ENEq e1 e2 -> do 
							compareExp e1 e2
							return Type_bool
					EAnd e1 e2 -> do
							t1 <- inferExp env e1
							t2 <- inferExp env e2
							if t1 == Type_bool && t2 == Type_bool
								then return t1
								else fail $"Arguments are not boolean types."
					EOr e1 e2 -> do
							t1 <- inferExp env e1
							t2 <- inferExp env e2
							if t1 == Type_bool && t2 == Type_bool
								then return t1
								else fail $ "Arguments are not boolean types."
					EAss (EId x) e1 -> do 
							compareExp (EId x) e1 
							inferExp env (EId x)
			  where compareExp e1 e2 = do 
							t1 <- inferExp env e1
							t2 <- inferExp env e2
							if t1 == t2
								  then return t1
								  else fail $ "Different types used for comparing."
				inferNumber types env e = do
							typ <- inferExp env e
							if elem typ types
								then return typ
								else fail $ "Wrong type of expression" ++ printTree e
											
				inferNumbers types env e1 e2 = do
							typ <- inferExp env e1
							if elem typ types
								then do 
									checkExp env e2 typ 
									return typ
								else fail $ "Wrong type of expression" ++ printTree e1

lookupDef :: Env -> Id -> Err ([Type], Type)
lookupDef (Env sig _ _) i = do
				case Map.lookup i sig of
					Nothing -> fail $ "Function was not found :" ++ show i
					Just f  -> return f

updateFun :: Env -> Id -> ([Type], Type) -> Err Env
updateFun (Env sig x ret) id s = do
    case Map.lookup id sig of
        Nothing -> do
            let sig' = Map.insert id s sig
            return $ Env sig' x ret
        Just _  -> fail $ show id ++ " is already declared."

lookupVar :: Env -> Id -> Err Type
lookupVar env x = case catMaybes $ map (Map.lookup x) (envCxt env) of
				  []      -> fail $ "unbound variable " ++ printTree x
				  (t : _) -> return t
  
addVar :: Env -> Id -> Type -> Err Env
addVar (Env sig (c:cs) ret) x t = do
				    if x `Map.notMember` c
					then return $ Env sig (Map.insert x t c:cs) ret
					else fail $ "Variable " ++ show x ++ " already declared."

newBlock :: Env -> Env
newBlock env = env { envCxt = Map.empty : (envCxt env) }

exitBlock :: Env -> Env
exitBlock env@Env { envCxt = b : bs } = env { envCxt = bs }

emptyEnv :: Env
emptyEnv = Env { envSig = Map.empty, envCxt = [Map.empty],  returnType = Type_void}