module CodeGenerator where

import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import AbsCPP

-- | Environment

data Env = Env 
    {   vars        :: [Map.Map Id Address]
        ,funs        :: Map.Map Id Type
        ,nextLabel   :: Int
        ,nextAddress :: Address
        ,maxAddress  :: Address
        ,stackSize   :: Int
        ,maxSize     :: Int
        ,code        :: [Instruction]
    } 
    deriving (Show)

data CompareOp = CLT | CLTEQ | CEQ | CNEQ | CGTEQ | CGT deriving (Enum, Eq)

type Instruction = String
type Address = Int
type FunType = Int
type Label = Int

emptyEnv :: Env
emptyEnv = Env 
    {   vars        = [Map.empty]
        ,funs        = Map.empty
        ,nextLabel   = 0
        ,nextAddress = 1
        ,maxAddress  = 1
        ,stackSize   = 0
        ,maxSize     = 1
        ,code        = []
    }

-- | Service functions
emit :: Instruction -> State Env ()
emit i = modify $ \s -> s {code = i : code s}

lookupVar :: Id -> State Env Address
lookupVar x = do
    s <- get
    return $ lookVars (vars s)
  where lookVars [] = error $ "Unbound variable " ++ show x
        lookVars (m:ms) = do
            case Map.lookup x m of
                Just a  -> a
                Nothing -> lookVars ms

lookupFun :: Id -> State Env Type
lookupFun i = do
    s <- get
    case Map.lookup i (funs s) of
        Nothing -> error $ "No function with id " ++ show i
        Just t  -> return t

newBlock :: State Env ()
newBlock = modify $ \s -> s { vars = Map.empty:vars s }

exitBlock :: State Env ()
exitBlock = modify $ \s -> s { vars = tail $ vars s }

nLabel :: State Env Label
nLabel = do
    s <- get
    let label = nextLabel s
    modify $ \s' -> s' { nextLabel = label + 1 }
    return label

addVar :: Id -> Type -> State Env ()
addVar i t = do
    s <- get
    let (currS:restS) = vars s
    modify (\s' -> s'
            { nextAddress = (nextAddress s') + size t
            , vars = Map.insert i (nextAddress s') currS:restS
            }
           )

addFun :: Id -> Type -> State Env ()
addFun i t = modify ( \s -> s { funs = Map.insert i t (funs s) })

size :: Type -> Int
size Type_int    = 1
size Type_bool   = 1

-- * Code generator

codeGenerator :: String -> Program -> State Env ()
codeGenerator filename (PDefs defs) = do
    buildSymbolTable defs
    mapM_ emit
      [ ".class public " ++ filename
      , ".super java/lang/Object"
      , ""
      , ".method public <init>()V"
      , "  aload_0"
      , "  invokespecial java/lang/Object/<init>()V"
      , "  return"
      , ".end method"
      , ""
      , ".method public static main([Ljava/lang/String;)V"
      , ".limit locals 1"
      , "  invokestatic "++filename++"/main()I"
      , "  pop"
      , "  return"
      , ".end method"
      ]
    mapM_ compileDef defs

compile :: String -> Program -> String
compile s p = unlines $ reverse $ code (execState (codeGenerator s p) emptyEnv)

buildSymbolTable :: [Def] -> State Env ()
buildSymbolTable def = mapM_ (\(DFun t i _ _) -> addFun i t) def

compileDef :: Def -> State Env ()
compileDef (DFun t (Id "main") _ stms) = do
    emit $ ".method public static main2()I"
    emit $ ".limit locals 1000"
    emit $ ".limit stack 1000"
    
    newBlock
    
    mapM_ compileStm $ stms
    
    exitBlock

    emit $ "iconst_0"
    emit $ "ireturn"
    emit ".end method"
compileDef (DFun t (Id i) args stms) = do
    emit $ ".method public static " ++ i ++ "(" ++ typArgs ++ ")" ++ typeNm t
    emit $ ".limit locals 100"
    emit $ ".limit stack 1337"
    newBlock
    s <- get
    let n' = nextAddress s
    modify (\s -> s {nextAddress = 0} )
    mapM_ (\(ADecl t' i') -> addVar i' t') args
    mapM_ (\(ADecl t' i') -> lookupVar i' >>= (\a -> emit $ loadx t' ++ " " ++ show a)) args
    mapM_ compileStm $ stms
    modify (\s' -> s' { nextAddress = n' } )
    
    case t of
        Type_int -> emit "iconst_0" >> emit "ireturn"
        Type_bool -> emit "iconst_0" >> emit "ireturn"
        Type_void -> emit $ "return"

    emit ".end method"

    exitBlock

  where typeNm (Type_int)    = "I"
        typeNm(Type_void)   = "V"
        typeNm (Type_bool)   = "Z"
        typArgs = concat $ map (\(ADecl t' _) -> typeNm t') args
        loadx Type_int = "iload"
        loadx Type_bool   = "iload"

compileStm :: Stm -> State Env ()
compileStm stm = case stm of
	SExp e -> do
		compileExp e >> case selType e of
				    Type_int -> emit "pop"
				    Type_bool -> emit "pop"
				    Type_void -> return ()
	SDecls t ids -> do
		mapM_ (\id -> addVar id t) ids >> case t of
						    Type_int -> mapM_ (\id -> lookupVar id >>= (\x -> emit "iconst_0" >> emit ("istore " ++ show x))) ids
						    Type_bool -> mapM_ (\id -> lookupVar id >>= (\x -> emit "iconst_0" >> emit ("istore " ++ show x))) ids
	SInit   t i e   -> do
		addVar i t >> lookupVar i >>= \x -> compileExp e >> case t of
								       Type_int -> emit ("istore " ++ show x)
								       Type_bool -> emit ("istore " ++ show x)
	SReturn e -> do
		compileExp e >> case selType e of
		    	             Type_int -> emit "ireturn"
		    		     Type_bool -> emit "ireturn"
		    		     Type_void -> emit "return"
	SWhile  e s    -> do
		x <- nLabel
		y <- nLabel
		let testLabel = "l" ++ show x
		let endLabel = "l" ++ show y	    
		emit (testLabel ++ ":") >> compileExp e 
		emit ( "ifeq " ++ endLabel) >> compileStm s  
		emit ("goto " ++ testLabel) >> emit (endLabel ++ ":")	    
	SBlock s -> do
		newBlock >> mapM_ compileStm s >> exitBlock
	SIfElse e s1 s2 -> ifElse e (compileStm s1) (compileStm s2)
	where
	selType (ETyped t _) = t

compileExp :: Exp -> State Env ()
compileExp (ETyped t e) = 
	case e of
		ETrue -> emit ("iconst_1")
	    	EFalse -> emit ("iconst_0")
		EInt i -> emit ("ldc " ++ show i)
		EId i -> do
			lookupVar i >>= \x -> emit $ case t of
						  Type_int -> "iload " ++ show x
						  Type_bool -> "iload " ++ show x
		-- 	
		EApp (Id "printInt") args -> do
			mapM_ compileExp args >> emit "invokestatic Runtime/printInt(I)V"
		EApp (Id "readInt")    _ -> do
			emit "invokestatic Runtime/readInt()I"
		EApp (Id i) a -> do
			lookupFun (Id i) >>= \t -> mapM_ compileExp a >> emit ( "invokestatic test/" ++ i ++ "(" ++ typeArg ++ ")" ++ typeNm t)
			where 
			typeNm (Type_int) = "I"
			typeNm (Type_bool) = "Z"
			typeNm (Type_void) = "V"
			typeArg = concat (map (\(ETyped t' _) -> typeNm t') a)
		-- 	   
		EPostIncr e'@(ETyped t' (EId i)) -> do
			compileExp e' >> lookupVar i >>= \x -> case t' of
								    Type_int -> do
									emit "dup" >> emit "iconst_1" >> emit "iadd" >> emit ("istore " ++ show x)
		EPostDecr e'@(ETyped t' (EId i))    -> do
			compileExp e' >> lookupVar i >>= \x -> case t' of
									    Type_int -> do
										emit "dup" >> emit "iconst_1" >> emit "isub" >> emit ("istore " ++ show x)

		EPreIncr e'@(ETyped t' (EId i))    -> do
			compileExp e' >> lookupVar i >>= \x -> case t' of
								    Type_int -> do
									emit "iconst_1" >> emit "iadd" >> emit "dup" >> emit ("istore " ++ show x)
		EPreDecr e-> error "Not defined!"
	    
		--
		ETimes e1 e2 -> arc "mul" e1 e2
		EDiv e1 e2 -> arc "div" e1 e2
		EPlus e1 e2 -> arc "add" e1 e2
		EMinus e1 e2 -> arc "sub" e1 e2
		--
		ELt e1 e2 -> eval CLT e1 e2 
		EGt e1 e2 -> eval CGT e1 e2 
		ELtEq e1 e2 -> eval CLTEQ e1 e2 
		EGtEq e1 e2 -> eval CGTEQ e1 e2
		EEq e1 e2 -> eval CEQ e1 e2
		ENEq e1 e2 -> eval CNEQ e1 e2
		EAnd e1 e2 -> 
			ifElse e1 ( ifElse e2 (emit "iconst_1") (emit "iconst_0") ) (emit "iconst_0")
	    	EOr   e1 e2  -> 
			ifElse e1 (emit "iconst_1") ( ifElse e2 (emit "iconst_1") (emit "iconst_0") )
	    	EAss  (ETyped _ (EId i)) e2  -> do
			compileExp e2 >> lookupVar i >>= \a -> case t of
							    Type_int -> do
								emit "dup" >> emit ("istore " ++ show a)
							    Type_bool -> do
								emit "dup" >> emit ("istore " ++ show a)
		where
		arc i e1 e2 = do
		    compileExp e1 >> compileExp e2 >> emit ("i" ++ i)
compileExp exp = error ("Not ETyped: " ++ show exp)		


eval :: CompareOp -> Exp -> Exp -> State Env ()
eval c e1 e2 = do
		let t = selType e1
		x <- nLabel
		let y = "l" ++ show x
		emit "bipush 1" >> compileExp e1 >> compileExp e2
		emit ("if_icmp" ++ instrRep c ++ y) >> emit "pop" >> emit "bipush 0" >> emit (y ++ ":")
		where 
		instrRep c' = fromJust (lookup c' (zip [CLT ..] ["lt ", "le ", "eq ", "ne ", "ge ", "gt "]))
		selType (ETyped t _) = t

ifElse :: Exp -> State Env () -> State Env () -> State Env ()
ifElse e st1 st2 = do
    x <- nLabel
    y <- nLabel
    compileExp e 
    emit ("ifeq " ++ "l" ++ show x) >> st1
    emit ("goto " ++ "l" ++ show y) >> emit ("l" ++ show x ++ ":") >> st2 >> emit ("l" ++ show x ++ ":")
