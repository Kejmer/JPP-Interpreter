module Interpreter where

import Types
import ErrM
import Control.Monad.State
import Data.Map (Map, lookup, findMax, size, insert, member, empty, (!))
import Data.Maybe (fromJust)
import Control.Monad.Except


-----------------------------
-- MEMORY MENAGEMENT START --
-----------------------------

type Loc = Int
data TypeEnv = TypeEnv
    { parent_env :: Maybe TypeEnv
    , local_env :: Map Ident Loc
    }

data TypeContext = TypeContext
    { env :: TypeEnv
    , store :: Map Loc Type
    , values :: Map Loc Value
    }

data Value
    = VInt Integer
    | VBool Bool
    | VStr String
    | VFun BasicType [Arg] [Stmt]
    | VProc [Arg] [Arg] [Stmt]
    | VArr Value Value -- val + next // like a queue
    | VNone
    deriving (Prelude.Eq, Prelude.Ord, Prelude.Show, Prelude.Read)

type Context a = StateT TypeContext (ExceptT String IO) a

emptyEnv :: TypeEnv
emptyEnv = TypeEnv { parent_env = Nothing, local_env = Data.Map.empty }

emptyContext :: TypeContext
emptyContext = TypeContext { env = emptyEnv, store = Data.Map.empty, values = Data.Map.empty }

getLocAux :: Ident -> TypeEnv -> Err Loc
getLocAux name env =
    let local = local_env env in
    if Data.Map.member name local
    then Ok (fromJust $ Data.Map.lookup name local)
    else case parent_env env of
        Nothing -> Bad $ "Called variable has no defined type: " ++ show name
        Just parent -> getLocAux name parent

getLoc :: Ident -> Context (Err Loc)
getLoc name =
    gets (getLocAux name . env)

getTypeAux :: Err Loc -> Map Loc Type -> Err Type
getTypeAux eloc mem = do
    loc <- eloc
    if Data.Map.member loc mem
    then pure $ fromJust $ Data.Map.lookup loc mem
    else Bad "Execution error, got location but there was nothing saved"

getType :: Ident -> Context (Err Type)
getType name = do
    loc <- getLoc name
    gets (getTypeAux loc . store)

pushEnv ::  Context ()
pushEnv = do
    context <- get
    put TypeContext {
        env = TypeEnv {
            parent_env = Just $ env context,
            local_env = Data.Map.empty
        },
        store = store context,
        values = values context
    }

popEnv :: Context ()
popEnv = do
    context <- get
    case parent_env $ env context of
        Nothing -> pure ()
        Just env -> put TypeContext {
            env = env,
            store = store context,
            values = values context
        }

newLoc :: Context Loc
newLoc = gets (size . store)

declareAux :: Ident -> Loc -> TypeEnv -> TypeEnv
declareAux name loc env = TypeEnv {
    parent_env = parent_env env,
    local_env = insert name loc $ local_env env
}

declare :: Arg -> Context ()
declare (FArg typ name) = do
    loc <- newLoc
    context <- get
    put TypeContext {
        env = declareAux name loc $ env context,
        store = insert loc typ $ store context,
        values = values context
    }

assignValue :: Ident -> Value -> Context ()
assignValue name val = do
    loc <- getLoc name
    context <- get
    case loc of
        Left _ -> pure ()
        Right l -> put TypeContext {
            env = env context,
            store = store context,
            values = insert l val $ values context
        }

assignValueArg :: Arg -> Value -> Context ()
assignValueArg (FArg typ name) = assignValue name

assignValuesArgs :: [Arg] -> [Value] -> Context ()
assignValuesArgs (x:xs) (y:ys) = assignValueArg x y >> assignValuesArgs xs ys
assignValuesArgs [] [] = pure ()
assignValuesArgs _ _ = pure raiseErr >> pure () -- ERROR

getValue :: Ident -> Context Value
getValue name = do
    loc <- getLoc name
    context <- get
    pure $ case loc of
        Left _ -> VNone
        Right l -> values context ! l

addEnvFrame :: [Arg] -> Context ()
addEnvFrame args = do
    pushEnv
    forM_ args declare

---------------------------------------
------------- OPERATIONS --------------
---------------------------------------

addOp :: Value -> AddOp -> Value -> Value
addOp (VInt a) Plus (VInt b) = VInt $ a + b
addOp (VStr a) Plus (VStr b) = VStr $ a ++ b
addOp (VInt a) Minus (VInt b) = VInt $ a - b
addOP _ _ = VNone

mulOp :: Value -> MulOp -> Value -> Value
mulOp (VInt a) Times (VInt b) = VInt $ a * b
mulOp (VInt a) Div (VInt b) = VInt $ a `div` b
mulOp (VInt a) Mod (VInt b) = VInt $ a `mod` b
mulOp _ _ _ = VNone

negateOp :: Value -> Value
negateOp (VBool True) = VBool False
negateOp (VBool False) = VBool True
negateOp (VInt a) = VInt (-a)
negateOp _ = VNone

compOp :: Value -> CompOp -> Value -> Value
compOp (VInt a) Eq (VInt b) = VBool $ a == b
compOp (VStr a) Eq (VStr b) = VBool $ a == b
compOp (VBool a) Eq (VBool b) = VBool $ a == b
compOp x NEq y = negateOp $ compOp x Eq y
compOp (VInt a) Low (VInt b) = VBool $ a < b
compOp (VInt a) LowEq (VInt b) = VBool $ a <= b
compOp (VInt a) Grt (VInt b) = VBool $ a > b
compOp (VInt a) GrtEq (VInt b) = VBool $ a >= b

data LogicOp = LOr | LAnd

logicOp :: Value -> LogicOp -> Value -> Value
logicOp (VBool a) LOr (VBool b) = VBool $ a || b
logicOp (VBool a) LAnd (VBool b) = VBool $ a && b
logicOp _ _ _ = VNone

toStr :: Value -> Value
toStr (VInt a) = VStr $ show a
toStr (VBool True) = VStr "True"
toStr (VBool False) = VStr "False"
toStr (VStr a) = VStr a
toStr VNone = VStr "--none--"
toStr _ = VNone

printStr :: Value -> Context ()
printStr (VStr s) = liftIO $ putStrLn s
printStr _ = pure ()

isTrue :: Value -> Bool
isTrue (VBool a) = a
isTrue _ = False -- ERROR raiseErr

---------------------------------------
---------------- EXPR -----------------
---------------------------------------

getNthElem :: Value -> Value -> Context Value
getNthElem (VArr h t) (VInt 0) = pure h
getNthElem (VArr h t) (VInt n) = if n < 0 then pure VNone else getNthElem t (VInt $ n-1)
getNthElem _ _ = pure VNone

raiseErr :: Value
raiseErr = VNone

guardNonNegativeIndex :: Value -> Value
guardNonNegativeIndex (VInt n) = if n < 0
    then raiseErr
    else VInt n
guardNonNegativeIndex x = raiseErr

putNthElemAux :: Value -> Value -> Value -> Value
putNthElemAux (VArr h t) (VInt 0) v = VArr v t
putNthElemAux (VArr h VNone) (VInt n) v = VArr h tail
    where
    tail = putNthElemAux (VArr VNone VNone) (VInt $ n-1) v
putNthElemAux (VArr h t) (VInt n) v = VArr h (putNthElemAux t (VInt $ n-1) v)
putNthElemAux _ _ _ = raiseErr

putNthElem :: Ident -> Value -> Value -> Value -> Context Value
putNthElem name a b c = do
    assignValue name (putNthElemAux a (guardNonNegativeIndex b) c)
    pure VNone

takeFirst :: Value -> (Value, Value)
takeFirst (VArr h t) = (h, t)
takeFirst _ = (VNone, VNone)

evalExpr :: Expr -> Context Value
evalExpr (EVar name) = getValue name
evalExpr (EInt a) = pure $ VInt a
evalExpr ETrue = pure $ VBool True
evalExpr EFalse = pure $ VBool False
evalExpr (EString s) = pure $ VStr s
evalExpr (EParen expr) = evalExpr expr
evalExpr (EStringify expr) = toStr <$> evalExpr expr
evalExpr (EArr (x:xs)) = do
    val <- evalExpr x
    next <- evalExpr (EArr xs)
    pure $ VArr val next
evalExpr (EArr []) = pure VNone
evalExpr (EArrRead name expr) = do
    arr <- getValue name
    idx <- evalExpr expr
    getNthElem arr idx
evalExpr (Neg expr) = negateOp <$> evalExpr expr
evalExpr (Not expr) = negateOp <$> evalExpr expr
evalExpr (EMul expr1 op expr2) = mulOp <$> evalExpr expr1 <*> pure op <*> evalExpr expr2
evalExpr (EAdd expr1 op expr2) = addOp <$> evalExpr expr1 <*> pure op <*> evalExpr expr2
evalExpr (EComp expr1 op expr2) = compOp <$> evalExpr expr1 <*> pure op <*> evalExpr expr2
evalExpr (EAnd expr1 expr2) = logicOp <$> evalExpr expr1 <*> pure LAnd <*> evalExpr expr2
evalExpr (EOr expr1 expr2) = logicOp <$> evalExpr expr1 <*> pure LOr <*> evalExpr expr2
evalExpr (ECall expr args) = do
    fun <- evalExpr expr
    args' <- mapM evalExpr args
    callFun fun args'
evalExpr (EProc (PDec externs args (Blok blk))) = pure $ VProc externs args blk
evalExpr (ELamb (LDec typ args (Blok blk))) = pure $ VFun typ args blk

assertReturnedType :: BasicType -> Value -> Value
assertReturnedType Int (VInt x) = VInt x
assertReturnedType Str (VStr x) = VStr x
assertReturnedType Bool (VBool x) = VBool x
assertReturnedType Void VNone = VNone
assertReturnedType (Fun typ args) (VFun typ' args' _) = undefined
assertReturnedType (TProc _ externs args) (VProc externs' args' _) = undefined
assertReturnedType _ _ = raiseErr

callFun :: Value -> [Value] -> Context Value
callFun (VFun typ args blok) values = do
    addEnvFrame args
    assignValuesArgs args values
    res <- execStmts blok
    popEnv
    pure $ assertReturnedType typ res
callFun (VProc _ args blok) values = do
    addEnvFrame args
    assignValuesArgs args values
    execStmts blok
    popEnv
    pure VNone
callFun _ _ = pure raiseErr

---------------------------------------
---------------- STMT -----------------
---------------------------------------

execStmts :: [Stmt] -> Context Value
execStmts [] = pure VNone
execStmts (x:xs) = do
    ret <- execStmt x
    if ret == VNone then execStmts xs else pure ret


execStmt :: Stmt -> Context Value
execStmt (BStmt (Blok blok)) = do
    pushEnv
    res <- execStmts blok
    popEnv
    pure res
execStmt (DeclConst typ name expr) = do
    declare (FArg (Const typ) name)
    execStmt (Ass name expr)
execStmt (DeclMut typ name expr) = do
    declare (FArg (Mut typ) name)
    execStmt (Ass name expr)
execStmt (Ass name expr) = do
    val <- evalExpr expr
    assignValue name val
    pure VNone
execStmt (ArrAss name expr_idx expr_val) = do
    arr <- getValue name
    idx <- evalExpr expr_idx
    val <- evalExpr expr_val
    putNthElem name arr idx val
execStmt (Ret expr) = evalExpr expr
execStmt (If expr blok) = do
    val <- evalExpr expr
    if isTrue val then execHBlock blok else pure VNone
execStmt (IfElse expr blok blok_else) = do
    val <- evalExpr expr
    execHBlock $ if isTrue val then blok else blok_else
execStmt (While expr blok) = do
    val <- evalExpr expr
    if not $ isTrue val then pure VNone
    else do
        ret <- execHBlock blok
        if ret == VNone then execStmt (While expr blok) else pure ret
execStmt (Print expr) = do
    val <- evalExpr expr
    printStr val
    pure VNone
execStmt (SExp expr) = do
    evalExpr expr
    pure VNone
execStmt (For expr (PDec _ args (Blok blok))) = do
    arr <- evalExpr expr
    let (el, arr') = takeFirst arr in
        forAux el arr' (head args) blok
execStmt (FDefAlt _ name _ blok) = do
    fun <- evalExpr (ELamb blok)
    declare (FArg (Const Void) name)
    assignValue name fun
    pure VNone
execStmt (FDef _ name _ (FProc (PDec externs args (Blok blok)))) = do
    declare (FArg (Const Void) name)
    assignValue name (VProc externs args blok)
    pure VNone
execStmt (FDef typ name args (FBlok (Blok blok))) = do 
    declare (FArg (Const Void) name)
    assignValue name (VFun typ args blok)
    pure VNone
execStmt (FDef _ name _ (FVar p)) = do 
    fun <- evalExpr (EVar p)
    declare (FArg (Const Void) name)
    assignValue name fun
    pure VNone


forAux :: Value -> Value -> Arg -> [Stmt] -> Context Value
forAux VNone VNone arg stmts = pure VNone
forAux VNone arr arg stmts = let (el, arr') = takeFirst arr in forAux el arr' arg stmts
forAux el arr arg stmts = do
    addEnvFrame [arg]
    assignValueArg arg el
    res <- execStmts stmts
    popEnv
    if res /= VNone then pure res else forAux VNone arr arg stmts

execHBlock :: HBlock -> Context Value
execHBlock (AsStmt stmt) = execStmt stmt
execHBlock (AsProc blok) = execPBlock blok

execPBlock :: PBlock -> Context Value
execPBlock (FProc (PDec _ _ (Blok blok))) = execPBlock (FBlok (Blok blok))
execPBlock (FBlok (Blok blok)) = execStmt (BStmt (Blok blok))
execPBlock (FVar name) = execStmt (SExp (ECall (EVar name) []))

---------------------------------------
---------------- INIT -----------------
---------------------------------------

extractErrorCode :: Value -> Integer  
extractErrorCode (VInt err) = err 
extractErrorCode _ = 0

runProgramAux :: Program -> Context Integer
runProgramAux (MyProgram blok) = do 
    execStmts blok -- load all functions including main 
    err <- evalExpr (ECall (EVar (Ident "main")) []) -- call main and get error code
    pure $ extractErrorCode err

runProgram :: Program -> IO (Either String Integer)
runProgram p = runExceptT s 
    where s = evalStateT (runProgramAux p) emptyContext
    