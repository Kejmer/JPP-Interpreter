module Interpreter where

import Types
import ErrM
import Control.Monad.State
import Data.Map (Map, lookup, findMax, size, insert, member, empty, (!))
import Data.Maybe (fromJust)

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
    | VBlock Block
    | VArr Value Value -- val + next // like a queue
    | VNone
type Context a = (StateT TypeContext IO) a

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
printStr (VStr a) = liftIO $ putStrLn s
printStr _ = pure ()


---------------------------------------
---------------- EXPR -----------------
---------------------------------------

getNthElem :: Value -> Value -> Context Value
getNthElem (VArr h t) (VInt 0) = pure h
getNthElem (VArr h t) (VInt n) = if n < 0 then pure VNone else getNthElem t (VInt n-1)
getNthElem _ _ = pure VNone

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
evalExpr (Neg expr) = negate <$> evalExpr expr
evalExpr (Not expr) = negate <$> evalExpr expr
evalExpr (EMul expr1 op expr2) = mulOp <$> evalExpr expr1 <*> pure op <*> evalExpr expr2
evalExpr (EAdd expr1 op expr2) = addOp <$> evalExpr expr1 <*> pure op <*> evalExpr expr2
evalExpr (EComp expr1 op expr2) = compOp <$> evalExpr expr1 <*> pure op <*> evalExpr expr2
evalExpr (EAnd expr1 expr2) = logicOp <$> evalExpr expr1 <*> pure LAnd <*> evalExpr expr2
evalExpr (EOr expr1 expr2) = logicOp <$> evalExpr expr1 <*> pure LOr <*> evalExpr expr2
evalExpr _ = pure VNone
-- evalExpr (EProc (PDec externs args (Blok blk))) = do
--     addEnvFrame args
--     typ <- typecheckBlock blk
--     popEnv
--     case typ of
--         Right x -> pure $ Ok $ buildProcType x externs args
--         Left y -> pure $ Left y
-- evalExpr (ELamb (LDec typ args (Blok blk))) = do
--     addEnvFrame args
--     typ' <- typecheckBlock blk
--     popEnv
--     case typ' of
--         Right x -> if x == typ then pure $ Ok $ buildFunType typ args
--             else pure $ Left $ "Missmatched function return type - expected " ++ show typ ++ " got " ++ show x
--         Left y -> pure $ Left y
-- evalExpr (ECall expr args) = do
--     typ <- evalExpr expr
--     args' <- mapM evalExpr args
--     evalCall typ args'








