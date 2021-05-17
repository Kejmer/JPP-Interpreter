
module StaticTypeChecker where

import Types
import ErrM
import Control.Applicative (Alternative(..))
import Data.Map (Map, lookup, findMax, size, insert, member, empty)
import Control.Monad.State
import Data.Maybe (fromJust)
import Data.Either

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
    }

type Context a = State TypeContext a

emptyEnv :: TypeEnv
emptyEnv = TypeEnv { parent_env = Nothing, local_env = Data.Map.empty }

emptyContext :: TypeContext
emptyContext = TypeContext { env = emptyEnv, store = Data.Map.empty }

getLocAux :: Ident -> TypeEnv -> Err Loc
getLocAux name env =
    let local = local_env env in
    if Data.Map.member name local
    then Ok (fromJust $ Data.Map.lookup name local)
    else case parent_env env of
        Nothing -> Bad "Called variable has no defined type"
        Just parent -> getLocAux name parent

getLoc :: Ident -> Context (Err Loc)
getLoc name = do
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
        store = store context
    }

popEnv :: Context ()
popEnv = do
    context <- get
    case parent_env $ env context of
        Nothing -> pure ()
        Just env -> put TypeContext {
            env = env,
            store = store context
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
        store = insert loc typ $ store context
    }


addEnvFrame :: [Arg] -> Context ()
addEnvFrame args = do
    pushEnv
    forM_ args declare

-----------------------------
------- INITIALIZING --------
-----------------------------


checkProgram :: Program -> Err ()
checkProgram (MyProgram tree) = evalState (typeCheckTree tree) emptyContext

typeCheckTree :: [Stmt] -> Context (Err ())
typeCheckTree tree = do
    main <- locateMainAndBuildContext tree (Bad "Couldn't find entrypoint (int main)")
    case main of 
        Left y -> pure $ Left y
        Right x -> startAddToContextAux <$> typecheckStmt x

isMain :: Stmt -> Bool
isMain (FDef Int (Ident "main") [] _) = True
isMain _ = False

startAddToContextAux :: Err BasicType -> Err ()
startAddToContextAux (Left y) = Left y
startAddToContextAux _ = Right ()

startAddToContext :: Stmt -> Context (Err ())
startAddToContext (DeclConst typ name expr) = startAddToContextAux <$> typecheckStmt (DeclConst typ name expr)
startAddToContext (DeclMut typ name expr) = startAddToContextAux <$> typecheckStmt (DeclMut typ name expr)
startAddToContext (FDef typ name args blok) = startAddToContextAux <$> typecheckStmt (FDef typ name args blok)
startAddToContext (FDefAlt typ name args blok) = startAddToContextAux <$> typecheckStmt (FDefAlt typ name args blok)
startAddToContext anything = pure $ Left $ "Unknown statement outside of main: " ++ show anything

locateMainAndBuildContext :: [Stmt] -> Err Stmt -> Context (Err Stmt)
locateMainAndBuildContext [] acc = pure acc
locateMainAndBuildContext (x:xs) acc = if isMain x
    then locateMainAndBuildContext xs (acc <|> Ok x)
    else do
        succeed <- startAddToContext x
        case succeed of
            Right _ -> locateMainAndBuildContext xs acc
            Left x -> return $ Left x


-----------------------------
------- STMT CHECKING -------
-----------------------------

normalizeReturnType :: Err BasicType -> Err BasicType -> Err BasicType
normalizeReturnType x y = do
    typ  <- x
    typ' <- y
    if typ == Void then y
    else if typ == typ' || typ' == Void then x
    else Left $ "Block returns two values of diffrent types " ++ show typ ++ " and " ++ show typ'

typecheckBlockAux :: [Stmt] -> Err BasicType -> Context (Err BasicType)
typecheckBlockAux [] acc = pure acc
typecheckBlockAux (x:xs) acc = do
    res <- typecheckStmt x
    case res of
        Left y -> pure res
        Right x -> typecheckBlockAux xs (normalizeReturnType acc res)


typecheckBlock :: [Stmt] -> Context (Err BasicType)
typecheckBlock x = do 
    pushEnv
    res <- typecheckBlockAux x (Ok Void)
    popEnv
    pure res

typecheckStmt :: Stmt -> Context (Err BasicType)
typecheckStmt (BStmt (Blok block)) = typecheckBlock block
typecheckStmt (DeclConst typ name expr) = do
    declare (FArg (Const typ) name)
    typ' <- assertBasicType typ expr
    pure $ case typ' of
        Right _ -> Ok Void
        Left y -> Left y
typecheckStmt (DeclMut typ name expr) = do
    declare (FArg (Mut typ) name)
    typ' <- assertBasicType typ expr
    pure $ case typ' of
        Right _ -> Ok Void
        Left y -> Left y
typecheckStmt (Ass name expr) = pure $ Ok Void -- UNDEFINED
typecheckStmt (ArrAss name expr1 expr2) = pure $ Ok Void -- UNDEFINED
typecheckStmt (Ret expr) = do 
    res <- evalType expr
    pure $ extractBasicType <$> res 

typecheckStmt (If expr hblok) = pure $ Ok Void -- UNDEFINED
typecheckStmt (IfElse expr hblok_if hblok_else) = pure $ Ok Void -- UNDEFINED
typecheckStmt (While expr hblock) = pure $ Ok Void -- UNDEFINED
typecheckStmt (Print expr) = do
    typ <- assertBasicType Str expr
    case typ of
        Right _ -> pure $ Ok Void
        Left y -> pure $ Left "Tried to print not a string"
typecheckStmt (For expr (PDec externs args (Blok blk))) = do
    arr_typ <- evalType expr
    addEnvFrame args
    ret_typ <- typecheckBlock blk
    popEnv
    pure $ if length args /= 1
    then Left "Proc passed to for has too many arguments"
    else case assertTypeFitsArray arr_typ (head $ argsToType args) of
        Right x -> ret_typ
        Left y -> Left y

typecheckStmt (SExp expr) = pure $ Ok Void -- UNDEFINED
typecheckStmt (FDef typ name args (FProc p)) = pure $ Ok Void -- UNDEFINED
typecheckStmt (FDef typ name args (FBlok (Blok blok))) = do 
    addEnvFrame args 
    declare (FArg (buildFunType typ args) name)
    res <- typecheckBlock blok 
    popEnv 
    pure $ case res of 
        Left y -> Left y
        Right x -> if x == typ then Ok Void 
            else Left $ "Missmatched return types " ++ show x ++ " and " ++ show typ
typecheckStmt (FDef typ name args (FVar p)) = pure $ Ok Void -- UNDEFINED
typecheckStmt (FDefAlt typ name args blok) = pure $ Ok Void -- UNDEFINED

extractArrayType :: BasicType -> Err BasicType
extractArrayType (Arr x) = pure x
extractArrayType x = Left $ show x ++ " is not an Array!"

assertTypeFitsArray :: Err Type -> Type -> Err ()
assertTypeFitsArray arr' typ = do
    arr <- arr' >>= extractArrayType . extractBasicType
    if arr == extractBasicType typ
    then pure ()
    else Left $ "Proc arg type and array type missmatch: " ++ show arr ++ " and " ++ show (extractBasicType typ)


-----------------------------
----- TYPE EVALUTATION ------
-----------------------------

missmatchedTypes :: (Show a) => Err a -> Err a -> Err a
missmatchedTypes typ1 typ2 = Left $ "Missmatched types. Expected " ++ show typ1 ++ " got " ++ show typ2

extractBasicType :: Type -> BasicType
extractBasicType (MutRef x) = x
extractBasicType (Ref x) = x
extractBasicType (Mut x) = x
extractBasicType (Const x) = x

assertType :: Type -> Expr -> Context (Err Type)
assertType typ expr = do
    next_type <- evalType expr
    if next_type == Ok typ
    then pure next_type
    else pure $ missmatchedTypes (Ok typ) next_type

assertMutableType :: BasicType -> Expr -> Context (Err Type)
assertMutableType typ expr = do
    typ1 <- assertType (MutRef typ) expr
    typ2 <- assertType (Mut typ) expr
    pure $ typ1 <|> typ2

assertBasicType :: BasicType -> Expr -> Context (Err Type)
assertBasicType typ expr = do
    typ1 <- assertType (Ref typ) expr
    typ2 <- assertType (MutRef typ) expr
    typ3 <- assertType (Mut typ) expr
    typ4 <- assertType (Const typ) expr
    pure $ typ1 <|> typ2 <|> typ3 <|> typ4

evalTypeArr :: Err Type -> [Expr] -> Context (Err Type)
evalTypeArr typ (x:xs) = do
    next_type <- evalType x
    if next_type == typ
    then evalTypeArr typ xs
    else pure $ missmatchedTypes typ next_type
evalTypeArr typ [] = do 
    pure $ case extractBasicType <$> typ of 
        Right x -> Ok $ Const (Arr x) 
        Left y -> Left y 

assertSameBasicType :: Err Type -> Err Type -> Err BasicType
assertSameBasicType typ1 typ2 = do
    typ1' <- extractBasicType <$> typ1
    typ2' <- extractBasicType <$> typ2
    if typ1' == typ2'
    then pure typ1'
    else missmatchedTypes (Ok typ1') (Ok typ2')

assertArrayAux :: BasicType -> Err Type
assertArrayAux (Arr typ) = pure $ Const typ
assertArrayAux _ = Left "It is not an array"

assertArray :: Err Type -> Err Type
assertArray typ = typ >>= assertArrayAux . extractBasicType

evalType :: Expr -> Context (Err Type)
evalType (EVar name) = getType name
evalType (EInt _) = pure $ Ok $ Const Int
evalType ETrue = pure $ Ok $ Const Bool
evalType EFalse = pure $ Ok $ Const Bool
evalType (EString _) = pure $ Ok $ Const Str
evalType (EParen expr) = evalType expr
evalType (EProc (PDec externs args (Blok blk))) = do
    addEnvFrame args
    typ <- typecheckBlock blk
    popEnv
    case typ of
        Right x -> pure $ Ok $ buildProcType x externs args
        Left y -> pure $ Left y
evalType (ELamb (LDec typ args (Blok blk))) = do
    typ' <- typecheckBlock blk
    case typ' of
        Right x -> if x == typ then pure $ Ok $ buildFunType typ args
            else pure $ Left $ "Missmatched function return type - expected " ++ show typ ++ " got " ++ show x
        Left y -> pure $ Left y
evalType (ECall expr args) = do
    typ <- evalType expr
    args' <- mapM evalType args
    evalCall typ args'
evalType (EStringify expr) = evalsToAnyBasicType expr [Str, Int, Bool, Void]
evalType (EArr (x:xs)) = do
    typ <- evalType x
    case typ of
        Right _ -> evalTypeArr typ xs
        Left y -> pure $ Left $ "Failed parsing array definition: " ++ y
evalType (EArr []) = pure $ Bad "Array definition cannot be empty"
evalType (EArrRead name expr) = do
    idx <- assertBasicType Int expr
    arr <- getType name
    pure $ if isLeft idx
    then Left $ "Array index is not of type Int, got: " ++ show idx
    else assertArray arr
evalType (Neg expr) = assertBasicType Int expr
evalType (Not expr) = assertBasicType Bool expr
evalType (EMul expr1 _ expr2) = evalTypesOpAux expr1 expr2 [Int] id
evalType (EAdd expr1 Plus expr2) = evalTypesOpAux expr1 expr2 [Int, Str] id
evalType (EAdd expr1 Minus expr2) = evalTypesOpAux expr1 expr2 [Int] id
evalType (EComp expr1 Eq expr2) = evalTypesOpAux expr1 expr2 [Str, Int, Bool, Void] (const Bool)
evalType (EComp expr1 NEq expr2) = evalType (EComp expr1 Eq expr2)
evalType (EComp expr1 _ expr2) = evalTypesOpAux expr1 expr2 [Int] (const Bool)
evalType (EAnd expr1 expr2) = evalTypesOpAux expr1 expr2 [Bool] (const Bool)
evalType (EOr expr1 expr2) = evalType (EAnd expr1 expr2)


argsToTypeAux :: Arg -> Type
argsToTypeAux (FArg typ _) = typ

argsToType :: [Arg] -> [Type]
argsToType = map argsToTypeAux

buildFunType :: BasicType -> [Arg] -> Type
buildFunType typ args = Const $ Fun typ (argsToType args)

buildProcType :: BasicType -> [Arg] -> [Arg] -> Type
buildProcType typ externs args = Const $ TProc typ externs (argsToType args)

evalCall :: Err Type -> [Err Type] -> Context (Err Type)
evalCall fun args = do
    case fun of
        Left y -> pure $ Left y
        Right fun_type ->
            if null errs
            then funTypeEqualsArgs (extractBasicType fun_type) goods
            else pure $ Left $ head errs
            where
                goods = rights args
                errs = lefts args

assertExternsExistAux :: Arg -> Context (Err ())
assertExternsExistAux (FArg typ name) = do
    typ' <- evalType (EVar name)
    pure $ case typ' of
        Left _ -> Left $ "Calling a proc block requires " ++ show name ++ " variable to be of type " ++ show typ
        Right x -> if x == typ then Right ()
            else Left $ "Calling a proc block requires " ++ show name ++ " variable to be of type " ++ show typ

assertExternsExist :: [Arg] -> Context (Err ())
assertExternsExist [] = pure $ Ok ()
assertExternsExist (x:xs) = do
    err <- assertExternsExistAux x
    case err of
        Right _ -> assertExternsExist xs
        Left y -> pure err

funTypeEqualsArgs :: BasicType -> [Type] -> Context (Err Type)
funTypeEqualsArgs (Fun typ expected) args =
    pure $ if expected == args then Ok $ Const typ
    else Left "Arguments in function call have missmatched types."
funTypeEqualsArgs (TProc _ externs expected) args = do
    assertExternsExist externs
    funTypeEqualsArgs (Fun Void expected) args
funTypeEqualsArgs typ _ = pure $ Left $ "This type is not callable " ++ show typ

evalsToAnyBasicType :: Expr -> [BasicType] -> Context (Err Type)
evalsToAnyBasicType expr [] = pure $ Left "This type is not stringifyable"
evalsToAnyBasicType expr (x:xs) = do
    res <- assertBasicType x expr
    if isLeft res then evalsToAnyBasicType expr xs
    else pure $ Right $ Const Str

evalTypesOpAux :: Expr -> Expr -> [BasicType] -> (BasicType -> BasicType) -> Context (Err Type)
evalTypesOpAux expr1 expr2 xs expected = do
    typ1 <- evalType expr1
    typ2 <- evalType expr2
    let typ = assertSameBasicType typ1 typ2 in
        pure $ case typ of
            Left y -> Left y
            Right x -> if x `elem` xs
                then Right $ Const (expected x)
                else Left $ "Type " ++ show x ++ " doesn't support that operation."


------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------GRAVEYARD------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------



-- startAddToContext :: Stmt -> Context (Err ())
-- startAddToContext BStmt Block
-- startAddToContext DeclConst BasicType Ident Expr
-- startAddToContext DeclMut BasicType Ident Expr
-- startAddToContext Ass Ident Expr
-- startAddToContext ArrAss Ident Expr Expr
-- startAddToContext Ret Expr
-- startAddToContext If Expr HBlock
-- startAddToContext IfElse Expr HBlock HBlock
-- startAddToContext While Expr HBlock
-- startAddToContext Print Expr
-- startAddToContext For Expr Proc
-- startAddToContext SExp Expr
-- startAddToContext FDef BasicType Ident ([Arg]) PBlock
-- startAddToContext FDefAlt BasicType Ident ([Arg]) Lambda
-- -- 


-- evalType EComp expr1 op expr2 = do
--     typ1 <- assertBasicType Int expr1
--     typ2 <- assertBasicType Int expr2
--     if isLeft typ1 || isLeft typ2
--     then Left "Can't compare " ++ show typ1 ++ " and " ++ show typ2
--     else Const Bool
-- evalType EAnd expr1 expr2 = do
--     typ1 <- assertBasicType Bool expr1
--     typ2 <- assertBasicType Bool expr2
--     if isLeft typ1 || isLeft typ2
--     then Left "Both variables should be boolean, got: " ++ show typ1 ++ " and " ++ show typ2
--     else Const Bool
-- evalType EMul expr1 _ expr2 = do
--     typ1 <- assertBasicType Int expr1
--     typ2 <- assertBasicType Int expr2
--     pure $ if isLeft typ1 || isLeft typ2
--     then Left "Can't multiply " ++ show typ1 ++ " and " ++ show typ2
--     else Const Int