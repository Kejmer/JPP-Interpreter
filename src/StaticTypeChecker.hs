
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

type Loc = Integer
data TypeEnv = TypeEnv
    { parent_env :: Maybe TypeEnv
    , local_env :: Map Ident Loc
    }

data TypeContext = TypeContext
    { env :: TypeEnv
    , store :: Map Loc Type
    }

type Context a = State TypeContext a
-- type Context a = StateT TypeContext Err a

-- newtype ErrT m a = ErrT { runErrT :: m (Err a)}

-- instance (Monad m) => Monad (ErrT m) where 
--     return = lift . return 
--     x >>= f = ErrT $ do 
--         v <- runErrT x
--         case v of 
--             Left err -> return (Left err)
--             Right val -> runErrT (f val)

emptyEnv :: TypeEnv
emptyEnv = TypeEnv { parent_env = Nothing, local_env = Data.Map.empty }

emptyContext :: TypeContext
emptyContext = TypeContext { env = emptyEnv, store = Data.Map.empty }

getLocAux :: Ident -> TypeEnv -> Err Loc
getLocAux name env =
    let local = local_env env in
    if Data.Map.member name local
    then Ok (fromJust $ Data.Map.lookup name local)
    -- then Ok 3x
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


checkProgram :: Program -> Err ()
checkProgram (Program tree) = evalState (typeCheckTree tree) emptyContext

typeCheckTree :: [Stmt] -> Context (Err ())
typeCheckTree tree = do
    main <- locateMainAndBuildContext tree (Bad "Couldn't find entrypoint (int main)")
    pure (Bad $ show main)

-----------------------------
------- INITIALIZING --------
-----------------------------




isMain :: Stmt -> Bool
isMain (FDef Int (Ident "main") [] _) = True
isMain _ = False

startAddToContext :: Stmt -> Context (Err ())
-- startAddToContext DeclConst BasicType Ident Expr = 
-- startAddToContext DeclMut BasicType Ident Expr
-- startAddToContext FDef BasicType Ident ([Arg]) PBlock
-- startAddToContext FDefAlt BasicType Ident ([Arg]) Lambda
-- startAddToContext anything = Left $ "Unknown statement outside of main: " ++ show anything
startAddToContext = undefined

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
    else Left "Block returns two values of diffrent types " ++ show typ ++ " and " ++ show typ'

typecheckBlockAux :: [Stmt] -> Err BasicType -> Context (Err BasicType)
typecheckBlockAux [] acc = pure acc
typecheckBlockAux (x:xs) acc = do
    res <- typecheckStmt x
    case res of
        Left y -> pure res
        Right x -> typecheckBlockAux xs (normalizeReturnType acc x)


typecheckBlock :: [Stmt] -> Context (Err BasicType)
typecheckBlock = undefined

typecheckStmt :: Stmt -> Context (Err BasicType)
typecheckStmt (BStmt (Blok block)) = undefined
typecheckStmt (DeclConst typ name expr) = undefined
typecheckStmt (DeclMut typ name expr) = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined
typecheckStmt () = undefined


-- BStmt Block
--     | DeclConst BasicType Ident Expr
--     | DeclMut BasicType Ident Expr
--     | Ass Ident Expr
--     | ArrAss Ident Expr Expr
--     | Ret Expr
--     | If Expr HBlock
--     | IfElse Expr HBlock HBlock
--     | While Expr HBlock
--     | Print Expr
--     | For Expr Proc
--     | SExp Expr
--     | FDef BasicType Ident [Arg] PBlock
--     | FDefAlt BasicType Ident [Arg] Lambda







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
evalTypeArr typ [] = pure typ

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
evalType (EProc (PDec externs args blk)) = pure $ Ok $ buildProcType externs args
evalType (ELamb (LDec typ args blk)) = pure $ Ok $ buildFunType typ args
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

buildProcType :: [Arg] -> [Arg] -> Type
buildProcType externs args = Const $ Proc Void externs (argsToType args)

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
funTypeEqualsArgs (Proc typ externs expected) args = do 
    assertExternsExist externs
    funTypeEqualsArgs (Fun typ expected) args
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