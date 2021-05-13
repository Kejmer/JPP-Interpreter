
module StaticTypeChecker where

import Types
import ErrM
import Data.Map (Map, lookup, findMax, size, insert, member, empty)
import Control.Monad.State
import Data.Maybe (fromJust)

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

newtype ErrT m a = ErrT { runErrT :: m (Err a)}

instance (Monad m) => Monad (ErrT m) where 
    return = lift . return 
    x >>= f = ErrT $ do 
        v <- runErrT x
        case v of 
            Left err -> return (Left err)
            Right val -> runErrT (f val)

emptyEnv :: TypeEnv
emptyEnv = TypeEnv { parent_env = Nothing, local_env = Data.Map.empty }

-- Relation { domain = Set.empty, relation = Set.empty}
emptyContext :: TypeContext 
emptyContext = TypeContext { env = emptyEnv, store = Data.Map.empty }

getLocAux :: Ident -> TypeEnv -> Err Loc
getLocAux name env =
    let local = local_env env in
    if member name local
    -- then Ok fromJust . Data.Map.lookup name local
    then Ok 3
    else case parent_env env of
        Nothing -> Bad "Called variable has no defined type"
        Just parent -> getLocAux name parent

getLoc :: Ident -> Context (Err Loc)
getLoc name = do
    gets (getLocAux name . env)

-- getType :: Ident -> Context (Err Type)
-- getType context name = do
--     context <- get
--     loc <- getLoc name
--     pure (fromJust . Data.Map.lookup loc (store context))

-- 

checkProgram :: Program -> Err ()
checkProgram (Program tree) = evalState (typeCheckTree tree) emptyContext

typeCheckTree :: [Stmt] -> State TypeContext (Err ())
typeCheckTree tree = do 
    main <- locateMain tree
    
    
    pure (Ok ())

locateMainAux :: Stmt -> Bool
locateMainAux (FDef Int (Ident "main") [] _) = True 
locateMainAux _ = False  


locateMain :: [Stmt] -> Err Stmt
locateMain tree =
    let result = filter locateMainAux tree in
    case result of 
        x:_ -> Right x
        [] -> Left "Couldn't find entrypoint (int main)" 