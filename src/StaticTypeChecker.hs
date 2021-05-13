
module StaticTypeChecker where

import Types
import ErrM
import Data.Map (Map, lookup, findMax, size, insert, member)
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

checkProgram :: Program -> State TypeContext Bool
checkProgram = undefined
