module TypeCheckTest where

import Interpreter
import Par   (pProgram)


testGoodTypes :: Verbosity -> IO Bool 
testGoodTypes v = do
    putStrLn "No siema"
    run v pProgram
    pure True