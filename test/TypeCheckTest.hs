module TypeCheckTest where

import Interpreter
import Par   (pProgram)


testGoodTypes :: Verbosity -> IO Bool 
testGoodTypes v = do
    putStrLn "No siema"
    runFile v pProgram "good/hello_world.spf"
    pure True