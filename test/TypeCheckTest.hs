module TypeCheckTest where

import Runner 

type TestFun = Verbosity  -> IO (Err ())

negateResult :: IO (Err ()) -> IO (Err ())
negateResult res = do 
    result <- res
    pure $ case result of 
        Right x -> Left "Didn't detect error BUT IT SHOULD"
        Left _ -> Right () 

testBadTypes :: TestFun
testBadTypes v = negateResult $ runFileTypecheck v "bad/hello_types.spf"

testGoodTypes :: TestFun 
testGoodTypes v = runFileTypecheck v "good/hello_world.spf"
    
testDeclarations :: TestFun 
testDeclarations v = runFileTypecheck v "good/declarations.spf"

testReturnInProcGood :: TestFun 
testReturnInProcGood v = runFileTypecheck v "good/proc_extern.spf" 

testReturnInProcBad :: TestFun 
testReturnInProcBad v = negateResult $ runFileTypecheck v "bad/proc_extern.spf" 

testTypeShadowing :: TestFun 
testTypeShadowing v = runFileTypecheck v "good/type_shadowing.spf"

testFor :: TestFun 
testFor v = runFileTypecheck v "good/for.spf"