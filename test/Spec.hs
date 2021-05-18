import qualified TypeCheckTest
import Runner (Err)

main :: IO ()
main = testAll

unwrapResult :: IO (Err ()) -> IO String
unwrapResult result = do 
    res <- result 
    case res of 
        Right _ -> pure "SUCCESS"
        Left x -> pure $ "FAILED: " ++ x

testFeature :: String -> IO (Err ()) -> IO ()
testFeature name result = do
    putStrLn $ "TESTING " ++ name ++ ":"
    msg <- unwrapResult result
    putStrLn msg

printBlock :: IO ()
printBlock = do 
    putStrLn ""
    putStrLn ""
    putStrLn "------------------------------------------------------------------"
    putStrLn "------------------------------------------------------------------"
    putStrLn "------------------------------------------------------------------"
    putStrLn "------------------------------------------------------------------"
    putStrLn ""
    putStrLn ""
    

testAll :: IO ()
testAll = do
    printBlock
    testFeature "Statyczne typowanie - hello world" (TypeCheckTest.testGoodTypes 0)
    testFeature "Statyczne typowanie - zly return type" (TypeCheckTest.testBadTypes 0)
    testFeature "Statyczne typowanie - deklaracje" (TypeCheckTest.testDeclarations 0)
    testFeature "Statyczne typowanie - petla for" (TypeCheckTest.testFor 0)
    testFeature "Statyczne typowanie - return w procesie" (TypeCheckTest.testReturnInProcGood 0)
    testFeature "Statyczne typowanie - brak extern" (TypeCheckTest.testReturnInProcBad 0)
    testFeature "Statyczne typowanie - type shadowing" (TypeCheckTest.testTypeShadowing 0)

    

    printBlock