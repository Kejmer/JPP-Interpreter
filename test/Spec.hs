import qualified TypeCheckTest

main :: IO ()
main = testAll

testFeature :: String -> IO Bool -> IO ()
testFeature name succeed = do
    putStrLn $ "TESTING " ++ name ++ ":"
    good <- succeed
    putStrLn $ if good
        then "SUCCESS"
        else "FAILED"

testAll :: IO ()
testAll = do
    testFeature "Statyczne typowanie" TypeCheckTest.testGoodTypes 2