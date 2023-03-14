import System.Environment (getProgName)

printHelp :: IO ()
printHelp = do
    progName <- getProgName
    putStrLn $ "Usage: " ++ progName ++ " <module> [comment]"