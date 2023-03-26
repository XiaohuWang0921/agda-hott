import System.Environment (getProgName)
import System.Exit (die)

printHelpAndExit :: IO a
printHelpAndExit = do
    progName <- getProgName
    die $ "Usage: " ++ progName ++ " <old> <new>"