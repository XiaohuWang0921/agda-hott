import System.Environment (getProgName, getArgs)
import System.Exit (die)
import System.Directory (getCurrentDirectory, doesFileExist)
import Root (noAgdaLib, findRootFromDirectory, getFullInfoByRoot)
import Control.Monad (when)
import System.Process (callCommand)

printHelpAndExit :: IO a
printHelpAndExit = do
    progName <- getProgName
    die $ "Usage: " ++ progName ++ " <module>"

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> printHelpAndExit
        (_ : _ : _) -> printHelpAndExit
        [mod] -> do
            cwd <- getCurrentDirectory
            root <- findRootFromDirectory cwd
            case root of
                Nothing -> noAgdaLib
                Just p -> do
                    (name, path) <- getFullInfoByRoot mod p
                    fileExists <- doesFileExist path
                    if fileExists
                        then callCommand $ "emacs " ++ path
                        else die $ "Module " ++ name ++ " does not exist\n Try run `Creagda " ++ name ++ "` first"