import System.Environment (getProgName, getArgs)
import System.Directory (getCurrentDirectory, createDirectoryIfMissing, doesFileExist)
import System.FilePath (takeDirectory)
import System.IO (withFile, IOMode (AppendMode), hPutStr)
import System.Exit (die)
import Root (findRootFromDirectory, getFullInfoByRoot, noAgdaLib)
import Control.Monad (when)

printHelpAndExit :: IO a
printHelpAndExit = do
    progName <- getProgName
    die $ "Usage: " ++ progName ++ " <module> [comment]"

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> printHelpAndExit
        (_ : _ : _ : _) -> printHelpAndExit
        (mod : rest) -> do
            cwd <- getCurrentDirectory
            root <- findRootFromDirectory cwd
            case root of
                Nothing -> noAgdaLib
                Just p -> do
                    (name, path) <- getFullInfoByRoot mod p
                    createDirectoryIfMissing True $ takeDirectory path
                    fileExists <- doesFileExist path
                    when fileExists $ die $ "Module " ++ name ++ " already exists"
                    withFile path AppendMode (\ hdl -> do
                        case rest of
                            [comment] -> hPutStr hdl $ "-- " ++ comment ++ "\n\n"
                            _ -> return ()
                        hPutStr hdl $ "{-# OPTIONS --without-K --safe #-}\n\nmodule " ++ name ++ " where")