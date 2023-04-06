import System.Environment (getProgName, getArgs)
import System.Directory (getCurrentDirectory, createDirectoryIfMissing)
import System.FilePath (normalise, (</>), takeDirectory, pathSeparator, makeRelative, (<.>))
import System.IO (withFile, IOMode (WriteMode), hPutStr)
import System.Exit (die)
import Root (findRootFromDirectory, replace, getPathByRoot)

printHelpAndExit :: IO a
printHelpAndExit = do
    progName <- getProgName
    die $ "Usage: " ++ progName ++ " <module> [comment]"

getFullInfoByRoot :: String -> FilePath -> IO (String, FilePath)
getFullInfoByRoot ('.' : mod) root =
    let rp = normalise $ replace '.' pathSeparator mod
    in do
        cwd <- getCurrentDirectory
        let fp = cwd </> rp
            fmod = replace pathSeparator '.' $ makeRelative root fp
        return (fmod, fp <.> "agda")
getFullInfoByRoot mod root =
    return (mod, getPathByRoot mod root <.> "agda")

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
                Nothing -> die "Cannot fine .agda-lib file pointing to the project root"
                Just p -> do
                    (name, path) <- getFullInfoByRoot mod p
                    createDirectoryIfMissing True $ takeDirectory path
                    withFile path WriteMode (\ hdl -> do
                        case rest of
                            [comment] -> hPutStr hdl $ "-- " ++ comment ++ "\n\n"
                            _ -> return ()
                        hPutStr hdl $ "{-# OPTIONS --without-K --safe #-}\n\nmodule " ++ name ++ " where")