import System.Environment (getProgName, getArgs)
import System.Exit (die)
import System.Directory (doesFileExist, doesDirectoryExist, createDirectoryIfMissing, renameFile, listDirectory, removeDirectoryRecursive, renameDirectory, getCurrentDirectory, doesPathExist, removeDirectory)
import System.FilePath (takeDirectory, (</>), (<.>))
import Root (findRootFromDirectory, getPathByRoot)
import System.IO (withFile, IOMode (ReadMode, WriteMode), hGetContents, hPutStr)
import Control.Monad (when, zipWithM_, filterM)

printHelpAndExit :: IO a
printHelpAndExit = do
    progName <- getProgName
    die $ "Usage: " ++ progName ++ " <old> <new>"

movePath :: FilePath -> FilePath -> IO ()
movePath old new = do
    fileExists <- doesFileExist old
    when fileExists $ do
        createDirectoryIfMissing True $ takeDirectory new
        renameFile old new
    directoryExists <- doesDirectoryExist old
    when directoryExists $ do
        newDirectoryExists <- doesDirectoryExist new
        if newDirectoryExists
            then do
                contents <- listDirectory old
                let newOlds = (old </>) <$> contents
                    newNews = (new </>) <$> contents
                zipWithM_ movePath newOlds newNews
                removeDirectoryRecursive old
            else do
                createDirectoryIfMissing True $ takeDirectory new
                renameDirectory old new

replaceSubstring :: String -> String -> String -> String
replaceSubstring old new = snd . replacePrefix old new
    where
        replacePrefix :: String -> String -> String -> (Bool, String)
        replacePrefix [] newPrefix s = (True, newPrefix ++ replaceSubstring old new s)
        replacePrefix _ _ "" = (False, "")
        replacePrefix (x : xs) newPrefix (c : s)
            | x == c = case replacePrefix xs newPrefix s of
                (True, newS) -> (True, newS)
                (False, newS) -> (False, c : newS)
            | otherwise = (False, c : replaceSubstring old new s)

replaceFile :: String -> String -> FilePath -> FilePath -> IO ()
replaceFile oldS newS oldF newF =
    withFile oldF ReadMode (\ oldH ->
    withFile newF WriteMode (\ newH -> do
        contents <- hGetContents oldH
        hPutStr newH $ replaceSubstring oldS newS contents))

getNewPath :: FilePath -> IO FilePath
getNewPath old =
    let new = old <.> "old"
    in do
        pathExists <- doesPathExist new
        if pathExists then getNewPath new else return new

isAgda :: FilePath -> Bool
isAgda ".agda" = True
isAgda (_ : p) = isAgda p
isAgda [] = False

replaceAllAgdas :: String -> String -> FilePath-> IO ()
replaceAllAgdas old new root = do
    contents <- ((root </>) <$>) <$> listDirectory root
    let agdas = filter isAgda contents
    olds <- traverse getNewPath agdas
    zipWithM_ renameFile agdas olds
    zipWithM_ (replaceFile old new) olds agdas
    dirs <- filterM doesDirectoryExist contents
    mapM_ (replaceAllAgdas old new) dirs

main :: IO ()
main = do
    args <- getArgs
    case args of
        [old, new] -> do
            cwd <- getCurrentDirectory
            root <- findRootFromDirectory cwd
            case root of
                Nothing -> die "Cannot fine .agda-lib file pointing to the project root"
                Just p -> do
                    let oldDir = getPathByRoot old p
                        oldFile = oldDir <.> "agda"
                        newDir = getPathByRoot new p
                        newFile = newDir <.> "agda"
                    movePath oldDir newDir
                    movePath oldFile newFile
                    replaceAllAgdas old new p
        _ -> printHelpAndExit