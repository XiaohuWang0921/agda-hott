import System.Environment (getProgName, getArgs)
import System.Exit (die)
import System.Directory (doesFileExist, doesDirectoryExist, createDirectoryIfMissing, renameFile, listDirectory, removeDirectoryRecursive, renameDirectory, getCurrentDirectory)
import System.FilePath (takeDirectory, (</>), (<.>))
import Root (findRootFromDirectory)

printHelpAndExit :: IO a
printHelpAndExit = do
    progName <- getProgName
    die $ "Usage: " ++ progName ++ " <old> <new>"

movePath :: FilePath -> FilePath -> IO ()
movePath old new = do
    fileExists <- doesFileExist old
    directoryExists <- doesDirectoryExist old
    if fileExists then
        createDirectoryIfMissing True $ takeDirectory new
        renameFile old new
    else if directoryExists then
        newDirectoryExists <- doesDirectoryExist new^
        if newDirectoryExists then
            contents <- listDirectory old
            let newOlds = (old </>) <$> contents
                newNews = (new </>) <$> contents
            foldr (>>) (return ()) $ zipWith movePath newOlds newNews
            removeDirectoryRecursive old
        else
            createDirectoryIfMissing True $ takeDirectory new
            renameDirectory old new
    else
        return ()

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
        _ -> printHelpAndExit