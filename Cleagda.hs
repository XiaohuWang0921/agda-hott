import Root (findRootFromDirectory, noAgdaLib)
import System.Directory (doesFileExist, doesDirectoryExist, removeFile, listDirectory, getCurrentDirectory)
import System.FilePath ((</>))
import Control.Monad (when)
import Data.Foldable (traverse_)

isOld :: FilePath -> Bool
isOld ".old" = True
isOld (_ : p) = isOld p
isOld [] = False

removeOld :: FilePath -> IO ()
removeOld p = do
    fileExists <- doesFileExist p
    when (fileExists && isOld p) $ removeFile p
    directoryExists <- doesDirectoryExist p
    when directoryExists $ do
        contents <- listDirectory p
        traverse_ (removeOld . (p </>)) contents

main :: IO ()
main = do
    cwd <- getCurrentDirectory
    root <- findRootFromDirectory cwd
    maybe noAgdaLib removeOld root