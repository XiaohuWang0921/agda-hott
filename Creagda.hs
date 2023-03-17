import System.Environment (getProgName)
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Traversable (for)
import System.Directory (getDirectoryContents, getCurrentDirectory)
import System.FilePath (joinPath, normalise, (</>), splitDirectories, isDrive, takeDirectory, dropTrailingPathSeparator)
import System.IO (Handle, hGetLine, hIsEOF, withFile, IOMode (ReadMode))
import Control.Monad (join)
import Control.Applicative

printHelp :: IO ()
printHelp = do
    progName <- getProgName
    putStrLn $ "Usage: " ++ progName ++ " <module> [comment]"

extractRoot :: String -> Maybe String
extractRoot s = end . init <$> (include (init s) >>= colon . init)
    where
        init :: String -> String
        init (' ' : s) = init s
        init s = s

        include :: String -> Maybe String
        include ('i':'n':'c':'l':'u':'d':'e':s) = Just s
        include _ = Nothing

        colon :: String -> Maybe String
        colon (':' : s) = Just s
        colon _ = Nothing

        end :: String -> String
        end [] = []
        end (' ' : s) = case end s of
            [] -> []
            t -> ' ' : t
        end (c : s) = c : end s

isAgdaLib :: String -> Bool
isAgdaLib ".agda-lib" = True
isAgdaLib (_ : s) = isAgdaLib s
isAgdaLib [] = False

findRelativeRootFromAgdaLib :: Handle -> IO (Maybe FilePath)
findRelativeRootFromAgdaLib hdl = do
    eof <- hIsEOF hdl
    if eof then return Nothing else do
        line <- hGetLine hdl
        case extractRoot line of
            Just path -> do
                return $ Just path
            Nothing -> findRelativeRootFromAgdaLib hdl

findRootFromDirectory :: FilePath -> IO (Maybe FilePath)
findRootFromDirectory p = do
    agdaLibs <- ((p </>) <$>) . filter isAgdaLib <$> getDirectoryContents p
    root <- foldr (liftA2 (<|>)) (return Nothing) $ (\ lib -> withFile lib ReadMode findRelativeRootFromAgdaLib) <$> agdaLibs
    case root of
        Nothing -> if isDrive p then return Nothing else findRootFromDirectory $ takeDirectory p
        Just rp -> return $ Just $ dropTrailingPathSeparator $ normalise $ p </> rp