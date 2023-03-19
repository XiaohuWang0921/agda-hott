import System.Environment (getProgName, getArgs)
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Traversable (for)
import System.Directory (getDirectoryContents, getCurrentDirectory)
import System.FilePath (joinPath, normalise, (</>), splitDirectories, isDrive, takeDirectory, pathSeparator, makeRelative, (<.>))
import System.IO (Handle, hGetLine, hIsEOF, withFile, IOMode (ReadMode, WriteMode), hPutStr)
import Control.Monad (join)
import Control.Applicative (Applicative (liftA2), Alternative ((<|>)))
import System.Exit (die)

printHelpAndExit :: IO a
printHelpAndExit = do
    progName <- getProgName
    die $ "Usage: " ++ progName ++ " <module> [comment]"

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

findRootFromAgdaLib :: Handle -> IO (Maybe FilePath)
findRootFromAgdaLib hdl = do
    eof <- hIsEOF hdl
    if eof then return Nothing else do
        line <- hGetLine hdl
        case extractRoot line of
            Just path -> do
                return $ Just path
            Nothing -> findRootFromAgdaLib hdl

findRootFromDirectory :: FilePath -> IO (Maybe FilePath)
findRootFromDirectory p = do
    agdaLibs <- ((p </>) <$>) . filter isAgdaLib <$> getDirectoryContents p
    root <- foldr (liftA2 (<|>)) (return Nothing) $ (\ lib -> withFile lib ReadMode findRootFromAgdaLib) <$> agdaLibs
    case root of
        Nothing -> if isDrive p then return Nothing else findRootFromDirectory $ takeDirectory p
        Just rp -> return $ Just $ normalise $ p </> rp

replace :: (Eq a, Functor f) => a -> a -> f a -> f a
replace old new = fmap (\ x -> if x == old then new else x)

getFullInfoByRoot :: String -> FilePath -> IO (String, FilePath)
getFullInfoByRoot ('.' : mod) root =
    let rp = normalise $ replace '.' pathSeparator mod
    in do
        cwd <- getCurrentDirectory
        let fp = cwd </> rp
            fmod = replace pathSeparator '.' $ makeRelative root fp
        return (fmod, fp <.> "agda")
getFullInfoByRoot mod root =
    return (mod, root </> replace '.' pathSeparator mod <.> "agda")

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
                    withFile path WriteMode (\ hdl -> do
                        case rest of
                            [comment] -> hPutStr hdl $ "-- " ++ comment ++ "\n\n"
                            _ -> return ()
                        hPutStr hdl $ "{-# OPTIONS --without-K --safe #-}\n\nmodule " ++ name ++ " where")