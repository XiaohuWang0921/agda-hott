module Root where

import System.IO (Handle, hIsEOF, hGetLine, withFile, IOMode(ReadMode))
import System.FilePath (FilePath, (</>), isDrive, takeDirectory, normalise, pathSeparator, (<.>))
import Control.Applicative (liftA2, (<|>))
import System.Directory (listDirectory)

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
    agdaLibs <- ((p </>) <$>) . filter isAgdaLib <$> listDirectory p
    root <- foldr (liftA2 (<|>)) (return Nothing) $ (\ lib -> withFile lib ReadMode findRootFromAgdaLib) <$> agdaLibs
    case root of
        Nothing -> if isDrive p then return Nothing else findRootFromDirectory $ takeDirectory p
        Just rp -> return $ Just $ normalise $ p </> rp

replace :: (Eq a, Functor f) => a -> a -> f a -> f a
replace old new = fmap (\ x -> if x == old then new else x)

getPathByRoot :: String -> FilePath -> FilePath
getPathByRoot mod root = root </> replace '.' pathSeparator mod <.> "agda"