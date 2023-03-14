import System.Environment (getProgName)

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