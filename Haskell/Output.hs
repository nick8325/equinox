module Output where

import Form( Answer )

putInfo :: String -> IO ()
putInfo s = putStrLn s

putOfficial :: String -> IO ()
putOfficial s = putStrLn ("+++ " ++ s)

putResult :: Answer -> String -> IO ()
putResult ans "" = putOfficial ("RESULT: " ++ show ans)
putResult ans s  = putOfficial ("RESULT: " ++ show ans ++ " (" ++ s ++ ")")

putWarning :: String -> IO ()
putWarning s = putStrLn ("*** " ++ s)

putHeader :: String -> IO ()
putHeader s = putStrLn ("== " ++ s ++ " " ++ replicate (74 - length s) '=')

putSubHeader :: String -> IO ()
putSubHeader s = putStrLn ("-- " ++ s)
