import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.Process

import AbsCPP
import LexCPP
import ParCPP
import ErrM
import PrintCPP

import TypeChecker
import CodeGenerator

-- driver

check :: String -> IO () 
check s = case pProgram (myLexer s) of
            Bad err  -> do putStrLn "SYNTAX ERROR"
                           putStrLn err
                           exitFailure 
            Ok  tree -> case typecheck tree of
                          Bad err -> do putStrLn "TYPE ERROR"
                                        putStrLn err
                                        exitFailure 
                          Ok t -> do
                            putStrLn $ printTree t
                            createFile $ compile "test" t

createFile :: String -> IO ()
createFile code = do
    writeFile "lab3.j" code
    system "jasmin lab3.j > /dev/null"
    system "java -cp . test"
    return ()

main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= check
            _      -> do putStrLn "Usage: lab2 <SourceFile>"
                         exitFailure
