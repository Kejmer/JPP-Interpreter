module Main where

import System.Environment ( getArgs, getProgName )
import Par   ( pProgram, myLexer )

import Runner

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    -- []         -> getContents >>= run 0 pProgram
    -- "-s":fs    -> mapM_ (runFile 0 pProgram) fs
    fs         -> mapM_ (runFile 0 pProgram) fs

