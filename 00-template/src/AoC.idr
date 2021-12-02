module AoC

import Generics.Derive
import System.File.ReadWrite
import public Text.Lexer
import public Text.Lexer.Tokenizer
import public Text.Parser
import public Text.Parser.Core

%language ElabReflection

%runElab (derive "ParsingError" [ Meta, Show ])

public export
record AoCSolution tokenType inputType where
  constructor MkAoCSolution
  inputFilePath : String
  tokenizer : Tokenizer tokenType
  grammar : Grammar () tokenType True inputType
  part1 : inputType -> IO ()
  part2 : inputType -> IO ()

export
solveAoC : Show tokenType => Show inputType => AoCSolution tokenType inputType -> IO ()
solveAoC solution = do

  -- Read file.
  readResult <- readFile solution.inputFilePath
  inputString <- case readResult of
              Left err => do
                printLn err
                ?handleFileError
              Right x => pure x

  -- Lex input.
  tokens <- case lex solution.tokenizer inputString of
                 (x, (EndInput, _)) => pure x
                 (_, stopReason) => do
                   printLn stopReason
                   ?handleLexError

  -- Parse input.
  input <- case parse solution.grammar tokens of
                Left err => do
                  printLn err
                  ?handleParseError
                Right (result, rest) => do
                  printLn rest
                  pure result

  putStrLn "=========="
  putStrLn "Input:"
  print input
  putStrLn "=========="
  putStrLn "Part 1:"
  solution.part1 input
  putStrLn "=========="
  putStrLn "Part 2:"
  solution.part2 input
  putStrLn "=========="
  pure ()
