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
  case readResult of
       Left err => do
         putStrLn "Error reading file."
         printLn err
       Right inputString => do

         -- Lex input.
         case lex solution.tokenizer inputString of
              (tokens, (EndInput, _)) => do

                -- Parse input.
                case parse solution.grammar tokens of
                     Left err => do
                       printLn err
                     Right (result, rest) => do
                       putStrLn "=========="
                       putStrLn "Remaining tokens:"
                       printLn rest
                       putStrLn "=========="
                       putStrLn "Input:"
                       printLn result
                       putStrLn "=========="
                       putStrLn "Part 1:"
                       solution.part1 result
                       putStrLn "=========="
                       putStrLn "Part 2:"
                       solution.part2 result
                       putStrLn "=========="
                       pure ()

              (_, stopReason) => do
                putStrLn "Error lexing input."
                printLn stopReason

private
countLength' : List a -> (n ** Vect n a)
countLength' [] = (0 ** [])
countLength' (x :: xs) with (countLength' xs)
  _ | (n ** ys) = (S n ** x :: ys)

public export
countLength : Foldable f => f a -> (n ** Vect n a)
countLength = countLength' . toList

public export
exactLengths : (len : Nat) -> Traversable t => t (n ** Vect n a) -> Maybe (t (Vect len a))
exactLengths len xs = traverse (\ x => exactLength len x.snd) xs

public export
equalLengths : List1 (n ** Vect n a) -> Maybe (m ** (List1 (Vect m a)))
equalLengths ((len ** xs) ::: ys) = do
  list <- exactLengths len ys
  pure (len ** xs ::: list)

export
grammarEmbedMaybe : String -> Maybe a -> Grammar state tok False a
grammarEmbedMaybe msg Nothing = fail msg
grammarEmbedMaybe _ (Just x) = pure x
