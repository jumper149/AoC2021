module Main

import System.File.ReadWrite
import Text.Lexer
import Text.Lexer.Tokenizer
import Text.Parser
import Text.Parser.Core

namespace Input
  data Token = MkTokenNewline
             | MkTokenNumber Nat

  tokenizer : Tokenizer Token
  tokenizer = match newline (const MkTokenNewline)
          <|> match digits (MkTokenNumber . cast)

  public export
  InputType : Type
  InputType = List1 Nat

  grammarNumber : Grammar () Token True Nat
  grammarNumber = terminal "Number" $ \ x =>
                  case x of
                       MkTokenNumber n => Just n
                       _ => Nothing

  grammarNewline : Grammar () Token True ()
  grammarNewline = terminal "Newline" $ \ x =>
                   case x of
                        MkTokenNewline => Just ()
                        _ => Nothing

  grammarLine : Grammar () Token True Nat
  grammarLine = grammarNumber <* grammarNewline

  grammar : Grammar () Token True InputType
  grammar = someTill eof grammarLine

  export
  input : IO InputType
  input = do
    readResult <- readFile "./input"
    inputString <- case readResult of
                Left err => do
                  printLn err
                  ?handleFileError
                Right x => pure x
    tokens <- case lex tokenizer inputString of
                   (x, (EndInput, _)) => pure x
                   (_, stopReason) => do
                     printLn stopReason
                     ?handleLexError
    case parse grammar tokens of
         Left err => do
           --printLn err
           ?handleParseError
         Right (result, rest) => do
           --printLn rest
           pure result
  input = ?input_rhs

countIncrements : Ord a => List1 a -> Nat
countIncrements (x ::: []) = 0
countIncrements (x ::: (y :: ys)) = if x < y
                                       then S $ countIncrements $ y ::: ys
                                       else countIncrements $ y ::: ys

main : IO ()
main = do
  input <- Input.input
  printLn input

  -- part 1
  printLn $ countIncrements input

  pure ()
