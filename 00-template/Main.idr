module Main

import System.File.ReadWrite
import Text.Lexer
import Text.Lexer.Tokenizer
import Text.Parser
import Text.Parser.Core

namespace Input

  public export
  InputType : Type
  InputType = ?inputType

  data Token = MkTokenNewline

  tokenizer : Tokenizer Token
  tokenizer = match newline (const MkTokenNewline)
          <|> ?tokenize
  
  grammar : Grammar () Token True InputType
  grammar = do
    let grammarNewline = terminal "Newline" $ \ x =>
                         case x of
                              MkTokenNewline => Just ()
                              _ => Nothing
    ?grammarize

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

part1 : InputType -> IO ()
part1 input = do
  pure ()

part2 : InputType -> IO ()
part2 input = do
  pure ()

main : IO ()
main = do
  input <- Input.input
  printLn input
  part1 input
  part2 input
  pure ()
