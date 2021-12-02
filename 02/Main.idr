module Main

import System.File.ReadWrite
import Text.Lexer
import Text.Lexer.Tokenizer
import Text.Parser
import Text.Parser.Core

data Command = MkCommandForward Nat
             | MkCommandDown Nat
             | MkCommandUp Nat

namespace Input

  public export
  InputType : Type
  InputType = List1 Command

  data Token = MkTokenNewline
             | MkTokenWhitespace
             | MkTokenWord String
             | MkTokenNumber Nat

  tokenizer : Tokenizer Token
  tokenizer = match newline (const MkTokenNewline)
          <|> match spaces (const MkTokenWhitespace)
          <|> match alphas MkTokenWord
          <|> match digits (MkTokenNumber . cast)
  
  grammar : Grammar () Token True InputType
  grammar = do
    let grammarNewline = terminal "Newline" $ \ x =>
                         case x of
                              MkTokenNewline => Just ()
                              _ => Nothing
    let grammarWhitespace = terminal "Whitespace" $ \ x =>
                            case x of
                                 MkTokenWhitespace => Just ()
                                 _ => Nothing
    let grammarCommand = terminal "Command" $ \ x =>
                         case x of
                              MkTokenWord "forward" => Just $ MkCommandForward
                              MkTokenWord "down" => Just $ MkCommandDown
                              MkTokenWord "up" => Just $ MkCommandUp
                              _ => Nothing
    let grammarNumber = terminal "Number" $ \ x =>
                        case x of
                             MkTokenNumber n => Just n
                             _ => Nothing
    let grammarLine = grammarCommand <* grammarWhitespace <*> grammarNumber <* grammarNewline
    someTill eof grammarLine

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

record Coordinate where
  constructor MkCoordinate
  xPosition, depth : Integer

evalCommand : Command -> Coordinate -> Coordinate
evalCommand (MkCommandForward n) = { xPosition $= (+ natToInteger n) }
evalCommand (MkCommandDown n) = { depth $= (+ natToInteger n) }
evalCommand (MkCommandUp n) = { depth $= (+ negate (natToInteger n)) }

record SubmarineState where
  constructor MkSubmarineState
  aim, horizontalPosition, depth : Integer

evalCommand2 : Command -> SubmarineState -> SubmarineState
evalCommand2 (MkCommandForward n) subState = let x = natToInteger n
                                              in { horizontalPosition $= (+ x)
                                                 , depth $= (+ (subState.aim * x))
                                                 } subState
evalCommand2 (MkCommandDown n) subState = { aim $= (+ natToInteger n) } subState
evalCommand2 (MkCommandUp n) subState = { aim $= (+ negate (natToInteger n)) } subState

part1 : InputType -> IO ()
part1 input = do
  let finalCoordinate = foldl (flip evalCommand) (MkCoordinate 0 0) input
  printLn $ finalCoordinate.xPosition * finalCoordinate.depth
  pure ()

part2 : InputType -> IO ()
part2 input = do
  let finalCoordinate = foldl (flip evalCommand2) (MkSubmarineState 0 0 0) input
  printLn $ finalCoordinate.horizontalPosition * finalCoordinate.depth
  pure ()

main : IO ()
main = do
  input <- Input.input
  --printLn input
  part1 input
  part2 input
  pure ()
