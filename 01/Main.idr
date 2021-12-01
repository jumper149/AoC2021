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

countIncrements : Ord a => List1 a -> Nat
countIncrements (x ::: []) = 0
countIncrements (x ::: (y :: ys)) = if x < y
                                       then S $ countIncrements $ y ::: ys
                                       else countIncrements $ y ::: ys

record List3 a where
  constructor MkList3
  x0, x1, x2 : a
  xs : List a

fromList : List a -> Maybe (List3 a)
fromList (x0::x1::x2::xs) = Just $ MkList3 x0 x1 x2 xs
fromList _ = Nothing

groupMeasurements : List3 Nat -> List1 Nat
groupMeasurements (MkList3 x0 x1 x2 []) = (x0 + x1 + x2) ::: []
groupMeasurements (MkList3 x0 x1 x2 (x :: xs)) = (x0 + x1 + x2) `cons` groupMeasurements (MkList3 x1 x2 x xs)

main : IO ()
main = do
  input <- Input.input
  printLn input

  -- part 1
  printLn $ countIncrements input

  -- part 2
  let groupedMeasurements = case Main.fromList $ toList input of
                                 Nothing => ?inputTooShort
                                 Just xs => groupMeasurements xs
  printLn $ countIncrements groupedMeasurements

  pure ()
