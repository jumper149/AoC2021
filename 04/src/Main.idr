module Main

import AoC
import Generics.Derive
%language ElabReflection

Number : Type
Number = Integer

Board : Type
Board = Vect 5 $ Vect 5 $ Number

-- Input.
InputType : Type
InputType = (List1 Number, List1 Board)

-- Lexer.
data Token = MkTokenNewline
           | MkTokenWhitespace
           | MkTokenComma
           | MkTokenNumber Nat
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match spaces (const MkTokenWhitespace)
        <|> match (is ',') (const MkTokenComma)
        <|> match digits (MkTokenNumber . cast)

-- Parser.
grammarNewline : Grammar () Token True ()
grammarNewline = terminal "Newline" $ \ x =>
                 case x of
                      MkTokenNewline => Just ()
                      _ => Nothing
grammarWhitespace : Grammar () Token True ()
grammarWhitespace = terminal "Whitespace" $ \ x =>
                    case x of
                         MkTokenWhitespace => Just ()
                         _ => Nothing
grammarComma : Grammar () Token True ()
grammarComma = terminal "Comma" $ \ x =>
               case x of
                    MkTokenComma => Just ()
                    _ => Nothing
grammarNumber : Grammar () Token True Number
grammarNumber = terminal "Number" $ \ x =>
                case x of
                     MkTokenNumber x => Just $ natToInteger x
                     _ => Nothing
--grammarFromList : (n : Nat) -> List a -> Grammar state tok False (Vect n a)
--grammarFromList n xs = case toVect n xs of
--                            Nothing => fail "Expected n numbers."
--                            Just ys => pure ys
grammarRow : Grammar () Token True (Vect 5 Number)
grammarRow = do
  x1 <- optional grammarWhitespace *> grammarNumber
  x2 <- grammarWhitespace *> grammarNumber
  x3 <- grammarWhitespace *> grammarNumber
  x4 <- grammarWhitespace *> grammarNumber
  x5 <- grammarWhitespace *> grammarNumber
  pure [x1,x2,x3,x4,x5]
grammarBoard : Grammar () Token True Board
grammarBoard = do
  grammarNewline
  y1 <- grammarRow <* grammarNewline
  y2 <- grammarRow <* grammarNewline
  y3 <- grammarRow <* grammarNewline
  y4 <- grammarRow <* grammarNewline
  y5 <- grammarRow
  pure [y1,y2,y3,y4,y5]
grammarNumbers : Grammar () Token True (List1 Number)
grammarNumbers = someTill grammarNewline $ grammarNumber <* optional grammarComma
grammarBoards : Grammar () Token True (List1 Board)
grammarBoards = someTill eof grammarBoard
grammar : Grammar () Token True InputType
grammar = do
  ns <- grammarNumbers
  grammarNewline
  bs <- grammarBoards
  pure (ns,bs)

-- Part 1.
part1 : InputType -> IO ()
part1 input = ?part1_rhs

-- Part 2.
part2 : InputType -> IO ()
part2 input = ?part2_rhs

main : IO ()
main = solveAoC solution
  where solution : AoCSolution Token InputType
        solution = MkAoCSolution
          { inputFilePath = "./input"
          , tokenizer = tokenizer
          , grammar = grammar
          , part1 = part1
          , part2 = part2
          }