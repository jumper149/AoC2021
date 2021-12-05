module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Input.
InputType : Type
InputType = List1 ((Nat, Nat), (Nat, Nat))

-- Lexer.
data Token = MkTokenNewline
           | MkTokenWhitespace
           | MkTokenArrow
           | MkTokenComma
           | MkTokenNumber Nat
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match spaces (const MkTokenWhitespace)
        <|> match (exact "->") (const MkTokenArrow)
        <|> match (is ',') (const MkTokenComma)
        <|> match digits (MkTokenNumber . cast)

-- Parser.
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
  let grammarArrow = terminal "Arrow" $ \ x =>
                     case x of
                          MkTokenArrow => Just ()
                          _ => Nothing
  let grammarComma = terminal "Comma" $ \ x =>
                     case x of
                          MkTokenComma => Just ()
                          _ => Nothing
  let grammarNumber = terminal "Number" $ \ x =>
                      case x of
                           MkTokenNumber n => Just n
                           _ => Nothing
  let grammarLine = do
    x1 <- grammarNumber
    grammarComma
    y1 <- grammarNumber
    grammarWhitespace
    grammarArrow
    grammarWhitespace
    x2 <- grammarNumber
    grammarComma
    y2 <- grammarNumber
    grammarNewline
    pure ((x1, y1), (x2, y2))
  someTill eof grammarLine

-- Part 1.
line : ((Nat, Nat), (Nat, Nat)) -> List (Nat, Nat)
line ((x1, y1), (x2, y2)) with (x1 == x2, y1 == y2)
  _ | (True, True) = [ (x1, y2) ]
  _ | (True, False) = (x1, ) <$> [ y1 .. y2 ]
  _ | (False, True) = (, y1) <$> [ x1 .. x2 ]
  _ | (False, False) = []
count : List (Nat, Nat) -> List (Nat, (Nat, Nat))
count = map f . group . sort
  where
    f : List1 (Nat, Nat) -> (Nat, (Nat, Nat))
    f (x ::: xs) = (S (length xs), x)
part1 : InputType -> IO ()
part1 input = do
  let lines = foldMap id $ line <$> input
  let counts = filter (>= (S $ S Z)) $ fst <$> count lines
  printLn $ length counts

-- Part 2.
line2 : ((Nat, Nat), (Nat, Nat)) -> List (Nat, Nat)
line2 ((x1, y1), (x2, y2)) with (x1 == x2, y1 == y2)
  _ | (True, True) = [ (x1, y2) ]
  _ | (True, False) = (x1, ) <$> [ y1 .. y2 ]
  _ | (False, True) = (, y1) <$> [ x1 .. x2 ]
  _ | (False, False) = zipWith (,) [ x1 .. x2 ] [ y1 .. y2 ]
part2 : InputType -> IO ()
part2 input = do
  let lines = foldMap id $ line2 <$> input
  let counts = filter (>= (S $ S Z)) $ fst <$> count lines
  printLn $ length counts

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
