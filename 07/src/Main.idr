module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Input.
InputType : Type
InputType = List1 Nat

-- Lexer.
data Token = MkTokenNewline
           | MkTokenComma
           | MkTokenNumber Nat
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match (is ',') (const MkTokenComma)
        <|> match digits (MkTokenNumber . cast)

-- Parser.
grammar : Grammar () Token True InputType
grammar = do
  let grammarNewline = terminal "Newline" $ \ x =>
                       case x of
                            MkTokenNewline => Just ()
                            _ => Nothing
  let grammarComma = terminal "Comma" $ \ x =>
                     case x of
                          MkTokenComma => Just ()
                          _ => Nothing
  let grammarNumber = terminal "Comma" $ \ x =>
                      case x of
                           MkTokenNumber x => Just x
                           _ => Nothing
  xs <- sepBy1 grammarComma grammarNumber
  grammarNewline
  eof
  pure xs

-- Part 1.
fuel : (start : Integer) -> (stop : Integer) -> Integer
fuel start stop = abs $ stop - start
fuels : (starts : List Integer) -> (stop : Integer) -> Integer
fuels starts stop = sum $ fuel <$> starts <*> pure stop
part1 : InputType -> IO ()
part1 input = do
  let starts = natToInteger <$> input
  let stop = case last' $ sort $ forget starts of Nothing => 0; Just x => x
  let stops = [ 0 .. stop ]
  let fs = reverse $ sort $ (\ x => (fuels (forget starts) x, x)) <$> stops
  printLn fs
  pure ()

-- Part 2.
fuelModifier : Integer -> Integer
fuelModifier 0 = 0
fuelModifier n = n + fuelModifier (n-1)
fuels2 : (starts : List Integer) -> (stop : Integer) -> Integer
fuels2 starts stop = sum $ fuelModifier <$> (fuel <$> starts <*> pure stop)
part2 : InputType -> IO ()
part2 input = do
  let starts = natToInteger <$> input
  let stop = case last' $ sort $ forget starts of Nothing => 0; Just x => x
  let stops = [ 0 .. stop ]
  let fs = reverse $ sort $ (\ x => (fuels2 (forget starts) x, x)) <$> stops
  printLn fs
  pure ()

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
