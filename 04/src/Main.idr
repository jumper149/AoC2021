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
  grammarNewline
  pure [y1,y2,y3,y4,y5]
grammarNumbers : Grammar () Token True (List1 Number)
grammarNumbers = someTill grammarNewline $ grammarNumber <* optional grammarComma
grammarBoards : Grammar () Token True (List1 Board)
grammarBoards = someTill eof grammarBoard
grammar : Grammar () Token True InputType
grammar = do
  ns <- grammarNumbers
  bs <- grammarBoards
  pure (ns,bs)

-- Part 1.
PlayingBoard : Type
PlayingBoard = Vect 5 $ Vect 5 $ Maybe Number
toPlayingBoard : Board -> PlayingBoard
toPlayingBoard = map (map Just)
bingoStep : Number -> PlayingBoard -> PlayingBoard
bingoStep n = map (map updateNumber)
  where
    updateNumber : Maybe Number -> Maybe Number
    updateNumber Nothing = Nothing
    updateNumber (Just m) = if m == n
                               then Nothing
                               else Just m
checkBingo : PlayingBoard -> Bool
checkBingo xss = let bss = map (map numberToBool) xss
                  in check bss || check (transpose bss)
  where
    numberToBool : Maybe Number -> Bool
    numberToBool Nothing = True
    numberToBool (Just n) = False
    check : Vect 5 (Vect 5 Bool) -> Bool
    check = any id . map (all id)
sumBoard : PlayingBoard -> Number
sumBoard = sum . map sum . map (map ignoreNothing)
  where
    ignoreNothing : Maybe Number -> Number
    ignoreNothing Nothing = 0
    ignoreNothing (Just x) = x
bingoPlay : (last : Number) -> List Number -> List PlayingBoard -> Number
bingoPlay last ns boards =
  case reverse $ sort $ map sumBoard $ filter checkBingo boards of
       [] => case ns of
                  [] => ?nooneWins
                  (x :: xs) => bingoPlay x xs $ bingoStep x <$> boards
       x::xs => last * x
part1 : InputType -> IO ()
part1 (numbers, boards) = do
  let playingBoards = toPlayingBoard <$> boards
  let x = bingoPlay 0 (forget numbers) (forget playingBoards)
  printLn x
  pure ()

-- Part 2.
lastWinner : (last : Number) -> List Number -> List PlayingBoard -> (Number,List PlayingBoard)
lastWinner last numbers boards =
  case filter (not . checkBingo) boards of
       [] => (last,boards)
       ys => case numbers of
                  [] => (last,boards)
                  (x :: xs) => lastWinner x xs $ bingoStep x <$> ys
part2 : InputType -> IO ()
part2 (numbers, boards) = do
  let playingBoards = toPlayingBoard <$> boards
  let (n,bs) = lastWinner 0 (forget numbers) (forget playingBoards)
  printLn $ (n *) <$> (sumBoard <$> bs)
  pure ()

main : IO ()
main = do
  solveAoC solution
  pure ()
  where solution : AoCSolution Token InputType
        solution = MkAoCSolution
          { inputFilePath = "./input"
          , tokenizer = tokenizer
          , grammar = grammar
          , part1 = part1
          , part2 = part2
          }
