module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Input.
record Dot where
  constructor MkDot
  x, y : Integer
%runElab (derive "Dot" [ Eq, Generic, Meta, Ord, Show ])

data Fold = MkFoldAlongX Nat
          | MkFoldAlongY Nat
%runElab (derive "Fold" [ Eq, Generic, Meta, Ord, Show ])

InputType : Type
InputType = (List1 Dot, List1 Fold)

-- Lexer.
data Token = MkTokenNewline
           | MkTokenComma
           | MkTokenFoldInstructionX
           | MkTokenFoldInstructionY
           | MkTokenNumber Nat
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match (is ',') (const MkTokenComma)
        <|> match (exact "fold along x=") (const MkTokenFoldInstructionX)
        <|> match (exact "fold along y=") (const MkTokenFoldInstructionY)
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
  let grammarFold = terminal "Fold" $ \ x =>
                    case x of
                         MkTokenFoldInstructionX => Just MkFoldAlongX
                         MkTokenFoldInstructionY => Just MkFoldAlongY
                         _ => Nothing
  let grammarNumber = terminal "Number" $ \ x =>
                      case x of
                           MkTokenNumber x => Just x
                           _ => Nothing
  dots <- some (MkDot <$> (natToInteger <$> grammarNumber) <* grammarComma <*> (natToInteger <$> grammarNumber) <* grammarNewline)
  grammarNewline
  folds <- someTill eof (grammarFold <*> grammarNumber <* grammarNewline)
  pure (dots, folds)

-- Part 1.
foldDot : (f : Fold) -> (dot : Dot) -> Dot
foldDot (MkFoldAlongX k) dot@(MkDot x y) = if x <= natToInteger k then dot else record { x = natToInteger k - (x - natToInteger k) } dot
foldDot (MkFoldAlongY k) dot@(MkDot x y) = if y <= natToInteger k then dot else record { y = natToInteger k - (y - natToInteger k) } dot

foldPaper : (f : Fold) -> (dots : List Dot) -> List Dot
foldPaper f dots = sort $ nub $ foldDot f <$> dots

part1 : InputType -> IO ()
part1 input = do
  let dots = sort $ nub $ forget $ fst input
  let firstFold = head $ snd input
  printLn $ length dots
  printLn $ length $ foldPaper firstFold dots
  pure ()

-- Part 2.
drawDot : {xMax : Nat} -> {yMax : Nat} -> Dot -> Vect yMax (Vect xMax Bool) -> Vect yMax (Vect xMax Bool)
drawDot (MkDot x y) grid = case (f x, f y) of
                                (Just xx, Just yy) => updateAt yy (updateAt xx (const True)) grid
                                _ => grid
where
  f : {n : Nat} -> Integer -> Maybe (Fin n)
  f x = do
    y <- if x >= 0 then Just $ integerToNat x else Nothing
    z <- natToFin y n
    pure z

drawPaper : (xMax : Nat) -> (yMax : Nat) -> List Dot -> Vect yMax (Vect xMax Bool)
drawPaper xMax yMax dots = foldr drawDot (replicate yMax $ replicate xMax False) dots

renderPaper : {xMax : Nat} -> {yMax : Nat} -> Vect yMax (Vect xMax Bool) -> String
renderPaper [] = ""
renderPaper (y::ys) = renderLine (toList y) ++ "\n" ++ renderPaper ys
where
  renderLine : List Bool -> String
  renderLine [] = ""
  renderLine (x::xs) = (if x then 'X' else '.') `strCons` renderLine xs


part2 : InputType -> IO ()
part2 input = do
  let dots = sort $ nub $ forget $ fst input
  let folds = forget $ snd input
  putStrLn $ renderPaper $ drawPaper 50 50 $ foldl (flip foldPaper) dots folds
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
