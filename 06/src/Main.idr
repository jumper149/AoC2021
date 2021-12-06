module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Input.
InputType : Type
InputType = List1 $ Fin 6

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
  let ys = traverse (\ x => natToFin x 6) xs
  grammarEmbedMaybe "Finite numbers." ys

-- Part 1.
--stepFish : Nat -> List1 Nat
--stepFish Z = 6 ::: [8]
--stepFish (S k) = k ::: []
--stepFishes : List Nat -> List Nat
--stepFishes = foldr (++) [] . map (forget . stepFish)
times : Nat -> (a -> a) -> a -> a
times Z f x = x
times (S k) f x = times k f $ f x
Fishes : Type
Fishes = Vect 9 Nat
initFishes : List (Fin 9) -> Fishes
initFishes = foldr insert (replicate 9 0)
where
  insert : Fin 9 -> Vect 9 Nat -> Vect 9 Nat
  insert n = updateAt n S
stepFishes : Vect 9 Nat -> Vect 9 Nat
stepFishes (x :: xs) = updateAt 6 (+ x) xs `snoc` x
part1 : InputType -> IO ()
part1 input = do
  let initial = initFishes $ forget $ weakenN 3 <$> input
  let final = times 80 stepFishes initial
  printLn initial
  printLn final
  printLn $ sum final
  pure ()

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
