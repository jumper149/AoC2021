module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Testground.
countLength : List a -> (n ** Vect n a)
countLength [] = (0 ** [])
countLength (x :: xs) with (countLength xs)
  _ | (n ** ys) = (S n ** x :: ys)

exactLengths : (len : Nat) -> Traversable t => t (n ** Vect n a) -> Maybe (t (Vect len a))
exactLengths len xs = traverse (\ x => exactLength len x.snd) xs

equalLengths : List1 (n ** Vect n a) -> Maybe (m ** (List1 (Vect m a)))
equalLengths ((len ** xs) ::: ys) = do
  list <- exactLengths len ys
  pure (len ** xs ::: list)

-- Input.
InputType : Type
InputType = (n ** List1 (Vect n Bool))

-- Lexer.
data Token = MkTokenNewline
           | MkTokenZero
           | MkTokenOne
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match (is '0' ) (const MkTokenZero)
        <|> match (is '1' ) (const MkTokenOne)

-- Parser.
grammarNewline : Grammar () Token True ()
grammarNewline = terminal "Newline" $ \ x =>
                 case x of
                      MkTokenNewline => Just ()
                      _ => Nothing
grammarBool : Grammar () Token True Bool
grammarBool = terminal "Bool" $ \ x =>
              case x of
                   MkTokenZero => Just False
                   MkTokenOne => Just True
                   _ => Nothing
grammarLine : Grammar () Token True (n ** Vect n Bool)
grammarLine = countLength <$> manyTill grammarNewline grammarBool
grammarEmbedMaybe : String -> Maybe a -> Grammar state tok False a
grammarEmbedMaybe msg Nothing = fail msg
grammarEmbedMaybe _ (Just x) = pure x
grammar : Grammar () Token True InputType
grammar = equalLengths <$> someTill eof grammarLine >>= grammarEmbedMaybe "Unequal line lengths."

-- Part 1.
countBit : Bool -> Integer -> Integer
countBit False x = x - 1
countBit True x = x + 1
countBits : {n : Nat} -> Vect n Bool -> Vect n Integer -> Vect n Integer
countBits bs xs = countBit <$> bs <*> xs
countBitss : {n : Nat} -> Foldable f => f (Vect n Bool) -> Vect n Integer
countBitss vects = foldr countBits (pure 0) vects
mostCommonBits : Vect n Integer -> Vect n Bool
mostCommonBits = map (> 0)
leastCommonBits : Vect n Integer -> Vect n Bool
leastCommonBits = map (< 0)
bitsToNat : Vect n Bool -> Nat
bitsToNat [] = 0
bitsToNat (x :: xs) = 2 * bitsToNat xs + y
  where
    y : Nat
    y = if x then 1 else 0
part1 : InputType -> IO ()
part1 (n ** vects) = do
  let commonBits = countBitss vects
  let x = bitsToNat $ reverse $ mostCommonBits commonBits
  let y = bitsToNat $ reverse $ leastCommonBits commonBits
  printLn $ x * y
  pure ()

-- Part 2.
mostCommonFirstBit : List (Vect (S n) Bool) -> Bool
mostCommonFirstBit vects = if (count >= 0)
                              then True
                              else False
  where
    count : Integer
    count = foldr (\ x => countBit (Data.Vect.head x)) 0 vects
step1 : {n : Nat} -> List (Vect n Bool) -> List (Vect n Bool)
step1 xs with (n)
  _ | Z = xs
  _ | (S k) = (y ::) <$> step1 ys
    where
      y : Bool
      y = mostCommonFirstBit xs
      ys : List (Vect k Bool)
      ys = tail <$> filter ((== y) . head) xs
leastCommonFirstBit : List (Vect (S n) Bool) -> Bool
leastCommonFirstBit vects = if (count >= 0)
                               then False
                               else True
  where
    count : Integer
    count = foldr (\ x => countBit (Data.Vect.head x)) 0 vects
step2 : {n : Nat} -> List (Vect n Bool) -> List (Vect n Bool)
step2 xs with (n)
  _ | Z = xs
  _ | (S k) = case ys of
                   [] => xs
                   (z::zs) => (y ::) <$> step2 ys
    where
      y : Bool
      y = leastCommonFirstBit xs
      ys : List (Vect k Bool)
      ys = tail <$> filter ((== y) . head) xs
part2 : InputType -> IO ()
part2 (n ** vects) = do
  let x = bitsToNat . reverse <$> (step1 $ forget vects)
  let y = bitsToNat . reverse <$> (step2 $ forget vects)
  printLn $ x
  printLn $ y
  printLn $ (*) <$> x <*> y
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
