module Main

import AoC
import Data.SortedMap
import Generics.Derive
%language ElabReflection

-- Input.
record Instruction where
  constructor MkInstruction
  left, right, new : Char
%runElab (derive "Instruction" [ Eq, Generic, Meta, Ord, Show ])

InputType : Type
InputType = (List1 Char, List1 Instruction)

-- Lexer.
data Token = MkTokenNewline
           | MkTokenArrow
           | MkTokenChar String
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match (exact " -> ") (const MkTokenArrow)
        <|> match upper MkTokenChar

-- Parser.
grammar : Grammar () Token True InputType
grammar = do
  let grammarNewline = terminal "Newline" $ \ x =>
                       case x of
                            MkTokenNewline => Just ()
                            _ => Nothing
  let grammarArrow = terminal "Arrow" $ \ x =>
                     case x of
                          MkTokenArrow => Just ()
                          _ => Nothing
  let grammarChar = terminal "Arrow" $ \ x =>
                    case x of
                         MkTokenChar str => case unpack str of
                                                 [c] => Just c
                                                 _ => Nothing
                         _ => Nothing
  chars <- someTill grammarNewline grammarChar
  grammarNewline
  instructions <- someTill eof $ do
    left <- grammarChar
    right <- grammarChar
    grammarArrow
    new <- grammarChar
    grammarNewline
    pure $ MkInstruction { left, right, new }
  pure (chars, instructions)

-- Part 1.

insert : (instructions : SortedMap (Char, Char) Char) ->
         (chars : List Char) ->
         List Char
insert instructions xs@[] = xs
insert instructions xs@(_::[]) = xs
insert instructions xs@(c1::c2::cs) = case lookup (c1,c2) instructions of
                                           Nothing => c1 :: insert instructions (c2 :: cs)
                                           Just c => c1 :: c :: insert instructions (c2 :: cs)

times : Nat -> (f : a -> a) -> a -> a
times Z _ x = x
times (S k) f x = f $ times k f x

part1 : InputType -> IO ()
part1 input = do
  let chars = forget $ fst input
  let instructions = forget $ snd input
  let rules = foldr (\ x => insert (x.left, x.right) x.new) empty instructions
  let counts = sort $ map length $ group $ sort $ times 10 (insert rules) chars
  let xg = case head' $ reverse counts of
                Nothing => 0
                Just x => natToInteger x
  let xl = case head' counts of
                Nothing => 0
                Just x => natToInteger x
  printLn $ xg - xl
  pure ()


-- Part 2.
pairs : List1 Char -> SortedMap (Char, Char) Nat
pairs (x ::: []) = empty
pairs (x ::: (y :: ys)) = insert key val rec
where
  rec : SortedMap (Char, Char) Nat
  rec = pairs $ y ::: ys
  key : (Char, Char)
  key = (x, y)
  val : Nat
  val = S $ case lookup key rec of
                 Nothing => Z
                 Just x => x

useRule : (rules : SortedMap (Char, Char) Char) ->
          (charPair : ((Char, Char), Nat)) ->
          SortedMap (Char, Char) Nat
useRule rules (lr@(l, r), n) = case lookup lr rules of
                                    Nothing => insert lr n $ empty
                                    Just c => insert (l, c) n $ insert (c, r) n $ empty

step : (rules : SortedMap (Char, Char) Char) ->
       (chars : SortedMap (Char, Char) Nat) ->
       SortedMap (Char, Char) Nat
step rules chars = foldr (mergeWith (+)) empty $ useRule rules <$> Data.SortedMap.toList chars

fromPairs : SortedMap (Char, Char) Nat -> SortedMap Char Nat
fromPairs xs = foldr (mergeWith (+)) empty $ map (uncurry singleton) $ singles $ Data.SortedMap.toList xs
where
  singles : List ((Char, Char), Nat) -> List (Char, Nat)
  singles [] = []
  singles (((x, y), n)::xs) = (x, n) :: (y, n) :: singles xs

prepNumber : (firstChar : Char) -> (lastChar : Char) -> (Char, Nat) -> Integer
prepNumber firstChar lastChar (c, n) = if c == firstChar || c == lastChar
                                          then (natToInteger n + 1) `div` 2
                                          else natToInteger n `div` 2

part2 : InputType -> IO ()
part2 input = do
  let chars = fst input
  let firstChar = head chars
  let lastChar = last chars
  let charPairs = pairs chars
  let instructions = forget $ snd input
  let rules = foldr (\ x => insert (x.left, x.right) x.new) empty instructions
  let x0 = times 40 (step rules) charPairs
  let xFinal = Data.List1.fromList $ sortBy (\ x, y => compare (snd x) (snd y)) $ Data.SortedMap.toList $ fromPairs x0
  case xFinal of
       Nothing => ?emptyOut
       Just xs => do
         printLn $ (prepNumber firstChar lastChar $ last xs) - (prepNumber firstChar lastChar $ head xs)
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
