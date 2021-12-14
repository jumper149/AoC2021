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
