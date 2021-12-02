module Main

import AoC

-- Input.
InputType : Type
--InputType = ?inputType_rhs

-- Lexer.
data Token = MkTokenNewline
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> ?tokenize

-- Parser.
grammar : Grammar () Token True InputType
grammar = do
  let grammarNewline = terminal "Newline" $ \ x =>
                       case x of
                            MkTokenNewline => Just ()
                            _ => Nothing
  ?grammarize

-- Part 1.
part1 : InputType -> IO ()
part1 input = ?part1_rhs

-- Part 2.
part2 : InputType -> IO ()
part2 input = ?part2_rhs

-- Main.
solution : AoCSolution Token InputType
solution = MkAoCSolution
  { inputFilePath = "./input"
  , tokenizer = tokenizer
  , grammar = grammar
  , part1 = part1
  , part2 = part2
  }

main : IO ()
main = solveAoC solution
