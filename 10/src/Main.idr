module Main

import AoC
import Control.Monad.State
import Data.Either
import Generics.Derive
%language ElabReflection

-- Input.
data Enclosure = MkEnclosureOpen
               | MkEnclosureClose
%runElab (derive "Enclosure" [ Eq, Generic, Meta, Ord, Show ])
data ChunkCharacter = MkChunkCharacterParens Enclosure
                    | MkChunkCharacterBracket Enclosure
                    | MkChunkCharacterCurly Enclosure
                    | MkChunkCharacterOrd Enclosure
%runElab (derive "ChunkCharacter" [ Eq, Generic, Meta, Ord, Show ])
InputType : Type
InputType = List1 (List1 ChunkCharacter)

-- Lexer.
data Token = MkTokenNewline
           | MkTokenChunkCharacter ChunkCharacter
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match (is '(') (const $ MkTokenChunkCharacter $ MkChunkCharacterParens MkEnclosureOpen)
        <|> match (is ')') (const $ MkTokenChunkCharacter $ MkChunkCharacterParens MkEnclosureClose)
        <|> match (is '[') (const $ MkTokenChunkCharacter $ MkChunkCharacterBracket MkEnclosureOpen)
        <|> match (is ']') (const $ MkTokenChunkCharacter $ MkChunkCharacterBracket MkEnclosureClose)
        <|> match (is '{') (const $ MkTokenChunkCharacter $ MkChunkCharacterCurly MkEnclosureOpen)
        <|> match (is '}') (const $ MkTokenChunkCharacter $ MkChunkCharacterCurly MkEnclosureClose)
        <|> match (is '<') (const $ MkTokenChunkCharacter $ MkChunkCharacterOrd MkEnclosureOpen)
        <|> match (is '>') (const $ MkTokenChunkCharacter $ MkChunkCharacterOrd MkEnclosureClose)

-- Parser.
grammar : Grammar () Token True InputType
grammar = do
  let grammarNewline = terminal "Newline" $ \ x =>
                       case x of
                            MkTokenNewline => Just ()
                            _ => Nothing
  let grammarChunkCharacter = terminal "ChunkCharacter" $ \ x =>
                              case x of
                                   MkTokenChunkCharacter x => Just x
                                   _ => Nothing
  someTill eof $ someTill grammarNewline grammarChunkCharacter

-- Part 1.
data Chunk = MkChunkParens
           | MkChunkBracket
           | MkChunkCurly
           | MkChunkOrd
%runElab (derive "Chunk" [ Eq, Generic, Meta, Ord, Show ])
data Chunks = MkChunk (List (Chunk, Chunks))
%runElab (derive "Chunks" [ Eq, Generic, Meta, Ord, Show ])
data ChunkizeError = MkChunkizeErrorIncomplete
                   | MkChunkizeErrorCorrupted Chunk Chunk
                   | MkChunkizeErrorCritical
%runElab (derive "ChunkizeError" [ Eq, Generic, Meta, Ord, Show ])
matchingChar : ChunkCharacter -> ChunkCharacter -> Bool
matchingChar (MkChunkCharacterParens MkEnclosureOpen) (MkChunkCharacterParens MkEnclosureClose) = True
matchingChar (MkChunkCharacterBracket MkEnclosureOpen) (MkChunkCharacterBracket MkEnclosureClose) = True
matchingChar (MkChunkCharacterCurly MkEnclosureOpen) (MkChunkCharacterCurly MkEnclosureClose) = True
matchingChar (MkChunkCharacterOrd MkEnclosureOpen) (MkChunkCharacterOrd MkEnclosureClose) = True
matchingChar _ _ = False
enclosure : ChunkCharacter -> Enclosure
enclosure (MkChunkCharacterParens x) = x
enclosure (MkChunkCharacterBracket x) = x
enclosure (MkChunkCharacterCurly x) = x
enclosure (MkChunkCharacterOrd x) = x
g1 : List (ChunkCharacter) -> State (List Chunk) (Either ChunkizeError Chunks)
g1 [] = pure $ Right $ MkChunk []
g1 (x::xs) = case x of
                  (MkChunkCharacterParens MkEnclosureOpen) => do
                    modify (MkChunkParens ::) 
                    g1 xs
                  (MkChunkCharacterParens MkEnclosureClose) => do
                    acc <- get
                    case acc of
                         [] => pure $ Left MkChunkizeErrorCritical
                         (y::ys) => if y == MkChunkParens
                                       then do
                                         put ys
                                         g1 xs
                                       else pure $ Left $ MkChunkizeErrorCorrupted y MkChunkParens
                  (MkChunkCharacterBracket MkEnclosureOpen) => do
                    modify (MkChunkBracket ::) 
                    g1 xs
                  (MkChunkCharacterBracket MkEnclosureClose) => do
                    acc <- get
                    case acc of
                         [] => pure $ Left MkChunkizeErrorCritical
                         (y::ys) => if y == MkChunkBracket
                                       then do
                                         put ys
                                         g1 xs
                                       else pure $ Left $ MkChunkizeErrorCorrupted y MkChunkBracket
                  (MkChunkCharacterCurly MkEnclosureOpen) => do
                    modify (MkChunkCurly ::) 
                    g1 xs
                  (MkChunkCharacterCurly MkEnclosureClose) => do
                    acc <- get
                    case acc of
                         [] => pure $ Left MkChunkizeErrorCritical
                         (y::ys) => if y == MkChunkCurly
                                       then do
                                         put ys
                                         g1 xs
                                       else pure $ Left $ MkChunkizeErrorCorrupted y MkChunkCurly
                  (MkChunkCharacterOrd MkEnclosureOpen) => do
                    modify (MkChunkOrd ::) 
                    g1 xs
                  (MkChunkCharacterOrd MkEnclosureClose) => do
                    acc <- get
                    case acc of
                         [] => pure $ Left MkChunkizeErrorCritical
                         (y::ys) => if y == MkChunkOrd
                                       then do
                                         put ys
                                         g1 xs
                                       else pure $ Left $ MkChunkizeErrorCorrupted y MkChunkOrd
errPoints : ChunkizeError -> Nat
errPoints MkChunkizeErrorIncomplete = 0
errPoints (MkChunkizeErrorCorrupted x y) = case y of
                                                MkChunkParens => 3
                                                MkChunkBracket => 57
                                                MkChunkCurly => 1197
                                                MkChunkOrd => 25137
errPoints MkChunkizeErrorCritical = 0

part1 : InputType -> IO ()
part1 input = do
  let lines = forget <$> input
  let chunkizeds = evalState [] <$> (g1 <$> lines)
  let errs = lefts $ forget chunkizeds
  printLn errs
  let points = sum $ errPoints <$> errs
  printLn points
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
