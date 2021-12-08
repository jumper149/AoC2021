module Main

import AoC
import Data.Vect
import Generics.Derive
%language ElabReflection

-- Input.
data Segment = SegmentA
             | SegmentB
             | SegmentC
             | SegmentD
             | SegmentE
             | SegmentF
             | SegmentG
%runElab (derive "Segment" [ Eq, Generic, Meta, Ord, Show ])
InputType : Type
InputType = List1 (List1 (List1 Segment), List1 (List1 Segment))

-- Lexer.
data Token = MkTokenNewline
           | MkTokenWhitespace
           | MkTokenDelimiter
           | MkTokenSegment Segment
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match spaces (const MkTokenWhitespace)
        <|> match (is '|') (const MkTokenDelimiter)
        <|> match (is 'a') (const $ MkTokenSegment SegmentA)
        <|> match (is 'b') (const $ MkTokenSegment SegmentB)
        <|> match (is 'c') (const $ MkTokenSegment SegmentC)
        <|> match (is 'd') (const $ MkTokenSegment SegmentD)
        <|> match (is 'e') (const $ MkTokenSegment SegmentE)
        <|> match (is 'f') (const $ MkTokenSegment SegmentF)
        <|> match (is 'g') (const $ MkTokenSegment SegmentG)

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
  let grammarDelimiter = terminal "Delimiter" $ \ x =>
                         case x of
                              MkTokenDelimiter => Just ()
                              _ => Nothing
  let grammarSegment = terminal "Segment" $ \ x =>
                       case x of
                            MkTokenSegment y => Just y
                            _ => Nothing
  let grammarLeft = someTill grammarDelimiter $ someTill grammarWhitespace grammarSegment
  let grammarRight = someTill grammarNewline $ grammarWhitespace *> some grammarSegment
  let grammarLine = (,) <$> grammarLeft <*> grammarRight
  someTill eof grammarLine

segments0 : List Segment
segments0 = [ SegmentA, SegmentB, SegmentC, SegmentE, SegmentF, SegmentG ]

segments1 : List Segment
segments1 = [ SegmentC, SegmentF ]

segments2 : List Segment
segments2 = [ SegmentA, SegmentC, SegmentD, SegmentE, SegmentG ]

segments3 : List Segment
segments3 = [ SegmentA, SegmentC, SegmentD, SegmentF, SegmentG ]

segments4 : List Segment
segments4 = [ SegmentB, SegmentC, SegmentD, SegmentF ]

segments5 : List Segment
segments5 = [ SegmentA, SegmentB, SegmentD, SegmentF, SegmentG ]

segments6 : List Segment
segments6 = [ SegmentA, SegmentB, SegmentD, SegmentE, SegmentF, SegmentG ]

segments7 : List Segment
segments7 = [ SegmentA, SegmentC, SegmentF ]

segments8 : List Segment
segments8 = [ SegmentA, SegmentB, SegmentC, SegmentD, SegmentE, SegmentF, SegmentG ]

segments9 : List Segment
segments9 = [ SegmentA, SegmentB, SegmentC, SegmentD, SegmentF, SegmentG ]

-- Part 1.
part1 : InputType -> IO ()
part1 input = do
  let lastParts = foldr (++) [] $ forget . snd <$> forget input
  let counted = length <$> lastParts
  let isUniqueLength = \ x => x == length segments1
                           || x == length segments4
                           || x == length segments7
                           || x == length segments8
  let uniques = filter isUniqueLength counted
  printLn $ length uniques
  pure ()

-- Part 2.
wireOutput : List Segment -> Vect 7 Bool
wireOutput [] = pure False
wireOutput (x :: xs) = case x of
                            SegmentA => replaceAt 0 True $ wireOutput xs
                            SegmentB => replaceAt 1 True $ wireOutput xs
                            SegmentC => replaceAt 2 True $ wireOutput xs
                            SegmentD => replaceAt 3 True $ wireOutput xs
                            SegmentE => replaceAt 4 True $ wireOutput xs
                            SegmentF => replaceAt 5 True $ wireOutput xs
                            SegmentG => replaceAt 6 True $ wireOutput xs
fixLengths : (List a, List b) -> Maybe (Vect 10 a, Vect 4 b)
fixLengths (xs, ys) = do
    xs' <- toVect 10 xs
    ys' <- toVect 4 ys
    pure (xs', ys')

count : Vect 7 Bool -> Nat
count = fst . filter id
findOrder : Vect 10 (Vect 7 Bool) -> Maybe (Vect 10 (Vect 7 Bool))
findOrder xs = do
  case sortBy (\ x, y => compare (count x) (count y)) $ toList xs of
       [ x1, x7, x4, xl51, xl52, xl53, xl61, xl62, xl63, x8 ] => do
         let eqCount = \ x, y => (count $ (==) <$> x <*> y, y)
         let compareFst = \ x, y => compare (fst x) (fst y)
         x3 <- head' $ reverse $ map snd $ sortBy compareFst $ map (eqCount x1) $ [ xl51, xl52, xl53 ]
         x2 <- head' $           map snd $ sortBy compareFst $ map (eqCount x4) $ [ xl51, xl52, xl53 ]
         x5 <- head' $ filter (/= x2) $ filter (/= x3) $ [ xl51, xl52, xl53 ]
         x6 <- head' $           map snd $ sortBy compareFst $ map (eqCount x1) $ [ xl61, xl62, xl63 ]
         x9 <- head' $ reverse $ map snd $ sortBy compareFst $ map (eqCount x4) $ [ xl61, xl62, xl63 ]
         x0 <- head' $           map snd $ sortBy compareFst $ map (eqCount x5) $ [ xl61, xl62, xl63 ]
         pure [ x0, x1, x2, x3, x4, x5, x6, x7, x8, x9 ]
       _ => ?unexpectedLengthAfterSorting
num : (lookup : Vect 10 (Vect 7 Bool)) -> Vect 7 Bool -> Maybe Nat
num lookup n = finToNat <$> findIndex (== n) lookup
calc : (lookup : Vect 10 (Vect 7 Bool)) -> (xs : Vect 4 (Vect 7 Bool)) -> Maybe Nat
calc lookup xs = case traverse (num lookup) xs of
                      Just [x1,x2,x3,x4] => Just $ x4 + 10 * (x3 + 10 * (x2 + 10 * x1))
                      Nothing => ?asjkhdlas
order : (Vect 10 (Vect 7 Bool), Vect 4 (Vect 7 Bool)) -> Maybe (Vect 10 (Vect 7 Bool), Vect 4 (Vect 7 Bool))
order = \ (x, y) => (,) <$> findOrder x <*> pure y
part2 : InputType -> IO ()
part2 input = do
  let preWires = bimap (forget . map (wireOutput . forget)) (forget . map (wireOutput . forget)) <$> input
  case traverse fixLengths preWires of
       Nothing => pure ()
       Just wires => do
         case traverse order wires of
              Nothing => ?askljhdalks
              Just res => case traverse (uncurry calc) res of
                               Nothing => ?alksjdhkljhlkashd
                               Just res2 => printLn $ sum res2
         pure ()
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

f : Vect 3 Nat
f = count . (\ x => (\ a, b => a == b) <$> wireOutput segments5 <*> wireOutput x) <$> [ segments0, segments6, segments9 ]
