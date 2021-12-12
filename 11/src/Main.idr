module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Input.
InputType : Type
InputType = Vect 10 (Vect 10 (Fin 10))

-- Lexer.
data Token = MkTokenNewline
           | MkTokenDigit Nat
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match digit (MkTokenDigit . cast)

-- Parser.
grammar : Grammar () Token True InputType
grammar = do
  let grammarNewline = terminal "Newline" $ \ x =>
                       case x of
                            MkTokenNewline => Just ()
                            _ => Nothing
  let grammarDigit = terminal "Digit" $ \ x =>
                       case x of
                            MkTokenDigit x => natToFin x 10
                            _ => Nothing
  let grammarLine = toVect 10 . forget <$> someTill grammarNewline grammarDigit >>= grammarEmbedMaybe "Line length"
  let grammarInput = toVect 10 . forget <$> someTill eof grammarLine >>= grammarEmbedMaybe "Input length"
  grammarInput

-- Part 1.
adjacent : {n : Nat} -> {m : Nat} -> (Fin n, Fin m) -> List (Fin n, Fin m)
adjacent (x, y) = catMaybes
  [ (,) <$> prev x <*> prev y
  , (,) <$> pure x <*> prev y
  , (,) <$> next x <*> prev y
  , (,) <$> next x <*> pure y
  , (,) <$> next x <*> next y
  , (,) <$> pure x <*> next y
  , (,) <$> prev x <*> next y
  , (,) <$> prev x <*> pure y
  ]
where
  next : {n : Nat} -> Fin n -> Maybe (Fin n)
  next x = strengthen $ FS x
  prev : {n : Nat} -> Fin n -> Maybe (Fin n)
  prev FZ = Nothing 
  prev (FS y) = Just $ weaken y
update : {n : Nat} -> {m : Nat} -> (a -> a) -> (Fin n, Fin m) -> Vect m (Vect n a) -> Vect m (Vect n a)
update f (x, y) = updateAt y (updateAt x f)
lookup : (Fin n, Fin m) -> Vect m (Vect n a) -> a
lookup (x, y) = index x . index y
f : {k : Nat} -> Vect k (Fin k)
f with (k)
  _ | (Z) = []
  _ | (S _) = FZ :: (FS <$> f)
allCoords : {n : Nat} -> {m : Nat} -> List (Fin n, Fin m)
allCoords = do
  x <- toList f
  y <- toList f
  pure (x, y)
adjacentToFlash : {n : Nat} -> {m : Nat} -> Vect m (Vect n (Nat, Bool)) -> List (Fin n, Fin m)
adjacentToFlash grid = foldr (++) []
                     $ map (adjacent . fst)
                     $ filter ((\ (a, b) => not b && a > 9) . snd)
                     $ map (\ x => (x, lookup x grid))
                     $ allCoords
stepRec : Vect 10 (Vect 10 (Nat, Bool)) -> Vect 10 (Vect 10 (Nat, Bool))
stepRec grid = if newGrid == grid
                  then newGrid
                  else stepRec newGrid
where
  increase : (Nat, Bool) -> (Nat, Bool)
  increase (x, b) = (x + 1, b)
  toFlash : List (Fin 10, Fin 10)
  toFlash = adjacentToFlash grid
  markFlash : (Nat, Bool) -> (Nat, Bool)
  markFlash (x, b) = (x, x > 9)
  newGrid : Vect 10 (Vect 10 (Nat, Bool))
  newGrid = foldr (update increase) (map (map markFlash) $ grid) toFlash
step : Vect 10 (Vect 10 (Fin 10)) -> Vect 10 (Vect 10 (Fin 10))
step = map (map to) . map (map fst) . stepRec . map (map (, False)) . map (map (+ 1)) . map (map from)
where
  from : Fin 10 -> Nat
  from = finToNat
  to : Nat -> Fin 10
  to x = case natToFin x 10 of
              Nothing => FZ
              Just y => y
countFlash : Vect 10 (Vect 10 (Fin 10)) -> Nat
countFlash = length . filter (== FZ) . foldr (++) [] . toList . map toList
countFlashes : Vect 10 (Vect 10 (Fin 10)) -> Nat -> Nat
countFlashes grid Z = 0
countFlashes grid (S k) = count + countFlashes newGrid k
where
  newGrid : Vect 10 (Vect 10 (Fin 10))
  newGrid = step grid
  count : Nat
  count = countFlash newGrid
debugGrid : Vect 10 (Vect 10 (Fin 10)) -> IO ()
debugGrid grid = traverse_ (\ x => traverse_ print x >> putStrLn "") grid
part1 : InputType -> IO ()
part1 input = do
  debugGrid input
  putStrLn ""
  debugGrid $ step input
  putStrLn ""
  debugGrid $ step $ step input
  printLn $ countFlashes input 100

-- Part 2.
zeroGrid : Vect 10 (Vect 10 (Fin 10))
zeroGrid = replicate 10 (replicate 10 FZ)
findSim : Vect 10 (Vect 10 (Fin 10)) -> Nat
findSim grid = if grid == zeroGrid
                  then Z
                  else S $ findSim $ step grid
part2 : InputType -> IO ()
part2 input = do
  printLn $ findSim input

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
