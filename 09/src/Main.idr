module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Input.
InputType : Type
InputType = (n ** (m ** Vect m (Vect n (Fin 10))))

-- Lexer.
data Token = MkTokenNewline
           | MkTokenDigit Nat
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])
tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match digit (MkTokenDigit . cast)

-- Parser.
--mapSnd' : (x ** p) -> (p -> q) -> (x ** q)
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
  let grammarLine = withLength <$> someTill grammarNewline grammarDigit
  xs <- someTill eof grammarLine
  (n ** ys) <- grammarEmbedMaybe "Equal line lengths." $ equalLengths xs
  pure (n ** withLength ys)

-- Part 1.
withNext : {n : Nat} -> Fin n -> Maybe (Fin n)
withNext x = strengthen $ FS x
withPrev : {n : Nat} -> Fin n -> Maybe (Fin n)
withPrev FZ = Nothing 
withPrev (FS y) = Just $ weaken y
adjacent : {n : Nat} -> {m : Nat} -> (Fin n, Fin m) -> List (Fin n, Fin m)
adjacent (x, y) = toList left ++ toList top ++ toList right ++ toList bottom
where
  left : Maybe (Fin n, Fin m)
  left = case withPrev x of
             Just z => Just (z, y)
             _ => Nothing
  top : Maybe (Fin n, Fin m)
  top = case withPrev y of
             Just z => Just (x, z)
             _ => Nothing
  right : Maybe (Fin n, Fin m)
  right = case withNext x of
               Just z => Just (z, y)
               _ => Nothing
  bottom : Maybe (Fin n, Fin m)
  bottom = case withNext y of
                Just z => Just (x, z)
                _ => Nothing
height : (Fin n, Fin m) -> Vect m (Vect n (Fin 10)) -> Fin 10
height (x, y) = index x . index y
isLowest : {n : Nat} -> {m : Nat} -> Vect m (Vect n (Fin 10)) -> (Fin n, Fin m) -> Bool
isLowest grid xy = all (height xy grid <) $ height <$> adjacent xy <*> pure grid
fins : (n : Nat) -> Vect n (Fin n)
fins Z = []
fins (S k) = FZ :: (FS <$> fins k)
part1 : InputType -> IO ()
part1 (n ** (m ** grid)) = do
  let coords = do
    x <- toList $ fins n
    y <- toList $ fins m
    pure (x, y)
  let f = \ x => (isLowest grid x, S $ finToNat $ height x grid)
  let riskLevels = sum $ map snd $ filter fst $ f <$> coords
  printLn riskLevels
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
