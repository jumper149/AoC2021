module Main

import AoC
import Generics.Derive
%language ElabReflection

-- Input.
data Cave = MkCaveStart
          | MkCaveEnd
          | MkCaveUpper String
          | MkCaveLower String
%runElab (derive "Cave" [ Eq, Generic, Meta, Ord, Show ])

record Connection where
  constructor MkConnection
  from, to : Cave

%runElab (derive "Connection" [ Eq, Generic, Meta, Ord, Show ])
InputType : Type
InputType = List1 Connection

-- Lexer.
data Token = MkTokenNewline
           | MkTokenDash
           | MkTokenNameStart
           | MkTokenNameEnd
           | MkTokenNameLower String
           | MkTokenNameUpper String
%runElab (derive "Token" [ Eq, Generic, Meta, Ord, Show ])

tokenizer : Tokenizer Token
tokenizer = match newline (const MkTokenNewline)
        <|> match (is '-') (const MkTokenDash)
        <|> match (exact "start") (const MkTokenNameStart)
        <|> match (exact "end") (const MkTokenNameEnd)
        <|> match lowers MkTokenNameLower
        <|> match uppers MkTokenNameUpper

-- Parser.
grammar : Grammar () Token True InputType
grammar = do
  let grammarNewline = terminal "Newline" $ \ x =>
                       case x of
                            MkTokenNewline => Just ()
                            _ => Nothing
  let grammarDash = terminal "Dash" $ \ x =>
                    case x of
                         MkTokenDash => Just ()
                         _ => Nothing
  let grammarCave = terminal "Cave" $ \ x =>
                    case x of
                         MkTokenNameStart => Just MkCaveStart
                         MkTokenNameEnd => Just MkCaveEnd
                         MkTokenNameUpper x => Just $ MkCaveUpper x
                         MkTokenNameLower x => Just $ MkCaveLower x
                         _ => Nothing
  let grammarLine = do
    from <- grammarCave
    grammarDash
    to <- grammarCave
    grammarNewline
    pure $ MkConnection { from, to }
  someTill eof grammarLine

-- Part 1.
flipConnection : (connection : Connection) ->
                 Connection
flipConnection (MkConnection from to) = MkConnection to from
nextCaves : (connections : List Connection) ->
            (cave : Cave) ->
            List Cave
nextCaves connections cave = to <$> filter (\ connection => connection.from == cave) connections

removeCave : (connections : List Connection) ->
             (cave : Cave) ->
             List Connection
removeCave connections cave = filter (\ connection => connection.to /= cave && connection.from /= cave) connections

waysToEnd : (connections : List Connection) ->
            (cave : Cave) ->
            List (List Cave)
waysToEnd _ MkCaveEnd = pure [ MkCaveEnd ]
waysToEnd connections cave@(MkCaveUpper name) = do
  next <- nextCaves connections cave
  way <- waysToEnd connections next
  pure $ cave :: way
waysToEnd connections cave = do
  next <- nextCaves connections cave
  way <- waysToEnd (removeCave connections cave) next
  pure $ cave :: way

part1 : InputType -> IO ()
part1 input = do
  let directedConnections = sort $ nub $ forget input
  let connections = nub $ sort $ directedConnections ++ (flipConnection <$> directedConnections)
  printLn $ length $ waysToEnd connections MkCaveStart
  pure ()

-- Part 2.
waysToEnd2 : (connections : List Connection) ->
             (cave : Cave) ->
             (twice : Bool) ->
             List (List Cave)
waysToEnd2 _ MkCaveEnd _ = pure [ MkCaveEnd ]
waysToEnd2 connections cave@(MkCaveUpper name) twice = do
  next <- nextCaves connections cave
  way <- waysToEnd2 connections next twice
  pure $ cave :: way
waysToEnd2 connections cave@MkCaveStart twice = do
  next <- nextCaves connections cave
  way <- waysToEnd2 (removeCave connections cave) next twice
  pure $ cave :: way
waysToEnd2 connections cave twice@True = do
  next <- nextCaves connections cave
  way <- waysToEnd2 (removeCave connections cave) next twice
  pure $ cave :: way
waysToEnd2 connections cave False = do
  next <- nextCaves connections cave
  way <- nub $ waysToEnd2 (removeCave connections cave) next False ++ waysToEnd2 connections next True
  pure $ cave :: way

part2 : InputType -> IO ()
part2 input = do
  let directedConnections = sort $ nub $ forget input
  let connections = nub $ sort $ directedConnections ++ (flipConnection <$> directedConnections)
  printLn $ length $ nub $ waysToEnd2 connections MkCaveStart False
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
