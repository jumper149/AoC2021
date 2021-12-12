module Main

import AoC
import Generics.Derive
import Data.SortedMap
import Data.SortedSet
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
connectionMap : List Connection -> SortedMap Cave (SortedSet Cave)
connectionMap = foldr ins empty
where
  ins : Connection -> SortedMap Cave (SortedSet Cave) -> SortedMap Cave (SortedSet Cave)
  ins c cm = insert c.to (c.from `insert` xTo) . insert c.from (c.to `insert` xFrom) $ cm
  where
    xFrom : SortedSet Cave
    xFrom = case lookup c.from cm of
                 Nothing => empty
                 Just cs => cs
    xTo : SortedSet Cave
    xTo = case lookup c.to cm of
               Nothing => empty
               Just cs => cs

lookupCaves : Cave -> SortedMap Cave (SortedSet Cave) -> SortedSet Cave
lookupCaves c cm = case lookup c cm of
                        Nothing => empty
                        Just cs => cs

deleteCave : Cave -> SortedMap Cave (SortedSet Cave) -> SortedMap Cave (SortedSet Cave)
deleteCave c = delete c . map (delete c)

waysToEnd3 : (connections : SortedMap Cave (SortedSet Cave)) ->
             (cave : Cave) ->
             (twice : Bool) ->
             SortedSet (List Cave)
waysToEnd3 _ MkCaveEnd _ = singleton [ MkCaveEnd ]
waysToEnd3 connections cave@(MkCaveUpper name) twice = fromList . map (cave ::) . Data.SortedSet.toList $ ways
where
  nexts : SortedSet Cave
  nexts = lookupCaves cave connections
  ways : SortedSet (List Cave)
  ways = foldr (\ x, y => waysToEnd3 connections x twice `union` y) empty nexts
waysToEnd3 connections cave@MkCaveStart twice = fromList . map (cave ::) . Data.SortedSet.toList $ ways
where
  nexts : SortedSet Cave
  nexts = lookupCaves cave connections
  nexts' : List (Cave, SortedMap Cave (SortedSet Cave))
  nexts' = (\ x => (x, deleteCave cave connections)) <$> Data.SortedSet.toList nexts
  ways : SortedSet (List Cave)
  ways = foldr (\ (x, conns), y => waysToEnd3 conns x twice `union` y) empty nexts'
waysToEnd3 connections cave twice@True = fromList . map (cave ::) . Data.SortedSet.toList $ ways
where
  nexts : SortedSet Cave
  nexts = lookupCaves cave connections
  nexts' : List (Cave, SortedMap Cave (SortedSet Cave))
  nexts' = (\ x => (x, deleteCave cave connections)) <$> Data.SortedSet.toList nexts
  ways : SortedSet (List Cave)
  ways = foldr (\ (x, conns), y => waysToEnd3 conns x twice `union` y) empty nexts'
waysToEnd3 connections cave twice@False = fromList . map (cave ::) . Data.SortedSet.toList $ ways
where
  nexts : SortedSet Cave
  nexts = lookupCaves cave connections
  nexts' : List (Cave, SortedMap Cave (SortedSet Cave))
  nexts' = (\ x => (x, deleteCave cave connections)) <$> Data.SortedSet.toList nexts
  ways1 : SortedSet (List Cave)
  ways1 = foldr (\ (x, conns), y => waysToEnd3 conns x twice `union` y) empty nexts'
  ways2 : SortedSet (List Cave)
  ways2 = foldr (\ x, y => waysToEnd3 connections x True `union` y) empty nexts
  ways : SortedSet (List Cave)
  ways = ways1 `union` ways2

part2 : InputType -> IO ()
part2 input = do
  let directedConnections = sort $ nub $ forget input
  let connections = connectionMap directedConnections
  let ways = waysToEnd3 connections MkCaveStart False
  printLn $ length $ Data.SortedSet.toList ways
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
