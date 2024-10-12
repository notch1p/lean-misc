import Std.Data.HashMap
open Std (HashMap)


abbrev TileIndex := Nat × Nat

inductive TileState | TileEmpty | TileX | TileO deriving Repr, BEq
inductive Player | XPlayer | OPlayer deriving Repr, BEq

abbrev Board := HashMap TileIndex TileState

structure GameState where
  board : Board
  currentPlayer : Player
  generator : StdGen

open TileState

def findOpen : StateM GameState (List TileIndex) := do
  let game <- get
  return game.board.toList.filterMap λ (i, x) => guard (x == TileEmpty) *> i

def chooseRandomMove : StateM GameState TileIndex := do
  let game <- get
  let openSpots <- findOpen
  let gen := game.generator
  let (i, gen') := randNat gen 0 (openSpots.length - 1) -- gen' is the new generator
  set { game with generator := gen' }
  return openSpots[i]!

#reduce (types := true) StateM GameState Bool

open Player

def tileStateForPlayer : Player -> TileState
  | XPlayer => TileX
  | OPlayer => TileO

def nextPlayer : Player -> Player
  | XPlayer => OPlayer
  | OPlayer => XPlayer

def applyMove (i : TileIndex) : StateM GameState Unit := do
  let game <- get
  let p := game.currentPlayer
  let board := game.board.insert i (tileStateForPlayer p)
  set { game with board, currentPlayer := nextPlayer p }

def isGameDone := do
  pure (<- findOpen).isEmpty

def nextTurn := do
  let i <- chooseRandomMove
  applyMove i
  isGameDone

def initBoard : Board := Id.run do
  let mut board := HashMap.empty
  for i in [0 : 3] do
    for j in [0 : 3] do
      board := board.insert (i, j) TileEmpty
  board

def printBoard (b : Board) : IO Unit := do
  let mut row : List String := []
  for i in b.toList do
    let s := match i.2 with
      | TileEmpty => " "
      | TileX => "X"
      | TileO => "O"
    row := row.append [s]
    if row.length == 3 then
      IO.println row
      row := []

def playGame := do
  while true do
    if (<- nextTurn) then return

def play : IO Unit := do
  let gen <- IO.stdGenRef.get
  let (x, generator) := randNat gen 0 1
  let gs : GameState := {
    board := initBoard,
    currentPlayer := if x == 0 then XPlayer else OPlayer,
    generator
  }
  let (_, g) := playGame |>.run gs
  printBoard g.board

def nextTurnManually : StateM GameState Bool -- GameState -> GameState × Bool
  | s =>
    let (i, gs) := chooseRandomMove |>.run s
    let (_, gs') := applyMove i |>.run gs
    let (res, gs'') := isGameDone |>.run gs'
    (res, gs'')
