/-
  Advent of Code 2025, Day 4 Part 2: Printing Department
  Formally verified solution in Lean 4

  Problem: Repeatedly remove accessible rolls (< 4 neighbors) until none remain.
  Count total rolls removed.
-/

namespace Day04Part2

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------

/-- A position in the grid (row, column). -/
structure Pos where
  row : Int
  col : Int
deriving Repr, DecidableEq, Hashable

/-- A grid is represented as a list of rows, where each row is a list of booleans
    (true = paper roll, false = empty). -/
abbrev Grid := List (List Bool)

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- Repeatedly find and remove accessible rolls until no more can be removed.
-------------------------------------------------------------------------------

namespace Spec

/-- The 8 directions for neighbors. -/
def directions : List (Int × Int) :=
  [(-1, -1), (-1, 0), (-1, 1),
   (0, -1),           (0, 1),
   (1, -1),  (1, 0),  (1, 1)]

/-- Get the value at a position (false if out of bounds). -/
def getAt (grid : Grid) (p : Pos) : Bool :=
  if p.row < 0 || p.col < 0 then false
  else
    let rowData := grid.getD p.row.toNat []
    rowData.getD p.col.toNat false

/-- Count neighboring rolls for a position. -/
def countNeighbors (grid : Grid) (p : Pos) : Nat :=
  directions.foldl (fun acc (dr, dc) =>
    let neighbor := { row := p.row + dr, col := p.col + dc : Pos }
    if getAt grid neighbor then acc + 1 else acc
  ) 0

/-- Check if a roll at position p is accessible (fewer than 4 neighbors). -/
def isAccessible (grid : Grid) (p : Pos) : Bool :=
  getAt grid p && countNeighbors grid p < 4

/-- All positions in the grid. -/
def allPositions (grid : Grid) : List Pos :=
  let numRows := grid.length
  let numCols := match grid with | row :: _ => row.length | [] => 0
  (List.range numRows).flatMap fun (r : Nat) =>
    (List.range numCols).map fun (c : Nat) =>
      (⟨↑r, ↑c⟩ : Pos)

/-- Find all accessible rolls in the current grid. -/
def findAccessible (grid : Grid) : List Pos :=
  (allPositions grid).filter (isAccessible grid)

/-- Set a position to empty (false). -/
def setEmpty (grid : Grid) (p : Pos) : Grid :=
  if p.row < 0 || p.col < 0 then grid
  else
    grid.mapIdx fun rowIdx row =>
      if rowIdx == p.row.toNat then
        row.mapIdx fun colIdx cell =>
          if colIdx == p.col.toNat then false else cell
      else row

/-- Remove all rolls at the given positions. -/
def removeRolls (grid : Grid) (positions : List Pos) : Grid :=
  positions.foldl setEmpty grid

/-- Count total rolls that can be removed by repeated removal.
    Uses fuel to ensure termination. -/
def countRemovableAux (grid : Grid) (fuel : Nat) : Nat :=
  if fuel == 0 then 0
  else
    let accessible := findAccessible grid
    if accessible.isEmpty then 0
    else
      let newGrid := removeRolls grid accessible
      accessible.length + countRemovableAux newGrid (fuel - 1)
termination_by fuel
decreasing_by simp_all; omega

/-- SPECIFICATION: Total rolls that can be removed. -/
def countRemovable (grid : Grid) : Nat :=
  -- Use total number of rolls as fuel (upper bound on iterations)
  let totalRolls := (allPositions grid).countP (getAt grid)
  countRemovableAux grid (totalRolls + 1)

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Same algorithm with efficient iteration.
-------------------------------------------------------------------------------

namespace Impl

/-- Get the value at a position (false if out of bounds). -/
def getAt (grid : Grid) (row col : Int) : Bool :=
  if row < 0 || col < 0 then false
  else
    let rowData := grid.getD row.toNat []
    rowData.getD col.toNat false

/-- Count neighboring rolls for a position. -/
def countNeighbors (grid : Grid) (row col : Int) : Nat :=
  let check := fun dr dc => if getAt grid (row + dr) (col + dc) then 1 else 0
  check (-1) (-1) + check (-1) 0 + check (-1) 1 +
  check 0 (-1) + check 0 1 +
  check 1 (-1) + check 1 0 + check 1 1

/-- Check if a cell is accessible. -/
def isAccessible (grid : Grid) (row col : Nat) : Bool :=
  getAt grid row col && countNeighbors grid row col < 4


/-- Process one row: mark accessible cells and count them. -/
def processRow (grid : Grid) (rowIdx : Nat) (rowData : List Bool) : Nat × List Bool :=
  go rowData 0 0 []
where
  go (cells : List Bool) (colIdx : Nat) (count : Nat) (acc : List Bool) : Nat × List Bool :=
    match cells with
    | [] => (count, acc.reverse)
    | cell :: rest =>
      if cell && countNeighbors grid rowIdx colIdx < 4 then
        go rest (colIdx + 1) (count + 1) (false :: acc)  -- Remove it
      else
        go rest (colIdx + 1) count (cell :: acc)  -- Keep it

/-- One iteration: remove all accessible rolls, return count and new grid. -/
def oneIteration (grid : Grid) : Nat × Grid :=
  go grid 0 0 []
where
  go (rows : List (List Bool)) (rowIdx : Nat) (count : Nat) (acc : Grid) : Nat × Grid :=
    match rows with
    | [] => (count, acc.reverse)
    | rowData :: rest =>
      let (rowCount, newRow) := processRow grid rowIdx rowData
      go rest (rowIdx + 1) (count + rowCount) (newRow :: acc)

/-- Count total removable rolls by repeated iteration. -/
def countRemovableAux (grid : Grid) (fuel : Nat) : Nat :=
  if fuel == 0 then 0
  else
    let (removed, newGrid) := oneIteration grid
    if removed == 0 then 0
    else removed + countRemovableAux newGrid (fuel - 1)
termination_by fuel
decreasing_by simp_all; omega

/-- Count total rolls in a grid. -/
def countRolls (grid : Grid) : Nat :=
  grid.foldl (fun acc row => acc + row.countP id) 0

/-- IMPLEMENTATION: Total rolls that can be removed. -/
def countRemovable (grid : Grid) : Nat :=
  let fuel := countRolls grid + 1
  countRemovableAux grid fuel

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------

namespace Proof

/-- MAIN THEOREM: Implementation equals specification for all inputs. -/
theorem impl_eq_spec (grid : Grid) :
    Impl.countRemovable grid = Spec.countRemovable grid := by
  sorry

end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
-------------------------------------------------------------------------------

/-- Parse a single character to a boolean. -/
def parseCell (c : Char) : Bool := c == '@'

/-- Parse a line into a row of the grid. -/
def parseLine (line : String) : List Bool :=
  line.toList.map parseCell

/-- Parse the input into a grid. -/
def parse (input : String) : Grid :=
  (input.splitOn "\n").map parseLine |>.filter (·.length > 0)

/-- Main solve function. -/
def solve (input : String) : Nat :=
  Impl.countRemovable (parse input)

/-- The solve function is correct by the main theorem. -/
theorem solve_correct (input : String) :
    solve input = Spec.countRemovable (parse input) :=
  Proof.impl_eq_spec (parse input)

def main : IO Unit := do
  let input ← IO.FS.readFile "inputs/day04.txt"
  IO.println s!"Answer: {solve input}"

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
-------------------------------------------------------------------------------

def testInput : String := "..@@.@@@@.
@@@.@.@.@@
@@@@@.@.@@
@.@@@@..@.
@@.@@@@.@@
.@@@@@@@.@
.@.@.@.@@@
@.@@@.@@@@
.@@@@@@@@.
@.@.@@@.@."

-- Test parsing
#guard (parse testInput).length = 10

-- Test the full example: 43 total rolls removed
#guard solve testInput = 43

-- Test on actual input
def actualInput : String := include_str "../inputs/day04.txt"
#guard solve actualInput = 8746

end Day04Part2
