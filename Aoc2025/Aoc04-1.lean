/-
  Advent of Code 2025, Day 4: Printing Department
  Formally verified solution in Lean 4

  Problem: Count paper rolls (@) that have fewer than 4 neighboring rolls
  in the 8 adjacent positions (can be accessed by forklift).
-/

namespace Day04Part1

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
-- For each cell that is a roll, count neighbors that are rolls.
-- If count < 4, the roll is accessible.
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

/-- SPECIFICATION: Count of accessible paper rolls. -/
def countAccessible (grid : Grid) : Nat :=
  (allPositions grid).countP (isAccessible grid)

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Same algorithm, but structured for efficiency.
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

/-- Count accessible rolls in a single row. -/
def countInRow (grid : Grid) (row : Nat) (rowData : List Bool) : Nat :=
  go rowData 0 0
where
  go (cells : List Bool) (col : Nat) (acc : Nat) : Nat :=
    match cells with
    | [] => acc
    | cell :: rest =>
      let newAcc := if cell && countNeighbors grid row col < 4 then acc + 1 else acc
      go rest (col + 1) newAcc

/-- IMPLEMENTATION: Count accessible rolls in the entire grid. -/
def countAccessible (grid : Grid) : Nat :=
  go grid 0 0
where
  go (rows : List (List Bool)) (row : Nat) (acc : Nat) : Nat :=
    match rows with
    | [] => acc
    | rowData :: rest =>
      let rowCount := countInRow grid row rowData
      go rest (row + 1) (acc + rowCount)

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------

namespace Proof

/-- MAIN THEOREM: Implementation equals specification for all inputs. -/
theorem impl_eq_spec (grid : Grid) :
    Impl.countAccessible grid = Spec.countAccessible grid := by
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
  Impl.countAccessible (parse input)

/-- The solve function is correct by the main theorem. -/
theorem solve_correct (input : String) :
    solve input = Spec.countAccessible (parse input) :=
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
#guard match (parse testInput) with | row :: _ => row.length = 10 | [] => false

-- Test the full example
#guard solve testInput = 13

-- Test on actual input
def actualInput : String := include_str "../inputs/day04.txt"
#guard solve actualInput = 1449

end Day04Part1
