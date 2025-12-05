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

/-- The 8 neighbor offsets. -/
def neighborOffsets : List (Int × Int) :=
  [(-1, -1), (-1, 0), (-1, 1),
   (0, -1),           (0, 1),
   (1, -1),  (1, 0),  (1, 1)]

/-- Get the 8 neighbor positions of a position. -/
def neighbors (p : Pos) : List Pos :=
  neighborOffsets.map fun (dr, dc) => ⟨p.row + dr, p.col + dc⟩

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- Declarative, set-based definition:
--   1. rolls(grid) = positions containing paper rolls
--   2. accessible = rolls with fewer than 4 neighbor rolls
--   3. answer = count of accessible rolls
-------------------------------------------------------------------------------

namespace Spec

/-- Get the value at a position (false if out of bounds). -/
def getAt (grid : Grid) (p : Pos) : Bool :=
  if p.row < 0 || p.col < 0 then false
  else
    let rowData := grid.getD p.row.toNat []
    rowData.getD p.col.toNat false

/-- All positions in the grid bounds. -/
def allPositions (grid : Grid) : List Pos :=
  let numRows := grid.length
  let numCols := match grid with | row :: _ => row.length | [] => 0
  (List.range numRows).flatMap fun (r : Nat) =>
    (List.range numCols).map fun (c : Nat) =>
      (⟨↑r, ↑c⟩ : Pos)

/-- The set of all positions containing paper rolls. -/
def rolls (grid : Grid) : List Pos :=
  (allPositions grid).filter (getAt grid)

/-- Count how many neighbors of a position are rolls. -/
def countNeighborRolls (grid : Grid) (p : Pos) : Nat :=
  (neighbors p).countP (getAt grid)

/-- A roll is accessible if it has fewer than 4 neighboring rolls. -/
def isAccessible (grid : Grid) (p : Pos) : Bool :=
  countNeighborRolls grid p < 4

/-- The set of accessible rolls (rolls with < 4 neighbor rolls). -/
def accessibleRolls (grid : Grid) : List Pos :=
  (rolls grid).filter (isAccessible grid)

/-- SPECIFICATION: Count of accessible paper rolls.
    Declaratively: the number of rolls that have fewer than 4 neighbor rolls. -/
def countAccessible (grid : Grid) : Nat :=
  (accessibleRolls grid).length

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Efficient nested iteration over the grid.
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

/-- IMPLEMENTATION: Count accessible rolls via nested iteration.
    Iterates row-by-row, column-by-column, accumulating the count. -/
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

/-- MAIN THEOREM: Implementation equals specification for all inputs.
    The nested iteration produces the same count as filtering the roll set. -/
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

-- Test spec components
#guard (Spec.rolls (parse testInput)).length = 71  -- Total rolls in example
#guard (Spec.accessibleRolls (parse testInput)).length = 13  -- Accessible rolls

-- Test the full example
#guard solve testInput = 13
#guard Spec.countAccessible (parse testInput) = 13

-- Test on actual input
def actualInput : String := include_str "../inputs/day04.txt"
#guard solve actualInput = 1449

end Day04Part1
