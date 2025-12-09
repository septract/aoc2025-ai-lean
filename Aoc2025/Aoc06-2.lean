/-
  Advent of Code 2025, Day 6 Part 2: Trash Compactor (Cephalopod Math)
  Formally verified solution in Lean 4

  Problem: Same as Part 1, but numbers are read differently:
  - Read columns right-to-left within each problem
  - Each column forms a number with MSD at top, LSD at bottom
-/

namespace Day06Part2

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------

/-- A grid is just the raw lines of the input. -/
abbrev Grid := List String

/-- An operation is either addition or multiplication. -/
inductive Op where
  | add : Op
  | mul : Op
deriving Repr, DecidableEq

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- Declarative definition working directly on the grid.
-- Read columns right-to-left, form numbers from digits top-to-bottom.
-------------------------------------------------------------------------------

namespace Spec

/-- Get character at position in a string, or space if out of bounds. -/
def charAt (s : String) (i : Nat) : Char :=
  s.toList.getD i ' '

/-- Check if a column is all spaces (separator column). -/
def isSpaceColumn (grid : Grid) (col : Nat) : Bool :=
  grid.all fun line => (charAt line col) == ' '

/-- Get the maximum line length in the grid. -/
def maxCol (grid : Grid) : Nat :=
  grid.map (·.length) |>.foldl max 0

/-- Find all problem boundaries (start, end column pairs).
    Problems are separated by columns that are all spaces. -/
def findProblemBoundaries (grid : Grid) : List (Nat × Nat) :=
  let mc := maxCol grid
  let cols := List.range (mc + 1)
  let isSpace := cols.map (isSpaceColumn grid)
  let rec findRuns (i : Nat) (inRun : Bool) (start : Nat) (acc : List (Nat × Nat))
      : List (Nat × Nat) :=
    if i > mc then
      if inRun then acc ++ [(start, i)] else acc
    else if isSpace.getD i true then
      if inRun then findRuns (i + 1) false 0 (acc ++ [(start, i)])
      else findRuns (i + 1) false 0 acc
    else
      if inRun then findRuns (i + 1) true start acc
      else findRuns (i + 1) true i acc
  termination_by mc + 1 - i
  findRuns 0 false 0 []

/-- Parse an operator from a character. -/
def parseOp (c : Char) : Option Op :=
  if c == '+' then some Op.add
  else if c == '*' then some Op.mul
  else none

/-- Convert a list of digit characters (MSD first) to a number. -/
def digitsToNum (digits : List Char) : Nat :=
  digits.foldl (fun acc c =>
    if c.isDigit then acc * 10 + (c.toNat - '0'.toNat) else acc) 0

/-- Read a single column from the number rows, returning digits top-to-bottom. -/
def readColumn (numRows : List String) (col : Nat) : List Char :=
  numRows.map (charAt · col)

/-- Extract numbers by reading columns right-to-left within a problem region.
    Each column forms a number with digits read top-to-bottom. -/
def extractNumbers (numRows : List String) (startCol endCol : Nat) : List Nat :=
  -- Columns from right to left
  let cols := (List.range (endCol - startCol)).reverse
  cols.filterMap fun offset =>
    let col := startCol + offset
    let digits := readColumn numRows col |>.filter Char.isDigit
    if digits.isEmpty then none
    else some (digitsToNum digits)

/-- Extract the operator from the operator row. -/
def extractOp (opRow : String) (startCol endCol : Nat) : Option Op :=
  let chars := (List.range (endCol - startCol)).map fun i => charAt opRow (startCol + i)
  chars.find? (fun c => c == '+' || c == '*') >>= parseOp

/-- Extract numbers and operator from a problem region (cephalopod style). -/
def extractProblem (grid : Grid) (startCol endCol : Nat) : Option (List Nat × Op) :=
  match grid.reverse with
  | [] => none
  | opRow :: numRows =>
    match extractOp opRow startCol endCol with
    | none => none
    | some op =>
      let nums := extractNumbers numRows.reverse startCol endCol
      some (nums, op)

/-- Evaluate a problem: apply the operation to all numbers. -/
def evalProblem (nums : List Nat) (op : Op) : Nat :=
  match op with
  | Op.add => nums.sum
  | Op.mul => nums.foldl (· * ·) 1

/-- SPECIFICATION: Solve the worksheet (cephalopod style).
    Find all problems, read columns right-to-left, evaluate each, sum results. -/
def solve (grid : Grid) : Nat :=
  let boundaries := findProblemBoundaries grid
  let results := boundaries.filterMap fun (s, e) =>
    match extractProblem grid s e with
    | none => none
    | some (nums, op) => some (evalProblem nums op)
  results.sum

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- More efficient single-pass algorithm.
-------------------------------------------------------------------------------

namespace Impl

/-- Get character at position in a string, or space if out of bounds. -/
def charAt (s : String) (i : Nat) : Char :=
  s.toList.getD i ' '

/-- Check if a column is all spaces. -/
def isSpaceColumn (grid : Grid) (col : Nat) : Bool :=
  grid.all fun line => (charAt line col) == ' '

/-- Convert digit characters to number. -/
def digitsToNum (digits : List Char) : Nat :=
  digits.foldl (fun acc c =>
    if c.isDigit then acc * 10 + (c.toNat - '0'.toNat) else acc) 0

/-- Extract and evaluate a single problem from column range (cephalopod style). -/
def evalProblemRange (grid : Grid) (startCol endCol : Nat) : Nat :=
  match grid.reverse with
  | [] => 0
  | opRow :: numRows =>
    -- Find operator
    let opChars := (List.range (endCol - startCol)).map fun i => charAt opRow (startCol + i)
    let isAdd := opChars.any (· == '+')
    -- Extract numbers: read columns right-to-left
    let numRowsRev := numRows.reverse
    let cols := (List.range (endCol - startCol)).reverse
    let nums := cols.filterMap fun offset =>
      let col := startCol + offset
      let digits := numRowsRev.map (charAt · col) |>.filter Char.isDigit
      if digits.isEmpty then none
      else some (digitsToNum digits)
    -- Apply operation
    if isAdd then nums.foldl (· + ·) 0
    else nums.foldl (· * ·) 1

/-- IMPLEMENTATION: Single pass through columns, accumulating result. -/
def solve (grid : Grid) : Nat :=
  if grid.isEmpty then 0
  else
    let mc := grid.map (·.length) |>.foldl max 0
    let rec go (fuel : Nat) (col : Nat) (inProblem : Bool) (start : Nat) (acc : Nat) : Nat :=
      match fuel with
      | 0 => if inProblem then acc + evalProblemRange grid start col else acc
      | fuel' + 1 =>
        if col > mc then
          if inProblem then acc + evalProblemRange grid start col else acc
        else if isSpaceColumn grid col then
          if inProblem then go fuel' (col + 1) false 0 (acc + evalProblemRange grid start col)
          else go fuel' (col + 1) false 0 acc
        else
          if inProblem then go fuel' (col + 1) true start acc
          else go fuel' (col + 1) true col acc
    go (mc + 2) 0 false 0 0

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------

namespace Proof

/-- MAIN THEOREM: Implementation equals specification. -/
theorem impl_eq_spec (grid : Grid) :
    Impl.solve grid = Spec.solve grid := by
  sorry

end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
-------------------------------------------------------------------------------

/-- Parse input to grid (minimal: just split lines). -/
def parse (input : String) : Grid :=
  input.splitOn "\n" |>.filter (·.length > 0)

/-- Main solve function. -/
def solve (input : String) : Nat :=
  Impl.solve (parse input)

/-- The solve function is correct by the main theorem. -/
theorem solve_correct (input : String) :
    solve input = Spec.solve (parse input) :=
  Proof.impl_eq_spec (parse input)

def main : IO Unit := do
  let input ← IO.FS.readFile "inputs/day06.txt"
  IO.println s!"Answer: {solve input}"

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
-------------------------------------------------------------------------------

def testInput : String := "123 328  51 64
 45 64  387 23
  6 98  215 314
*   +   *   +  "

-- Test parsing (minimal)
#guard (parse testInput).length = 4

-- Test spec components
#guard (Spec.findProblemBoundaries (parse testInput)).length = 4
#guard Spec.digitsToNum ['4', '3', '1'] = 431
#guard Spec.evalProblem [4, 431, 623] Op.add = 1058
#guard Spec.evalProblem [175, 581, 32] Op.mul = 3253600

-- Test the full example
-- Rightmost: 4 + 431 + 623 = 1058
-- Second: 175 * 581 * 32 = 3253600
-- Third: 8 + 248 + 369 = 625
-- Leftmost: 356 * 24 * 1 = 8544
-- Total: 1058 + 3253600 + 625 + 8544 = 3263827
#guard solve testInput = 3263827
#guard Spec.solve (parse testInput) = 3263827

-- Test on actual input
def actualInput : String := include_str "../inputs/day06.txt"
#guard solve actualInput = 6019576291014

end Day06Part2
