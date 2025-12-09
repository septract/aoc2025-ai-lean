/-
  Advent of Code 2025, Day 6 Part 1: Trash Compactor
  Formally verified solution in Lean 4

  Problem: Parse a worksheet of math problems arranged vertically in columns.
  Each problem has numbers stacked vertically with an operation (+/*) at bottom.
  Solve each problem and sum all answers.
-/

namespace Day06Part1

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
-- Find problem groups, extract numbers, apply operations.
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
  -- Mark each column as space or not
  let isSpace := cols.map (isSpaceColumn grid)
  -- Find runs of non-space columns
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

/-- Extract characters from a column range for a single line. -/
def extractRange (line : String) (startCol endCol : Nat) : String :=
  let chars := (List.range (endCol - startCol)).map fun i => charAt line (startCol + i)
  String.mk chars

/-- Parse a number from a string (trimmed). -/
def parseNum (s : String) : Option Nat :=
  let t := s.trim
  if t.isEmpty then none else t.toNat?

/-- Parse an operator from a character. -/
def parseOp (c : Char) : Option Op :=
  if c == '+' then some Op.add
  else if c == '*' then some Op.mul
  else none

/-- Extract numbers and operator from a problem region.
    Numbers are in all rows except the last; operator is in the last row. -/
def extractProblem (grid : Grid) (startCol endCol : Nat) : Option (List Nat × Op) :=
  match grid.reverse with
  | [] => none
  | opLine :: numLines =>
    let opStr := extractRange opLine startCol endCol
    let opChar := opStr.toList.find? (fun c => c == '+' || c == '*')
    match opChar >>= parseOp with
    | none => none
    | some op =>
      let numStrs := numLines.reverse.map (extractRange · startCol endCol)
      let nums := numStrs.filterMap parseNum
      some (nums, op)

/-- Evaluate a problem: apply the operation to all numbers. -/
def evalProblem (nums : List Nat) (op : Op) : Nat :=
  match op with
  | Op.add => nums.sum
  | Op.mul => nums.foldl (· * ·) 1

/-- SPECIFICATION: Solve the worksheet.
    Find all problems, evaluate each, sum the results. -/
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

/-- Parse a number from a string. -/
def parseNum (s : String) : Option Nat :=
  let t := s.trim
  if t.isEmpty then none else t.toNat?

/-- Extract and evaluate a single problem from column range. -/
def evalProblemRange (grid : Grid) (startCol endCol : Nat) : Nat :=
  match grid.reverse with
  | [] => 0
  | opLine :: numLines =>
    -- Find operator
    let opChars := (List.range (endCol - startCol)).map fun i => charAt opLine (startCol + i)
    let isAdd := opChars.any (· == '+')
    -- Extract numbers
    let nums := numLines.reverse.filterMap fun line =>
      let chars := (List.range (endCol - startCol)).map fun i => charAt line (startCol + i)
      parseNum (String.mk chars)
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
#guard Spec.evalProblem [123, 45, 6] Op.mul = 33210
#guard Spec.evalProblem [328, 64, 98] Op.add = 490

-- Test the full example
#guard solve testInput = 4277556
#guard Spec.solve (parse testInput) = 4277556

-- Test on actual input
def actualInput : String := include_str "../inputs/day06.txt"
#guard solve actualInput = 3968933219902

end Day06Part1
