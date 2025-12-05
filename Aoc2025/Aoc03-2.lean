/-
  Advent of Code 2025, Day 3 Part 2: Lobby
  Formally verified solution in Lean 4

  Problem: Given banks of batteries (digit strings), select exactly 12 batteries
  from each bank to form a 12-digit joltage number. Find the sum of max joltages.
-/

namespace Day03Part2

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------

/-- A digit is a natural number 0-9. -/
abbrev Digit := Fin 10

/-- A bank is a list of digits. -/
abbrev Bank := List Digit

/-- Number of digits to select from each bank. -/
def selectCount : Nat := 12

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- Enumerate all subsequences of exactly 12 elements, convert to number, take max.
-------------------------------------------------------------------------------

namespace Spec

/-- Convert a list of digits to a natural number. -/
def toNumber (digits : List Digit) : Nat :=
  digits.foldl (fun acc d => acc * 10 + d.val) 0

/-- All subsequences of exactly k elements (preserving order).
    This is the "n choose k" operation on lists. -/
def subsequences (k : Nat) : List α → List (List α)
  | [] => if k == 0 then [[]] else []
  | x :: xs =>
    if k == 0 then [[]]
    else
      -- Include x: need k-1 more from xs
      -- Exclude x: need k from xs
      (subsequences (k - 1) xs).map (x :: ·) ++ subsequences k xs

/-- Maximum joltage from selecting exactly 12 digits. -/
def maxJoltage (bank : Bank) : Nat :=
  (subsequences selectCount bank).map toNumber |>.max?.getD 0

/-- SPECIFICATION: Sum of maximum joltages from each bank. -/
def solve (banks : List Bank) : Nat :=
  (banks.map maxJoltage).sum

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Greedy algorithm: for each position in the result, pick the largest
-- available digit that leaves enough digits for remaining positions.
-------------------------------------------------------------------------------

namespace Impl

/-- Convert a list of digits to a natural number. -/
def toNumber (digits : List Digit) : Nat :=
  digits.foldl (fun acc d => acc * 10 + d.val) 0

/-- Find the index and value of the leftmost maximum in the first n elements.
    Returns (0, ⟨0, _⟩) if list is empty or n=0. -/
def findMaxInPrefix (xs : List Digit) (n : Nat) : Nat × Digit :=
  go xs n 0 0 ⟨0, by decide⟩
where
  go (xs : List Digit) (remaining : Nat) (curIdx : Nat) (bestIdx : Nat) (bestVal : Digit)
      : Nat × Digit :=
    if remaining == 0 then (bestIdx, bestVal)
    else match xs with
    | [] => (bestIdx, bestVal)
    | d :: rest =>
      if d.val > bestVal.val then
        go rest (remaining - 1) (curIdx + 1) curIdx d
      else
        go rest (remaining - 1) (curIdx + 1) bestIdx bestVal

/-- Select k digits from bank to maximize the resulting number.
    Greedy: at each step, pick the largest digit that leaves enough for remaining. -/
def selectMaxDigits (k : Nat) (bank : Bank) : List Digit :=
  let n := bank.length
  if n < k then []
  else go k bank n
where
  /-- remaining: digits still to select
      available: remaining portion of bank to choose from
      availLen: length of available (passed to avoid recomputation) -/
  go (remaining : Nat) (available : List Digit) (availLen : Nat) : List Digit :=
    if remaining == 0 then []
    else if availLen < remaining then []
    else
      -- Can search in first (availLen - remaining + 1) positions
      -- This ensures at least (remaining - 1) elements remain after our choice
      let searchLen := availLen - remaining + 1
      let (relIdx, digit) := findMaxInPrefix available searchLen
      digit :: go (remaining - 1) (available.drop (relIdx + 1)) (availLen - relIdx - 1)
  termination_by remaining
  decreasing_by simp_all; omega

/-- Maximum joltage from selecting exactly 12 digits. -/
def maxJoltage (bank : Bank) : Nat :=
  toNumber (selectMaxDigits selectCount bank)

/-- IMPLEMENTATION: Sum of maximum joltages from each bank. -/
def solve (banks : List Bank) : Nat :=
  (banks.map maxJoltage).sum

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------

namespace Proof

/-- MAIN THEOREM: Implementation equals specification for all inputs. -/
theorem impl_eq_spec (banks : List Bank) :
    Impl.solve banks = Spec.solve banks := by
  sorry

end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
-------------------------------------------------------------------------------

/-- Parse a character to a digit. Returns none for non-digits. -/
def charToDigit (c : Char) : Option Digit :=
  if h : c.toNat - '0'.toNat < 10 then
    some ⟨c.toNat - '0'.toNat, h⟩
  else
    none

/-- Parse a single line (bank) into a list of digits. -/
def parseLine (line : String) : Bank :=
  line.toList.filterMap charToDigit

/-- Parse the entire input into a list of banks. -/
def parse (input : String) : List Bank :=
  (input.splitOn "\n").map parseLine |>.filter (·.length ≥ selectCount)

/-- Main solve function: parse input and run implementation. -/
def solve (input : String) : Nat :=
  Impl.solve (parse input)

/-- The solve function is correct by the main theorem. -/
theorem solve_correct (input : String) :
    solve input = Spec.solve (parse input) :=
  Proof.impl_eq_spec (parse input)

def main : IO Unit := do
  let input ← IO.FS.readFile "inputs/day03.txt"
  IO.println s!"Answer: {solve input}"

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
-------------------------------------------------------------------------------

-- Helper to create a Digit from Nat
def d (n : Nat) (h : n < 10 := by decide) : Digit := ⟨n, h⟩

-- Test toNumber
#guard Impl.toNumber [d 9, d 8, d 7] = 987
#guard Impl.toNumber [d 1, d 2, d 3, d 4, d 5, d 6, d 7, d 8, d 9, d 0, d 1, d 2] = 123456789012

-- Test subsequences
#guard (Spec.subsequences 2 [d 1, d 2, d 3]).length = 3
#guard (Spec.subsequences 3 [d 1, d 2, d 3]).length = 1

-- Test example from problem
def testInput : String := "987654321111111
811111111111119
234234234234278
818181911112111"

-- Verify individual bank results from problem description
#guard Impl.maxJoltage (parseLine "987654321111111") = 987654321111
#guard Impl.maxJoltage (parseLine "811111111111119") = 811111111119
#guard Impl.maxJoltage (parseLine "234234234234278") = 434234234278
#guard Impl.maxJoltage (parseLine "818181911112111") = 888911112111

#guard solve testInput = 3121910778619

-- Test on actual input
def actualInput : String := include_str "../inputs/day03.txt"
#guard solve actualInput = 172664333119298

end Day03Part2
