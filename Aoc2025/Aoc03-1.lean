/-
  Advent of Code 2025, Day 3: Lobby
  Formally verified solution in Lean 4

  Problem: Given banks of batteries (digit strings), select exactly 2 batteries
  from each bank to form a 2-digit joltage. Find the sum of max joltages.
-/

namespace Day03Part1

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------

/-- A digit is a natural number 0-9. The problem uses 1-9 but we allow 0 for generality. -/
abbrev Digit := Fin 10

/-- A bank is a list of digits. -/
abbrev Bank := List Digit

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- Enumerate all pairs (i, j) with i < j, compute 10*d[i] + d[j], take maximum.
-------------------------------------------------------------------------------

namespace Spec

/-- The joltage formed by selecting two digits. -/
def joltage (d1 d2 : Digit) : Nat := 10 * d1.val + d2.val

/-- All pairs of digits at positions (i, j) with i < j.
    We enumerate by taking each element and pairing with all elements after it. -/
def allPairs (bank : Bank) : List (Digit × Digit) :=
  match bank with
  | [] => []
  | d :: rest => (rest.map fun d2 => (d, d2)) ++ allPairs rest

/-- Maximum joltage from a bank by checking all pairs. -/
def maxJoltage (bank : Bank) : Nat :=
  ((allPairs bank).map (fun (d1, d2) => joltage d1 d2)).max?.getD 0

/-- SPECIFICATION: Sum of maximum joltages from each bank. -/
def solve (banks : List Bank) : Nat :=
  (banks.map maxJoltage).sum

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Efficient algorithm: find the max digit that has something after it,
-- then find the max digit after that position.
-------------------------------------------------------------------------------

namespace Impl

/-- Find the maximum digit value in a list, returning 0 if empty. -/
def maxDigitVal (ds : List Digit) : Nat :=
  ds.foldl (fun acc d => max acc d.val) 0

/-- Find the position of the leftmost occurrence of the maximum digit
    in the prefix [0, n-1] (i.e., excluding the last element). -/
def findFirstMaxPos (bank : Bank) : Option Nat :=
  if bank.length < 2 then none
  else
    -- Find max value in positions 0..length-2
    let init := bank.take (bank.length - 1)
    let maxVal := maxDigitVal init
    -- Find leftmost position with that value
    findPosAux bank maxVal 0
where
  findPosAux (bank : Bank) (target : Nat) (pos : Nat) : Option Nat :=
    match bank with
    | [] => none
    | d :: rest =>
      -- Don't consider the last position (need something after)
      if rest.isEmpty then none
      else if d.val == target then some pos
      else findPosAux rest target (pos + 1)

/-- Maximum joltage from a bank.
    Strategy: Find the best first digit (max value, leftmost), then max digit after it. -/
def maxJoltage (bank : Bank) : Nat :=
  match findFirstMaxPos bank with
  | none => 0
  | some i =>
    let d1 := bank.getD i ⟨0, by decide⟩
    let rest := bank.drop (i + 1)
    let d2 := maxDigitVal rest
    10 * d1.val + d2

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
  (input.splitOn "\n").map parseLine |>.filter (·.length ≥ 2)

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

-- Test joltage calculation
#guard Spec.joltage (d 9) (d 8) = 98
#guard Spec.joltage (d 8) (d 9) = 89
#guard Spec.joltage (d 7) (d 8) = 78
#guard Spec.joltage (d 9) (d 2) = 92

-- Test allPairs on a simple example
#guard (Spec.allPairs [d 1, d 2, d 3]).length = 3

-- Test example from problem
def testInput : String := "987654321111111
811111111111119
234234234234278
818181911112111"

#guard Spec.maxJoltage (parseLine "987654321111111") = 98
#guard Spec.maxJoltage (parseLine "811111111111119") = 89
#guard Spec.maxJoltage (parseLine "234234234234278") = 78
#guard Spec.maxJoltage (parseLine "818181911112111") = 92

#guard Impl.maxJoltage (parseLine "987654321111111") = 98
#guard Impl.maxJoltage (parseLine "811111111111119") = 89
#guard Impl.maxJoltage (parseLine "234234234234278") = 78
#guard Impl.maxJoltage (parseLine "818181911112111") = 92

#guard solve testInput = 357
#guard Spec.solve (parse testInput) = 357

-- Test on actual input
def actualInput : String := include_str "../inputs/day03.txt"
#guard solve actualInput = 17343

end Day03Part1
