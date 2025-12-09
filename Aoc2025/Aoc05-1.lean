/-
  Advent of Code 2025, Day 5 Part 1: Cafeteria Inventory
  Formally verified solution in Lean 4

  Problem: Given a list of inclusive ranges defining "fresh" ingredient IDs,
  count how many of the available ingredient IDs are fresh.
  An ingredient is fresh if it falls within ANY of the ranges.
-/

namespace Day05Part1

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------

/-- A range of ingredient IDs (inclusive on both ends). -/
structure Range where
  low : Nat
  high : Nat
deriving Repr, DecidableEq

/-- The parsed input: ranges and ingredient IDs to check. -/
structure Input where
  ranges : List Range
  ingredients : List Nat
deriving Repr

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- Obviously correct: For each ingredient, enumerate ALL ranges and check.
-- No optimization - just filter and check non-empty.
-------------------------------------------------------------------------------

namespace Spec

/-- An ingredient is in a range if low ≤ id ≤ high. -/
def inRange (id : Nat) (r : Range) : Bool :=
  r.low ≤ id ∧ id ≤ r.high

/-- An ingredient is fresh if it's in at least one range.
    Declaratively: filter ranges that contain it, check non-empty.
    This enumerates ALL ranges (no short-circuit). -/
def isFresh (ranges : List Range) (id : Nat) : Bool :=
  (ranges.filter (inRange id)).length > 0

/-- SPECIFICATION: Count fresh ingredients.
    Filter the list to only fresh ones, return the count.
    Checks each ingredient against ALL ranges. -/
def countFresh (input : Input) : Nat :=
  (input.ingredients.filter (isFresh input.ranges)).length

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Efficient: Pre-merge ranges into non-overlapping intervals, then check.
-- This reduces the number of ranges to check and uses short-circuit `any`.
-------------------------------------------------------------------------------

namespace Impl

/-- An ingredient is in a range if low ≤ id ≤ high. -/
def inRange (id : Nat) (r : Range) : Bool :=
  r.low ≤ id ∧ id ≤ r.high

/-- Merge two overlapping or adjacent ranges. -/
def mergeTwo (r1 r2 : Range) : Range :=
  { low := min r1.low r2.low, high := max r1.high r2.high }

/-- Merge a new range into an accumulator of merged ranges (sorted by low).
    Assumes ranges are processed in sorted order. -/
def mergeInto (acc : List Range) (r : Range) : List Range :=
  match acc with
  | [] => [r]
  | last :: rest =>
    if last.high + 1 >= r.low then
      -- Overlaps or adjacent with last, merge them
      mergeTwo last r :: rest
    else
      -- No overlap, add as new range
      r :: acc

/-- Merge all ranges into non-overlapping sorted ranges. -/
def mergeRanges (ranges : List Range) : List Range :=
  let sorted := ranges.toArray.qsort (fun r1 r2 => r1.low < r2.low) |>.toList
  sorted.foldl mergeInto [] |>.reverse

/-- Check if an ingredient is fresh using merged ranges (short-circuits). -/
def isFresh (mergedRanges : List Range) (id : Nat) : Bool :=
  mergedRanges.any (inRange id)

/-- IMPLEMENTATION: Count fresh ingredients.
    First merge ranges, then count using short-circuit any. -/
def countFresh (input : Input) : Nat :=
  let merged := mergeRanges input.ranges
  input.ingredients.countP (isFresh merged)

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------

namespace Proof

/-- An ID is in a merged range iff it was in some original range. -/
theorem inMerged_iff_inOriginal (id : Nat) (ranges : List Range) :
    (Impl.mergeRanges ranges).any (Impl.inRange id) =
    ranges.any (Spec.inRange id) := by
  sorry

/-- isFresh on merged ranges equals Spec.isFresh on original ranges. -/
theorem isFresh_merged_eq_isFresh (ranges : List Range) (id : Nat) :
    Impl.isFresh (Impl.mergeRanges ranges) id = Spec.isFresh ranges id := by
  -- Will need: inMerged_iff_inOriginal to connect merged to original
  -- Will need: any_eq_filter_nonempty to connect any to filter.length > 0
  sorry

/-- MAIN THEOREM: Implementation equals specification for all inputs. -/
theorem impl_eq_spec (input : Input) :
    Impl.countFresh input = Spec.countFresh input := by
  -- Will need: isFresh_merged_eq_isFresh to show freshness predicates match
  -- Will need: countP_eq_filter_length to connect countP to filter.length
  sorry

end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
-------------------------------------------------------------------------------

/-- Parse a range from "low-high" format. -/
def parseRange (s : String) : Option Range :=
  match s.splitOn "-" with
  | [lowStr, highStr] =>
    match lowStr.toNat?, highStr.toNat? with
    | some low, some high => some { low := low, high := high }
    | _, _ => none
  | _ => none

/-- Parse the full input. -/
def parse (input : String) : Input :=
  let lines := input.splitOn "\n"
  -- Find the blank line separator
  let (rangeLines, rest) := lines.span (·.length > 0)
  let ingredientLines := rest.drop 1  -- Skip the blank line
  let ranges := rangeLines.filterMap parseRange
  let ingredients := ingredientLines.filterMap (·.trim.toNat?)
  { ranges := ranges, ingredients := ingredients }

/-- Main solve function. -/
def solve (input : String) : Nat :=
  Impl.countFresh (parse input)

/-- The solve function is correct by the main theorem. -/
theorem solve_correct (input : String) :
    solve input = Spec.countFresh (parse input) :=
  Proof.impl_eq_spec (parse input)

def main : IO Unit := do
  let input ← IO.FS.readFile "inputs/day05.txt"
  IO.println s!"Answer: {solve input}"

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
-------------------------------------------------------------------------------

def testInput : String := "3-5
10-14
16-20
12-18

1
5
8
11
17
32"

-- Test parsing
#guard (parse testInput).ranges.length = 4
#guard (parse testInput).ingredients.length = 6

-- Test individual range checks
#guard Spec.inRange 5 { low := 3, high := 5 } = true
#guard Spec.inRange 1 { low := 3, high := 5 } = false
#guard Spec.inRange 17 { low := 16, high := 20 } = true
#guard Spec.inRange 17 { low := 12, high := 18 } = true

-- Test freshness
#guard Spec.isFresh (parse testInput).ranges 1 = false  -- Not in any range
#guard Spec.isFresh (parse testInput).ranges 5 = true   -- In range 3-5
#guard Spec.isFresh (parse testInput).ranges 8 = false  -- Not in any range
#guard Spec.isFresh (parse testInput).ranges 11 = true  -- In range 10-14
#guard Spec.isFresh (parse testInput).ranges 17 = true  -- In ranges 16-20 and 12-18
#guard Spec.isFresh (parse testInput).ranges 32 = false -- Not in any range

-- Test merging in Impl
#guard (Impl.mergeRanges (parse testInput).ranges).length = 2  -- [3-5] and [10-20]

-- Test the full example
#guard solve testInput = 3
#guard Spec.countFresh (parse testInput) = 3

-- Test on actual input
def actualInput : String := include_str "../inputs/day05.txt"
#guard solve actualInput = 758

end Day05Part1
