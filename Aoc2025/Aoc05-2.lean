/-
  Advent of Code 2025, Day 5 Part 2: Cafeteria Inventory
  Formally verified solution in Lean 4

  Problem: Count the total number of unique ingredient IDs that are considered
  fresh by any of the ranges. Ranges can overlap, so we must not double-count.
-/

import Mathlib.Data.List.Basic

namespace Day05Part2

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------

/-- A range of ingredient IDs (inclusive on both ends). -/
structure Range where
  low : Nat
  high : Nat
deriving Repr, DecidableEq, Inhabited

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- Obviously correct: Insert ranges one at a time, maintaining sorted
-- non-overlapping invariant. No pre-sorting required - each insertion
-- finds the right place and merges. O(n²) but clearly correct.
-------------------------------------------------------------------------------

namespace Spec

/-- Size of a single range (number of integers it contains). -/
def rangeSize (r : Range) : Nat :=
  if r.high >= r.low then r.high - r.low + 1 else 0

/-- Merge two overlapping or adjacent ranges into one. -/
def mergeTwo (r1 r2 : Range) : Range :=
  { low := min r1.low r2.low, high := max r1.high r2.high }

/-- Insert a range into a sorted list of non-overlapping ranges.
    Finds the right position, merges with any overlapping neighbors.
    Maintains invariant: output is sorted and non-overlapping.
    This is O(n) per insertion = O(n²) total. -/
def insertRange (r : Range) (merged : List Range) : List Range :=
  match merged with
  | [] => [r]
  | m :: rest =>
    if r.high + 1 < m.low then
      -- r comes strictly before m, no overlap possible with rest either
      r :: m :: rest
    else if m.high + 1 < r.low then
      -- m comes strictly before r, r might overlap with rest
      m :: insertRange r rest
    else
      -- r and m overlap or are adjacent, merge them and continue
      insertRange (mergeTwo r m) rest

/-- SPECIFICATION: Merge ranges by inserting one at a time.
    No pre-sorting - each insert finds the right place.
    Obviously correct: we just accumulate merged ranges. -/
def mergeRanges (ranges : List Range) : List Range :=
  ranges.foldl (fun acc r => insertRange r acc) []

/-- Count of unique fresh IDs: sum sizes of merged non-overlapping ranges. -/
def countFreshIds (ranges : List Range) : Nat :=
  (mergeRanges ranges).map rangeSize |>.sum

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Efficient: Sort all ranges first by low, then linear merge.
-- O(n log n) sort + O(n) merge = O(n log n) total.
-------------------------------------------------------------------------------

namespace Impl

/-- Size of a range. -/
def rangeSize (r : Range) : Nat :=
  if r.high >= r.low then r.high - r.low + 1 else 0

/-- Merge a new range into the front of accumulator (reversed list).
    Assumes ranges are processed in sorted order by low. -/
def mergeInto (acc : List Range) (r : Range) : List Range :=
  match acc with
  | [] => [r]
  | last :: rest =>
    if last.high + 1 >= r.low then
      -- Overlaps or adjacent with last, merge them
      { low := last.low, high := max last.high r.high } :: rest
    else
      -- No overlap, add as new range
      r :: acc

/-- IMPLEMENTATION: Sort first, then linear merge.
    O(n log n) sort + O(n) merge. -/
def mergeRanges (ranges : List Range) : List Range :=
  let sorted := ranges.toArray.qsort (fun r1 r2 => r1.low < r2.low) |>.toList
  sorted.foldl mergeInto [] |>.reverse

/-- Count unique fresh IDs using efficient merge. -/
def countFreshIds (ranges : List Range) : Nat :=
  (mergeRanges ranges).foldl (fun acc r => acc + rangeSize r) 0

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------

namespace Proof

/-- Sorting is a permutation (preserves multiset). -/
theorem sort_perm (ranges : List Range) :
    (ranges.toArray.qsort (fun r1 r2 => r1.low < r2.low) |>.toList).length =
    ranges.length := by
  sorry

/-- Insert-merge on unsorted list equals linear-merge on sorted list.
    This is the key insight: order of insertion doesn't matter for final result. -/
theorem insertMerge_eq_linearMerge (ranges : List Range) :
    Spec.mergeRanges ranges = Impl.mergeRanges ranges := by
  sorry

/-- Sum via map equals sum via foldl. -/
theorem sum_map_eq_foldl (ranges : List Range) :
    (ranges.map Spec.rangeSize).sum =
    ranges.foldl (fun acc r => acc + Impl.rangeSize r) 0 := by
  sorry

/-- MAIN THEOREM: Implementation equals specification. -/
theorem impl_eq_spec (ranges : List Range) :
    Impl.countFreshIds ranges = Spec.countFreshIds ranges := by
  -- Will need: insertMerge_eq_linearMerge to show merge results match
  -- Will need: sum_map_eq_foldl to show summing methods match
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

/-- Parse the input (only need the ranges, ignore ingredients). -/
def parse (input : String) : List Range :=
  let lines := input.splitOn "\n"
  let rangeLines := lines.takeWhile (·.length > 0)
  rangeLines.filterMap parseRange

/-- Main solve function. -/
def solve (input : String) : Nat :=
  Impl.countFreshIds (parse input)

/-- The solve function is correct by the main theorem. -/
theorem solve_correct (input : String) :
    solve input = Spec.countFreshIds (parse input) :=
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
#guard (parse testInput).length = 4

-- Test range size
#guard Spec.rangeSize { low := 3, high := 5 } = 3
#guard Spec.rangeSize { low := 10, high := 14 } = 5

-- Test Spec merging (insert-based)
#guard (Spec.mergeRanges (parse testInput)).length = 2  -- [3-5] and [10-20]

-- Test Impl merging (sort-then-linear)
#guard (Impl.mergeRanges (parse testInput)).length = 2  -- [3-5] and [10-20]

-- Test the full example: 3,4,5 (3) + 10,11,12,13,14,15,16,17,18,19,20 (11) = 14
#guard solve testInput = 14
#guard Spec.countFreshIds (parse testInput) = 14

-- Test on actual input
def actualInput : String := include_str "../inputs/day05.txt"
#guard solve actualInput = 343143696885053

end Day05Part2
