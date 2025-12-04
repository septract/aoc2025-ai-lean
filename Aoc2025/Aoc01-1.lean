/-
  Advent of Code 2025, Day 1: Safe Dial
  Formally verified solution in Lean 4
-/

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-- These types are used by both the specification and implementation.
-------------------------------------------------------------------------------

inductive Direction where
  | left
  | right
deriving Repr, DecidableEq

structure Rotation where
  dir : Direction
  dist : Nat
deriving Repr

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- This section defines the problem mathematically. The spec should be
-- obviously correct by inspection, even if not optimally efficient.
-- We use Fin 100 to encode the dial constraint in the type system.
-------------------------------------------------------------------------------

namespace Spec

/-- A dial position is a natural number in [0, 100).
    Using Fin 100 makes the bounds invariant explicit in the type. -/
abbrev Dial := Fin 100

/-- The starting position is 50. -/
def start : Dial := ⟨50, by decide⟩

/-- The target position we're counting. -/
def zero : Dial := ⟨0, by decide⟩

/-- Rotate a dial right (toward higher numbers) by n clicks.
    Mathematical definition: add n, then take mod 100. -/
def rotateRight (d : Dial) (n : Nat) : Dial :=
  ⟨(d.val + n) % 100, Nat.mod_lt _ (by decide)⟩

/-- Rotate a dial left (toward lower numbers) by n clicks.
    Mathematical definition: subtract n with wraparound.
    We compute this as (d + 100 - n % 100) % 100 to avoid underflow. -/
def rotateLeft (d : Dial) (n : Nat) : Dial :=
  ⟨(d.val + 100 - n % 100) % 100, Nat.mod_lt _ (by decide)⟩

/-- Apply a rotation to a dial according to its direction. -/
def rotate (d : Dial) (rot : Rotation) : Dial :=
  match rot.dir with
  | Direction.right => rotateRight d rot.dist
  | Direction.left => rotateLeft d rot.dist

/-- Compute all dial positions after applying each rotation in sequence.
    Returns the list of positions after each rotation (not including start). -/
def positions (rotations : List Rotation) : List Dial :=
  go start rotations
where
  go (current : Dial) : List Rotation → List Dial
    | [] => []
    | rot :: rest =>
      let next := rotate current rot
      next :: go next rest

/-- SPECIFICATION: The answer is the count of times the dial points to 0
    after any rotation in the sequence.

    This is the formal problem statement. -/
def countZeros (rotations : List Rotation) : Nat :=
  (positions rotations).countP (· == zero)

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- This section contains the actual solution. It may use different
-- representations (e.g., Nat instead of Fin) for efficiency.
-------------------------------------------------------------------------------

namespace Impl

/-- Apply a rotation to a position (using Nat). -/
def applyRotation (pos : Nat) (rot : Rotation) : Nat :=
  match rot.dir with
  | Direction.right => (pos + rot.dist) % 100
  | Direction.left => (pos + 100 - rot.dist % 100) % 100

/-- IMPLEMENTATION: Count zeros by folding through rotations.
    Uses Nat instead of Fin 100 for simplicity. -/
def countZeros (rotations : List Rotation) : Nat :=
  let (_, count) := rotations.foldl (fun (pos, count) rot =>
    let newPos := applyRotation pos rot
    let newCount := if newPos == 0 then count + 1 else count
    (newPos, newCount)
  ) (50, 0)
  count

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-- This section proves that the implementation equals the specification
-- for ALL valid inputs. No `sorry` allowed!
-------------------------------------------------------------------------------

namespace Proof

/-- The implementation's rotation produces the same value as the spec's. -/
theorem applyRotation_eq_rotate (d : Spec.Dial) (rot : Rotation) :
    Impl.applyRotation d.val rot = (Spec.rotate d rot).val := by
  simp only [Impl.applyRotation, Spec.rotate, Spec.rotateRight, Spec.rotateLeft]
  cases rot.dir <;> rfl

/-- Generalized fold equivalence: if we start with matching positions,
    we end with matching positions and counts. -/
theorem fold_equiv (d : Spec.Dial) (c : Nat) (rotations : List Rotation) :
    let implResult := rotations.foldl (fun (pos, count) rot =>
      let newPos := Impl.applyRotation pos rot
      (newPos, if newPos == 0 then count + 1 else count)
    ) (d.val, c)
    let specResult := rotations.foldl (fun (dial, count) rot =>
      let next := Spec.rotate dial rot
      (next, if next == Spec.zero then count + 1 else count)
    ) (d, c)
    implResult.1 = specResult.1.val ∧ implResult.2 = specResult.2 := by
  induction rotations generalizing d c with
  | nil => simp
  | cons rot rest ih =>
    simp only [List.foldl_cons]
    -- Show the step preserves the invariant
    have h_pos := applyRotation_eq_rotate d rot
    -- The conditions are equivalent because both compare to 0
    have h_cond : (Impl.applyRotation d.val rot == 0) = (Spec.rotate d rot == Spec.zero) := by
      rw [h_pos]
      simp only [Spec.zero]
      -- Show that comparing Fin.val to 0 equals comparing Fin to ⟨0, _⟩
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Fin.ext_iff]
    rw [h_cond]
    -- Apply induction hypothesis
    have h_bounded : Impl.applyRotation d.val rot < 100 := by
      simp only [Impl.applyRotation]
      cases rot.dir <;> exact Nat.mod_lt _ (by decide)
    let d' : Spec.Dial := ⟨Impl.applyRotation d.val rot, h_bounded⟩
    have h_d' : d' = Spec.rotate d rot := Fin.ext h_pos
    rw [← h_d']
    exact ih d' _

/-- Helper: generalized fold equals positions.countP with arbitrary start. -/
theorem spec_fold_go_eq_countP (d : Spec.Dial) (c : Nat) (rotations : List Rotation) :
    (rotations.foldl (fun (dial, count) rot =>
      let next := Spec.rotate dial rot
      (next, if next == Spec.zero then count + 1 else count)
    ) (d, c)).2 = c + (Spec.positions.go d rotations).countP (· == Spec.zero) := by
  induction rotations generalizing d c with
  | nil => simp [Spec.positions.go]
  | cons rot rest ih =>
    simp only [List.foldl_cons, Spec.positions.go, List.countP_cons]
    rw [ih]
    -- Split on whether the rotated position is zero
    cases h : (Spec.rotate d rot == Spec.zero)
    · -- not zero
      simp
    · -- is zero
      simp [Nat.add_assoc]; omega

/-- Helper: the spec's fold computes the same as countZeros. -/
theorem spec_fold_eq_countZeros (rotations : List Rotation) :
    (rotations.foldl (fun (dial, count) rot =>
      let next := Spec.rotate dial rot
      (next, if next == Spec.zero then count + 1 else count)
    ) (Spec.start, 0)).2 = Spec.countZeros rotations := by
  simp only [Spec.countZeros, Spec.positions]
  rw [spec_fold_go_eq_countP]
  simp

/-- MAIN THEOREM: Implementation equals specification for all inputs. -/
theorem impl_eq_spec (rotations : List Rotation) :
    Impl.countZeros rotations = Spec.countZeros rotations := by
  simp only [Impl.countZeros]
  have h := fold_equiv Spec.start 0 rotations
  simp only [Spec.start] at h
  rw [h.2]
  exact spec_fold_eq_countZeros rotations

end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
-- This section handles input parsing and running the solution.
-------------------------------------------------------------------------------

def parseRotation (s : String) : Option Rotation := do
  let s := s.trim
  if s.isEmpty then none
  else
    let dir := s.front
    let numStr := s.drop 1
    let num ← numStr.toNat?
    match dir with
    | 'L' => some { dir := Direction.left, dist := num }
    | 'R' => some { dir := Direction.right, dist := num }
    | _ => none

def parse (input : String) : List Rotation :=
  (input.splitOn "\n").filterMap parseRotation

/-- Main solve function: parse input and run implementation. -/
def solve (input : String) : Nat :=
  Impl.countZeros (parse input)

/-- The solve function is correct by the main theorem. -/
theorem solve_correct (input : String) :
    solve input = Spec.countZeros (parse input) :=
  Proof.impl_eq_spec (parse input)

def main : IO Unit := do
  let input ← IO.FS.readFile "inputs/day01.txt"
  IO.println s!"Answer: {solve input}"

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
-- Sanity checks that run at compile time.
-------------------------------------------------------------------------------

def testInput : String := "L68
L30
R48
L5
R60
L55
L1
L99
R14
L82"

-- Test the example from the problem
#guard solve testInput = 3
#guard Spec.countZeros (parse testInput) = 3

-- Verify step-by-step matches problem description
#guard Impl.applyRotation 50 { dir := Direction.left, dist := 68 } = 82
#guard Impl.applyRotation 82 { dir := Direction.left, dist := 30 } = 52
#guard Impl.applyRotation 52 { dir := Direction.right, dist := 48 } = 0
#guard Impl.applyRotation 0 { dir := Direction.left, dist := 5 } = 95
#guard Impl.applyRotation 95 { dir := Direction.right, dist := 60 } = 55
#guard Impl.applyRotation 55 { dir := Direction.left, dist := 55 } = 0
#guard Impl.applyRotation 0 { dir := Direction.left, dist := 1 } = 99
#guard Impl.applyRotation 99 { dir := Direction.left, dist := 99 } = 0
#guard Impl.applyRotation 0 { dir := Direction.right, dist := 14 } = 14
#guard Impl.applyRotation 14 { dir := Direction.left, dist := 82 } = 32

-- Test on actual input
def actualInput : String := include_str "../inputs/day01.txt"
#guard solve actualInput = 1076
