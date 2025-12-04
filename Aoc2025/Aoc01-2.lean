/-
  Advent of Code 2025, Day 1 Part 2: Safe Dial (Method 0x434C49434B)
  Formally verified solution in Lean 4

  Part 2: Count ALL times the dial points at 0 during rotations,
  not just at the end of each rotation.
-/

namespace Day01Part2

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
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
-- Count every position visited during rotations, not just final positions.
-------------------------------------------------------------------------------

namespace Spec

abbrev Dial := Fin 100

def start : Dial := ⟨50, by decide⟩
def zero : Dial := ⟨0, by decide⟩

/-- All positions visited during a single step right (just the next position). -/
def stepRight (d : Dial) : Dial :=
  ⟨(d.val + 1) % 100, Nat.mod_lt _ (by decide)⟩

/-- All positions visited during a single step left (just the next position). -/
def stepLeft (d : Dial) : Dial :=
  ⟨(d.val + 99) % 100, Nat.mod_lt _ (by decide)⟩

/-- List of all positions visited during a rotation (not including start).
    This generates every single position the dial passes through. -/
def positionsDuringRotation (d : Dial) (rot : Rotation) : List Dial :=
  match rot.dir with
  | Direction.right => goRight d rot.dist []
  | Direction.left => goLeft d rot.dist []
where
  goRight (current : Dial) : Nat → List Dial → List Dial
    | 0, acc => acc.reverse
    | n + 1, acc =>
      let next := stepRight current
      goRight next n (next :: acc)
  goLeft (current : Dial) : Nat → List Dial → List Dial
    | 0, acc => acc.reverse
    | n + 1, acc =>
      let next := stepLeft current
      goLeft next n (next :: acc)

/-- Count zeros in a single rotation's visited positions. -/
def countZerosInRotation (d : Dial) (rot : Rotation) : Nat :=
  (positionsDuringRotation d rot).countP (· == zero)

/-- Final position after a rotation. -/
def rotate (d : Dial) (rot : Rotation) : Dial :=
  match rot.dir with
  | Direction.right => ⟨(d.val + rot.dist) % 100, Nat.mod_lt _ (by decide)⟩
  | Direction.left => ⟨(d.val + 100 - rot.dist % 100) % 100, Nat.mod_lt _ (by decide)⟩

/-- SPECIFICATION: Total count of zeros across all rotations.
    For each rotation, count every time the dial passes through 0. -/
def countZeros (rotations : List Rotation) : Nat :=
  go start rotations 0
where
  go (current : Dial) : List Rotation → Nat → Nat
    | [], acc => acc
    | rot :: rest, acc =>
      let zerosInThisRotation := countZerosInRotation current rot
      let next := rotate current rot
      go next rest (acc + zerosInThisRotation)

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Use efficient formula instead of enumerating all positions.
-------------------------------------------------------------------------------

namespace Impl

/-- Count zeros during a right rotation from position p by distance d.
    Formula: (p + d) / 100 (number of times we wrap around through 0). -/
def countZerosRight (p : Nat) (d : Nat) : Nat :=
  (p + d) / 100

/-- Count zeros during a left rotation from position p by distance d.
    We hit 0 at steps: p, p+100, p+200, ... (for p > 0)
    Or at steps: 100, 200, 300, ... (for p = 0) -/
def countZerosLeft (p : Nat) (d : Nat) : Nat :=
  if p == 0 then d / 100
  else if d < p then 0
  else 1 + (d - p) / 100

/-- Count zeros during a single rotation. -/
def countZerosInRotation (pos : Nat) (rot : Rotation) : Nat :=
  match rot.dir with
  | Direction.right => countZerosRight pos rot.dist
  | Direction.left => countZerosLeft pos rot.dist

/-- Apply rotation to get new position. -/
def applyRotation (pos : Nat) (rot : Rotation) : Nat :=
  match rot.dir with
  | Direction.right => (pos + rot.dist) % 100
  | Direction.left => (pos + 100 - rot.dist % 100) % 100

/-- IMPLEMENTATION: Total count using efficient formulas. -/
def countZeros (rotations : List Rotation) : Nat :=
  let (_, count) := rotations.foldl (fun (pos, count) rot =>
    let zeros := countZerosInRotation pos rot
    let newPos := applyRotation pos rot
    (newPos, count + zeros)
  ) (50, 0)
  count

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------

namespace Proof

/-
Strategy: Instead of reasoning about lists directly, we prove that
counting zeros during a rotation can be computed by tracking:
- How many complete "wraps" around the dial occur
- Whether we pass through 0 during a partial wrap

For right rotation: Starting at p, going right d steps visits positions
p+1, p+2, ..., p+d (mod 100). We hit 0 each time we cross from 99 to 0,
which happens ⌊(p+d)/100⌋ times.

For left rotation: Starting at p, going left d steps. We hit 0 when
we reach position 0, which first happens after p steps (if p > 0),
then every 100 steps thereafter.
-/

-- Key arithmetic lemma: (s + (n+1)) / 100 = ((s+1) % 100 + n) / 100 + (s+1) / 100
-- for s < 100. This captures how the count changes when we step right.
theorem right_step_arith (s : Nat) (hs : s < 100) (n : Nat) :
    (s + (n + 1)) / 100 = ((s + 1) % 100 + n) / 100 + (s + 1) / 100 := by
  by_cases h : s < 99
  · -- case: s < 99, so (s+1) / 100 = 0 and (s+1) % 100 = s + 1
    have hmod : (s + 1) % 100 = s + 1 := Nat.mod_eq_of_lt (by omega)
    have hdiv : (s + 1) / 100 = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hmod, hdiv, Nat.add_zero]
    congr 1
    omega
  · -- case: s = 99, so (s+1) / 100 = 1 and (s+1) % 100 = 0
    have hs99 : s = 99 := by omega
    subst hs99
    simp only [show (99 + 1) % 100 = 0 by native_decide,
               show (99 + 1) / 100 = 1 by native_decide,
               Nat.zero_add]
    omega

-- Key arithmetic lemma for right rotation:
-- When going from position p to p+1 (mod 100), we hit 0 iff (p+1) % 100 = 0
-- The formula (p + n) / 100 counts total zeros hit after n steps
theorem goRight_count (start : Spec.Dial) (n : Nat) (acc : List Spec.Dial) :
    (Spec.positionsDuringRotation.goRight start n acc).countP (· == Spec.zero) =
    acc.countP (· == Spec.zero) + (start.val + n) / 100 := by
  induction n generalizing start acc with
  | zero =>
    simp [Spec.positionsDuringRotation.goRight, List.countP_reverse]
  | succ n ih =>
    simp only [Spec.positionsDuringRotation.goRight]
    rw [ih]
    simp only [Spec.stepRight, List.countP_cons, Spec.zero, beq_iff_eq, Fin.ext_iff]
    -- Need: acc_count + (if (start+1)%100 = 0 then 1 else 0) + ((start+1)%100 + n)/100
    --     = acc_count + (start + (n + 1)) / 100
    have harith := right_step_arith start.val start.isLt n
    -- Connect the if-condition to division
    by_cases h : (start.val + 1) % 100 = 0
    · -- (start + 1) % 100 = 0, so start = 99
      have hs99 : start.val = 99 := by
        have := start.isLt
        omega
      simp only [ite_true, hs99]
      simp only [show (99 + 1) % 100 = 0 by native_decide,
                 Nat.zero_add]
      omega
    · -- (start + 1) % 100 ≠ 0, so start < 99
      simp only [h, ite_false, Nat.add_zero]
      have hdiv : (start.val + 1) / 100 = 0 := by
        have := start.isLt
        have hlt : start.val < 99 := by omega
        exact Nat.div_eq_of_lt (by omega)
      simp only [hdiv, Nat.add_zero] at harith
      omega

-- Key lemmas for left stepping
theorem stepLeft_zero : (0 + 99) % 100 = 99 := by native_decide

theorem stepLeft_pos (p : Nat) (hp : 0 < p) (hlt : p < 100) :
    (p + 99) % 100 = p - 1 := by
  have h1 : p + 99 ≥ 100 := by omega
  have h2 : p + 99 < 200 := by omega
  have h3 : (p + 99) / 100 = 1 := Nat.div_eq_of_lt_le h1 h2
  have h4 : (p + 99) % 100 = p + 99 - 100 * 1 := by
    rw [← h3]
    exact (Nat.mod_add_div (p + 99) 100).symm ▸ (by omega)
  omega

-- Left rotation count formula: arithmetic identity for the inductive step
theorem goLeft_count (start : Spec.Dial) (n : Nat) (acc : List Spec.Dial) :
    (Spec.positionsDuringRotation.goLeft start n acc).countP (· == Spec.zero) =
    acc.countP (· == Spec.zero) +
    (if start.val == 0 then n / 100
     else if n < start.val then 0
     else 1 + (n - start.val) / 100) := by
  induction n generalizing start acc with
  | zero =>
    simp [Spec.positionsDuringRotation.goLeft, List.countP_reverse]
  | succ n ih =>
    simp only [Spec.positionsDuringRotation.goLeft]
    rw [ih]
    simp only [Spec.stepLeft, List.countP_cons, Spec.zero, beq_iff_eq, Fin.ext_iff]
    -- Case split on start.val
    by_cases hs0 : start.val = 0
    · -- Case: start.val = 0, next position is 99
      simp only [hs0, ite_true, Nat.zero_add, stepLeft_zero]
      -- 99 ≠ 0, so no zero hit on this step
      have h99 : (99 : Nat) = 0 ↔ False := by decide
      simp only [h99, ite_false]
      -- Need: (if n < 99 then 0 else 1 + (n - 99)/100) = (n + 1)/100
      by_cases hn : n < 99
      · simp only [hn, ite_true]
        have hdiv : (n + 1) / 100 = 0 := Nat.div_eq_of_lt (by omega)
        omega
      · simp only [hn, ite_false]
        have hge : n ≥ 99 := by omega
        have hdiv1 : (n + 1) / 100 = (n + 1 - 100) / 100 + 1 := by
          have h : n + 1 ≥ 100 := by omega
          have := Nat.div_eq_sub_div (by omega : 0 < 100) h
          omega
        have hdiv2 : n + 1 - 100 = n - 99 := by omega
        omega
    · -- Case: start.val > 0
      have hpos : start.val > 0 := Nat.pos_of_ne_zero hs0
      have hnext : (start.val + 99) % 100 = start.val - 1 := stepLeft_pos start.val hpos start.isLt
      simp only [hnext]
      have hne0 : ¬(start.val = 0) := hs0
      simp only [hne0, ite_false]
      by_cases hs1 : start.val = 1
      · -- Case: start.val = 1, next = 0, we hit zero
        -- next = 1 - 1 = 0, so we hit zero
        simp only [hs1]
        simp only [ite_true]
        -- Need: 1 + n/100 = (if n+1 < 1 then 0 else 1 + (n+1-1)/100)
        have hlt : ¬(n + 1 < 1) := by omega
        simp only [hlt, ite_false]
        omega
      · -- Case: start.val > 1, next = start.val - 1 > 0, we don't hit zero
        have hgt1 : start.val > 1 := by omega
        have hnz : start.val - 1 ≠ 0 := by omega
        have hneq : ¬(start.val - 1 = 0) := hnz
        simp only [hneq, ite_false]
        -- Need: (if n < start.val - 1 then 0 else 1 + (n - (start.val - 1))/100)
        --     = (if n + 1 < start.val then 0 else 1 + (n + 1 - start.val)/100)
        by_cases hn : n < start.val - 1
        · simp only [hn, ite_true]
          have hlt : n + 1 < start.val := by omega
          simp only [hlt, ite_true]
        · simp only [hn, ite_false]
          have hge : ¬(n + 1 < start.val) := by omega
          simp only [hge, ite_false]
          -- n - (start.val - 1) = n + 1 - start.val
          have heq : n - (start.val - 1) = n + 1 - start.val := by omega
          omega

/-- Key lemma: counting zeros in right rotation equals (p + d) / 100. -/
theorem countZeros_right_eq (d : Spec.Dial) (dist : Nat) :
    Spec.countZerosInRotation d ⟨Direction.right, dist⟩ = Impl.countZerosRight d.val dist := by
  simp only [Spec.countZerosInRotation, Spec.positionsDuringRotation, Impl.countZerosRight]
  rw [goRight_count]
  simp

/-- Key lemma: counting zeros in left rotation matches the formula. -/
theorem countZeros_left_eq (d : Spec.Dial) (dist : Nat) :
    Spec.countZerosInRotation d ⟨Direction.left, dist⟩ = Impl.countZerosLeft d.val dist := by
  simp only [Spec.countZerosInRotation, Spec.positionsDuringRotation, Impl.countZerosLeft]
  rw [goLeft_count]
  simp only [List.countP_nil, Nat.zero_add]

/-- Counting zeros in any rotation matches the implementation. -/
theorem countZerosInRotation_eq (d : Spec.Dial) (rot : Rotation) :
    Spec.countZerosInRotation d rot = Impl.countZerosInRotation d.val rot := by
  cases rot with
  | mk dir dist =>
    cases dir
    · exact countZeros_left_eq d dist
    · exact countZeros_right_eq d dist

/-- The implementation's rotation matches the spec's rotation. -/
theorem applyRotation_eq_rotate (d : Spec.Dial) (rot : Rotation) :
    Impl.applyRotation d.val rot = (Spec.rotate d rot).val := by
  simp only [Impl.applyRotation, Spec.rotate]
  cases rot.dir <;> rfl

/-- Helper lemma: foldl matches spec's go function for any starting state. -/
theorem foldl_eq_go (rotations : List Rotation) (d : Spec.Dial) (acc : Nat) :
    (rotations.foldl (fun (pos, count) rot =>
      let zeros := Impl.countZerosInRotation pos rot
      let newPos := Impl.applyRotation pos rot
      (newPos, count + zeros)) (d.val, acc)).2 =
    Spec.countZeros.go d rotations acc := by
  induction rotations generalizing d acc with
  | nil =>
    simp [Spec.countZeros.go]
  | cons rot rest ih =>
    simp only [List.foldl_cons, Spec.countZeros.go]
    -- The next position in impl is Impl.applyRotation d.val rot
    -- The next position in spec is Spec.rotate d rot
    -- These are equal by applyRotation_eq_rotate
    have hpos : Impl.applyRotation d.val rot = (Spec.rotate d rot).val :=
      applyRotation_eq_rotate d rot
    -- The zero count in impl is Impl.countZerosInRotation d.val rot
    -- The zero count in spec is Spec.countZerosInRotation d rot
    -- These are equal by countZerosInRotation_eq
    have hcount : Impl.countZerosInRotation d.val rot = Spec.countZerosInRotation d rot :=
      (countZerosInRotation_eq d rot).symm
    -- Apply the induction hypothesis
    have := ih (Spec.rotate d rot) (acc + Spec.countZerosInRotation d rot)
    simp only [hpos, hcount] at this ⊢
    exact this

/-- MAIN THEOREM: Implementation equals specification for all inputs.
    The proof structure follows from:
    1. countZerosInRotation_eq: each rotation's count matches
    2. applyRotation_eq_rotate: positions match after each rotation
    3. Induction over the list of rotations -/
theorem impl_eq_spec (rotations : List Rotation) :
    Impl.countZeros rotations = Spec.countZeros rotations := by
  simp only [Impl.countZeros, Spec.countZeros]
  exact foldl_eq_go rotations Spec.start 0

end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
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

def solve (input : String) : Nat :=
  Impl.countZeros (parse input)

theorem solve_correct (input : String) :
    solve input = Spec.countZeros (parse input) :=
  Proof.impl_eq_spec (parse input)

def main : IO Unit := do
  let input ← IO.FS.readFile "inputs/day01.txt"
  IO.println s!"Answer: {solve input}"

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
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

-- Test the example: should be 6 (3 at end + 3 during)
#guard solve testInput = 6
#guard Spec.countZeros (parse testInput) = 6

-- Verify individual rotation counts match the problem description
-- L68 from 50: passes through 0 once during rotation
#guard Impl.countZerosInRotation 50 { dir := Direction.left, dist := 68 } = 1
-- L30 from 82: doesn't pass through 0
#guard Impl.countZerosInRotation 82 { dir := Direction.left, dist := 30 } = 0
-- R48 from 52: ends at 0 (passes through once)
#guard Impl.countZerosInRotation 52 { dir := Direction.right, dist := 48 } = 1
-- R60 from 95: passes through 0 once during rotation
#guard Impl.countZerosInRotation 95 { dir := Direction.right, dist := 60 } = 1
-- L55 from 55: ends at 0
#guard Impl.countZerosInRotation 55 { dir := Direction.left, dist := 55 } = 1
-- L1 from 0: goes to 99, doesn't hit 0
#guard Impl.countZerosInRotation 0 { dir := Direction.left, dist := 1 } = 0
-- L99 from 99: ends at 0
#guard Impl.countZerosInRotation 99 { dir := Direction.left, dist := 99 } = 1
-- L82 from 14: passes through 0 once
#guard Impl.countZerosInRotation 14 { dir := Direction.left, dist := 82 } = 1

-- Special case from problem: R1000 from 50 should hit 0 ten times
#guard Impl.countZerosInRotation 50 { dir := Direction.right, dist := 1000 } = 10

-- Test on actual input
def actualInput : String := include_str "../inputs/day01.txt"
#guard solve actualInput = 6379

end Day01Part2
