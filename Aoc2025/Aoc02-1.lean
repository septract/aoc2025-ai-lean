/-
  Advent of Code 2025, Day 2 Part 1: Invalid Product IDs
  Formally verified solution in Lean 4

  An invalid ID is a number whose decimal representation is some
  sequence of digits repeated twice (e.g., 55, 6464, 123123).
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Batteries.Data.Nat.Digits
import Batteries.Data.String.Lemmas
import Mathlib.Data.String.Lemmas

namespace Day02Part1

-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------

structure Range where
  lo : Nat
  hi : Nat
deriving Repr

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-- An invalid number has its string representation as some pattern repeated twice.
-- We check this directly via string comparison.
-------------------------------------------------------------------------------

namespace Spec

/-- A number is invalid if its string representation is a sequence repeated twice.
    E.g., 55 = "5" ++ "5", 6464 = "64" ++ "64", 123123 = "123" ++ "123" -/
def isInvalid (n : Nat) : Bool :=
  let s := toString n
  let len := s.length
  len > 0 && len % 2 == 0 && s.take (len / 2) == s.drop (len / 2)

/-- Check if a number is in a range (inclusive). -/
def inRange (n : Nat) (r : Range) : Bool :=
  r.lo ≤ n && n ≤ r.hi

/-- SPECIFICATION: Sum of all invalid IDs in a range.
    Naive enumeration - obviously correct but potentially slow for large ranges. -/
def sumInvalidInRange (r : Range) : Nat :=
  if r.hi < r.lo then 0
  else go r.lo r.hi 0
where
  go (cur hi acc : Nat) : Nat :=
    if cur > hi then acc
    else go (cur + 1) hi (if isInvalid cur then acc + cur else acc)
  termination_by hi + 1 - cur

/-- SPECIFICATION: Total sum of invalid IDs across all ranges. -/
def solve (ranges : List Range) : Nat :=
  ranges.foldl (fun acc r => acc + sumInvalidInRange r) 0

end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-- Instead of checking every number in a range, we generate all invalid numbers
-- up to the maximum and filter by ranges. Much more efficient for large ranges.
--
-- Key insight: n is invalid iff n = b × (10^k + 1) where b has exactly k digits.
-- E.g., 123123 = 123 × 1001 = 123 × (10³ + 1)
-------------------------------------------------------------------------------

namespace Impl

/-- Power of 10. -/
def pow10 (k : Nat) : Nat := 10 ^ k

/-- Number of decimal digits in a positive number. -/
def numDigits (n : Nat) : Nat :=
  if n == 0 then 1 else go n 0
where
  go (n acc : Nat) : Nat :=
    if h : n == 0 then acc else go (n / 10) (acc + 1)
  termination_by n
  decreasing_by
    simp_wf
    have hn : n ≠ 0 := by simp_all
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

/-- Generate an invalid number from a base: base × (10^k + 1) where k = digits of base.
    This produces the number formed by repeating 'base' twice in decimal. -/
def toInvalid (base : Nat) : Nat :=
  let k := numDigits base
  base * (pow10 k + 1)

/-- Generate all k-digit bases (numbers from 10^(k-1) to 10^k - 1, or 1-9 for k=1). -/
def basesWithKDigits (k : Nat) : List Nat :=
  if k == 0 then []
  else
    let lo := if k == 1 then 1 else pow10 (k - 1)
    let hi := pow10 k
    (List.range (hi - lo)).map (· + lo)

/-- Generate all invalid numbers whose base has at most maxK digits. -/
def allInvalidsUpToKDigitBase (maxK : Nat) : List Nat :=
  (List.range maxK).flatMap (fun k => (basesWithKDigits (k + 1)).map toInvalid)

/-- Sum of invalid numbers that fall within a range. -/
def sumInvalidInRange (invalids : List Nat) (r : Range) : Nat :=
  invalids.foldl (fun acc n =>
    if r.lo ≤ n && n ≤ r.hi then acc + n else acc
  ) 0

/-- IMPLEMENTATION: Efficiently compute sum by generating all invalid numbers
    and filtering by ranges. -/
def solve (ranges : List Range) : Nat :=
  let maxVal := ranges.foldl (fun acc r => max acc r.hi) 0
  -- Invalid number with k-digit base has 2k digits, so we need bases up to ceil(maxDigits/2)
  let maxK := (numDigits maxVal + 1) / 2
  let invalids := allInvalidsUpToKDigitBase maxK
  ranges.foldl (fun acc r => acc + sumInvalidInRange invalids r) 0

end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
--
-- Proof Strategy:
-- 1. Define a mathematical characterization: n is invalid iff n = b * (10^k + 1)
--    for some k-digit base b.
-- 2. Prove toInvalid produces mathematically invalid numbers (soundness).
-- 3. Prove mathematically invalid numbers can be expressed via toInvalid (completeness).
-- 4. Connect string-based Spec.isInvalid to mathematical characterization.
-- 5. Show both summation methods compute the same result.
--
-- The key lemma requiring string reasoning is isInvalid_eq_isInvalidMath.
-------------------------------------------------------------------------------

namespace Proof

/-! ## Helper lemmas about numDigits -/

/-- numDigits.go accumulator property.
    Used by: numDigits_pos, numDigits_div10, numDigits_go_pos' -/
lemma numDigits_go_add (n acc : Nat) :
    Impl.numDigits.go n acc = Impl.numDigits.go n 0 + acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    unfold Impl.numDigits.go
    split
    · simp
    · rename_i hn
      have hne : n ≠ 0 := by simp_all
      have hdiv : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hne) (by decide)
      rw [ih (n / 10) hdiv (acc + 1), ih (n / 10) hdiv 1]
      omega

/-- numDigits is always positive. -/
lemma numDigits_pos (n : Nat) : 0 < Impl.numDigits n := by
  unfold Impl.numDigits
  split
  · decide
  · rename_i hn
    have hne : n ≠ 0 := by simp_all
    unfold Impl.numDigits.go
    split
    · simp_all
    · rw [numDigits_go_add]
      omega

/-- Helper: 10^k = 10 * 10^(k-1) for k > 0.
    Used by: numDigits_lower_bound, toInvalid_numDigits -/
lemma pow10_succ_pred (k : Nat) (hk : k > 0) : Impl.pow10 k = 10 * Impl.pow10 (k - 1) := by
  cases k with
  | zero => omega
  | succ k' =>
    simp only [Impl.pow10, Nat.pow_succ, Nat.add_sub_cancel]
    exact Nat.mul_comm _ _

/-- For n ≥ 10, numDigits n = numDigits (n/10) + 1. -/
lemma numDigits_div10 (n : Nat) (hn : n ≥ 10) :
    Impl.numDigits n = Impl.numDigits (n / 10) + 1 := by
  have hne_n : n ≠ 0 := by omega
  have hne_div : n / 10 ≠ 0 := by
    have : n / 10 ≥ 1 := Nat.le_div_iff_mul_le (by decide : 0 < 10) |>.mpr (by omega)
    omega
  have hbeq_n : (n == 0) = false := beq_false_of_ne hne_n
  have hbeq_div : (n / 10 == 0) = false := beq_false_of_ne hne_div
  have lhs_eq : Impl.numDigits n = Impl.numDigits.go n 0 := by
    unfold Impl.numDigits; simp only [hbeq_n]; simp
  have go_step : Impl.numDigits.go n 0 = Impl.numDigits.go (n / 10) 1 := by
    rw [Impl.numDigits.go]
    simp only [hbeq_n, Bool.false_eq_true, dite_false, Nat.zero_add]
  have go_acc : Impl.numDigits.go (n / 10) 1 = Impl.numDigits.go (n / 10) 0 + 1 := by
    rw [numDigits_go_add]
  have rhs_eq : Impl.numDigits (n / 10) = Impl.numDigits.go (n / 10) 0 := by
    unfold Impl.numDigits; simp only [hbeq_div]; simp
  rw [lhs_eq, go_step, go_acc, rhs_eq]

/-- For 1 ≤ n < 10, numDigits n = 1. -/
lemma numDigits_lt10 (n : Nat) (hn : n > 0) (hlt : n < 10) : Impl.numDigits n = 1 := by
  unfold Impl.numDigits
  have hne : (n == 0) = false := beq_false_of_ne (by omega : n ≠ 0)
  simp only [hne]
  unfold Impl.numDigits.go
  simp only [hne]
  have hdiv : n / 10 = 0 := Nat.div_eq_of_lt hlt
  simp only [hdiv]
  unfold Impl.numDigits.go
  simp

/-- Lower bound: 10^(numDigits n - 1) ≤ n for n > 0. -/
lemma numDigits_lower_bound (n : Nat) (hn : n > 0) :
    Impl.pow10 (Impl.numDigits n - 1) ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hlt : n < 10
    · -- Base case: n < 10
      have heq : Impl.numDigits n = 1 := numDigits_lt10 n hn hlt
      simp only [heq, Impl.pow10]
      exact hn
    · -- Inductive case: n ≥ 10
      have hge : n ≥ 10 := Nat.not_lt.mp hlt
      have hdiv_pos : n / 10 > 0 := Nat.div_pos hge (by decide)
      have hdiv_lt : n / 10 < n := Nat.div_lt_self hn (by decide)
      have ih_app := ih (n / 10) hdiv_lt hdiv_pos
      rw [numDigits_div10 n hge]
      simp only [Nat.add_sub_cancel]
      have hnd_pos : Impl.numDigits (n / 10) > 0 := numDigits_pos (n / 10)
      rw [pow10_succ_pred (Impl.numDigits (n / 10)) hnd_pos]
      calc 10 * Impl.pow10 (Impl.numDigits (n / 10) - 1)
          ≤ 10 * (n / 10) := Nat.mul_le_mul_left 10 ih_app
        _ ≤ n := Nat.mul_div_le n 10

/-- Upper bound: n < 10^(numDigits n) for n > 0. -/
lemma numDigits_upper_bound (n : Nat) (hn : n > 0) :
    n < Impl.pow10 (Impl.numDigits n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hlt : n < 10
    · -- Base case: n < 10
      have heq : Impl.numDigits n = 1 := numDigits_lt10 n hn hlt
      simp only [heq, Impl.pow10]
      exact hlt
    · -- Inductive case: n ≥ 10
      have hge : n ≥ 10 := Nat.not_lt.mp hlt
      have hdiv_pos : n / 10 > 0 := Nat.div_pos hge (by decide)
      have hdiv_lt : n / 10 < n := Nat.div_lt_self hn (by decide)
      have ih_app := ih (n / 10) hdiv_lt hdiv_pos
      rw [numDigits_div10 n hge]
      simp only [Impl.pow10, Nat.pow_succ]
      rw [Nat.mul_comm]
      have h1 : n < 10 * (n / 10 + 1) := by omega
      have h2 : n / 10 + 1 ≤ Impl.pow10 (Impl.numDigits (n / 10)) := ih_app
      calc n < 10 * (n / 10 + 1) := h1
        _ ≤ 10 * Impl.pow10 (Impl.numDigits (n / 10)) := Nat.mul_le_mul_left 10 h2

/-- For n > 0, numDigits characterizes digit count: 10^(k-1) ≤ n < 10^k where k = numDigits n. -/
lemma numDigits_bounds (n : Nat) (hn : n > 0) :
    Impl.pow10 (Impl.numDigits n - 1) ≤ n ∧ n < Impl.pow10 (Impl.numDigits n) :=
  ⟨numDigits_lower_bound n hn, numDigits_upper_bound n hn⟩

/-! ## Mathematical characterization of invalid numbers -/

/-- A number is mathematically invalid if it equals b * (10^k + 1) for some k-digit b.
    This is equivalent to the string-based definition but easier to reason about. -/
def isInvalidMath (n : Nat) : Bool :=
  -- Try all possible digit counts k (up to half the digits of n)
  let maxK := (Impl.numDigits n + 1) / 2
  (List.range maxK).any (fun k =>
    let k := k + 1  -- k from 1 to maxK
    let divisor := Impl.pow10 k + 1
    n % divisor == 0 &&
    let b := n / divisor
    (if k == 1 then b ≥ 1 else Impl.pow10 (k - 1) ≤ b) && b < Impl.pow10 k
  )

/-- toInvalid always produces a positive result for positive base. -/
lemma toInvalid_pos (b : Nat) (hb : b > 0) : Impl.toInvalid b > 0 := by
  simp only [Impl.toInvalid, Impl.pow10]
  have hnd := numDigits_pos b
  have hpow : 10 ^ Impl.numDigits b > 0 := Nat.pow_pos (by decide : 0 < 10)
  have : 10 ^ Impl.numDigits b + 1 > 0 := by omega
  exact Nat.mul_pos hb this

/-- toInvalid b is divisible by (10^k + 1) where k = numDigits b.
    Used by: toInvalid_satisfies_math -/
lemma toInvalid_divisible (b : Nat) :
    Impl.toInvalid b % (Impl.pow10 (Impl.numDigits b) + 1) = 0 := by
  simp only [Impl.toInvalid]
  exact Nat.mul_mod_left b _

/-- toInvalid b / (10^k + 1) = b where k = numDigits b.
    Used by: toInvalid_satisfies_math, isInvalidMath_iff_toInvalid -/
lemma toInvalid_div (b : Nat) :
    Impl.toInvalid b / (Impl.pow10 (Impl.numDigits b) + 1) = b := by
  simp only [Impl.toInvalid]
  have hdiv : Impl.pow10 (Impl.numDigits b) + 1 > 0 := by
    simp only [Impl.pow10]
    have : 10 ^ Impl.numDigits b > 0 := Nat.pow_pos (by decide)
    omega
  exact Nat.mul_div_left b hdiv

/-! ## Key equivalence theorems -/

/-- Helper: (a-1)(a+1) = a² - 1 for natural numbers when a ≥ 1.
    Used by: toInvalid_numDigits -/
lemma nat_diff_of_squares (a : Nat) (ha : a ≥ 1) : (a - 1) * (a + 1) = a * a - 1 := by
  have expand : (a - 1) * (a + 1) = (a - 1) * a + (a - 1) := by simp [Nat.mul_add]
  have sub_mul : (a - 1) * a = a * a - a := Nat.sub_one_mul a a
  have ha_sq : a ≤ a * a := Nat.le_mul_self a
  have step1 : a * a - a + (a - 1) = a * a - a + a - 1 := (Nat.add_sub_assoc ha (a * a - a)).symm
  rw [expand, sub_mul, step1, Nat.sub_add_cancel ha_sq]

/-- numDigits is uniquely characterized by the bounds: if 10^(m-1) ≤ x < 10^m, then numDigits x = m. -/
lemma numDigits_unique (x m : Nat) (hx : x > 0) (hm : m > 0)
    (hlo : Impl.pow10 (m - 1) ≤ x) (hhi : x < Impl.pow10 m) :
    Impl.numDigits x = m := by
  have ⟨lo, hi⟩ := numDigits_bounds x hx
  -- We have: 10^(numDigits x - 1) ≤ x < 10^(numDigits x)
  -- And:     10^(m - 1) ≤ x < 10^m
  -- Since powers of 10 form a strictly increasing sequence, numDigits x = m
  have hnd_pos := numDigits_pos x
  -- If numDigits x < m: 10^(numDigits x) ≤ 10^(m-1) ≤ x, but x < 10^(numDigits x), contradiction
  -- If numDigits x > m: 10^m ≤ 10^(numDigits x - 1) ≤ x, but x < 10^m, contradiction
  by_cases hlt : Impl.numDigits x < m
  · have h1 : Impl.pow10 (Impl.numDigits x) ≤ Impl.pow10 (m - 1) := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 10)
      omega
    simp only [Impl.pow10] at *
    omega
  · by_cases hgt : Impl.numDigits x > m
    · have h1 : Impl.pow10 m ≤ Impl.pow10 (Impl.numDigits x - 1) := by
        apply Nat.pow_le_pow_right (by decide : 1 ≤ 10)
        omega
      simp only [Impl.pow10] at *
      omega
    · omega

/-- Our numDigits equals the length of the decimal digit list from Mathlib. -/
lemma numDigits_eq_digits_length (n : Nat) (hn : n > 0) :
    Impl.numDigits n = (Nat.digits 10 n).length := by
  -- Both are characterized by: 10^(k-1) ≤ n < 10^k ↔ k digits
  have hne : n ≠ 0 := by omega
  have hlen_pos : (Nat.digits 10 n).length > 0 :=
    List.length_pos_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hne)
  -- Mathlib's characterization: 10^(len-1) ≤ n < 10^len
  have hlen_eq : (Nat.digits 10 n).length = Nat.log 10 n + 1 :=
    Nat.digits_len 10 n (by decide) hne
  have mathlib_lo : 10 ^ ((Nat.digits 10 n).length - 1) ≤ n := by
    rw [hlen_eq, Nat.add_sub_cancel]
    exact Nat.pow_log_le_self 10 hne
  have mathlib_hi : n < 10 ^ (Nat.digits 10 n).length :=
    Nat.lt_base_pow_length_digits (by decide : 1 < 10)
  -- Both bounds match, so the digit counts must be equal
  exact numDigits_unique n (Nat.digits 10 n).length hn hlen_pos mathlib_lo mathlib_hi

/-- Connection between toDigits (big-endian chars) and digits (little-endian nats).
    This is the key bridge between string operations and digit list operations.
    Used by: repr_toInvalid, isInvalid_eq_isInvalidMath -/
lemma toDigits_eq_digits_reverse_map (n : Nat) (hn : n > 0) :
    Nat.toDigits 10 n = (Nat.digits 10 n).reverse.map Nat.digitChar := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h10 : n < 10
    · -- Base case: single digit (n < 10)
      have hne : n ≠ 0 := by omega
      have hdig : Nat.digits 10 n = [n] := Nat.digits_of_lt 10 n hne h10
      rw [hdig, List.reverse_singleton, List.map_cons, List.map_nil]
      exact Nat.toDigits_of_lt_base h10
    · -- Inductive case: n >= 10
      have hge : n ≥ 10 := Nat.not_lt.mp h10
      have hdiv_pos : n / 10 > 0 := Nat.div_pos hge (by decide)
      have hdiv_lt : n / 10 < n := Nat.div_lt_self hn (by decide)
      have ih_app := ih (n / 10) hdiv_lt hdiv_pos
      have hdig : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_eq_cons_digits_div (by decide : 1 < 10) (by omega : n ≠ 0)
      rw [hdig, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      rw [← ih_app]
      have hmod : n % 10 < 10 := Nat.mod_lt n (by decide)
      have hmod_dig : Nat.toDigits 10 (n % 10) = [Nat.digitChar (n % 10)] := Nat.toDigits_of_lt_base hmod
      rw [← hmod_dig]
      -- Goal: toDigits 10 n = toDigits 10 (n/10) ++ toDigits 10 (n % 10)
      have heq : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
      conv_lhs => rw [heq]
      exact (Nat.toDigits_append_toDigits (by decide : 1 < 10) hdiv_pos hmod).symm

/-- The digits of toInvalid b are the digits of b repeated twice. -/
lemma digits_toInvalid (b : Nat) (hb : b > 0) :
    Nat.digits 10 (Impl.toInvalid b) = Nat.digits 10 b ++ Nat.digits 10 b := by
  -- toInvalid b = b * (10^k + 1) = b + 10^k * b where k = numDigits b
  -- By Nat.digits_append_digits: digits b n ++ digits b m = digits b (n + b^len * m)
  -- where len = (digits b n).length
  -- So: digits 10 b ++ digits 10 b = digits 10 (b + 10^len * b)
  -- We need len = numDigits b = k
  have hk := numDigits_eq_digits_length b hb
  have hlen : (Nat.digits 10 b).length = Impl.numDigits b := hk.symm
  -- toInvalid b = b * (10^k + 1) = b + 10^k * b
  have htoi : Impl.toInvalid b = b + 10 ^ Impl.numDigits b * b := by
    simp only [Impl.toInvalid, Impl.pow10]
    ring
  rw [htoi, ← hlen]
  exact (Nat.digits_append_digits (by decide : 0 < 10)).symm

/-- The string representation of toInvalid b is the repr of b repeated twice. -/
lemma repr_toInvalid (b : Nat) (hb : b > 0) :
    Nat.repr (Impl.toInvalid b) = Nat.repr b ++ Nat.repr b := by
  simp only [Nat.repr]
  rw [toDigits_eq_digits_reverse_map (Impl.toInvalid b) (toInvalid_pos b hb)]
  rw [toDigits_eq_digits_reverse_map b hb]
  rw [digits_toInvalid b hb]
  simp only [List.reverse_append, List.map_append, List.asString_append]

/-- toInvalid b has exactly 2k digits when b has k digits. -/
lemma toInvalid_numDigits (b : Nat) (hb : b > 0) :
    Impl.numDigits (Impl.toInvalid b) = 2 * Impl.numDigits b := by
  have hk_pos : Impl.numDigits b > 0 := numDigits_pos b
  have ⟨b_lo, b_hi⟩ := numDigits_bounds b hb
  have htoi_pos : Impl.toInvalid b > 0 := toInvalid_pos b hb
  -- Lower bound
  have lower : Impl.pow10 (2 * Impl.numDigits b - 1) ≤ Impl.toInvalid b := by
    simp only [Impl.toInvalid, Impl.pow10] at *
    have h1 : 10 ^ (Impl.numDigits b - 1) * (10 ^ Impl.numDigits b + 1) ≤ b * (10 ^ Impl.numDigits b + 1) :=
      Nat.mul_le_mul_right _ b_lo
    have h2 : 10 ^ (2 * Impl.numDigits b - 1) ≤ 10 ^ (Impl.numDigits b - 1) * (10 ^ Impl.numDigits b + 1) := by
      have heq : 10 ^ (2 * Impl.numDigits b - 1) = 10 ^ (Impl.numDigits b - 1) * 10 ^ Impl.numDigits b := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [heq]; apply Nat.mul_le_mul_left; omega
    omega
  -- Upper bound
  have upper : Impl.toInvalid b < Impl.pow10 (2 * Impl.numDigits b) := by
    simp only [Impl.toInvalid, Impl.pow10] at *
    have hpow_pos : 10 ^ Impl.numDigits b ≥ 1 := Nat.one_le_pow _ 10 (by decide)
    have h1 : b ≤ 10 ^ Impl.numDigits b - 1 := by omega
    have h2 : b * (10 ^ Impl.numDigits b + 1) ≤ (10 ^ Impl.numDigits b - 1) * (10 ^ Impl.numDigits b + 1) :=
      Nat.mul_le_mul_right _ h1
    have h3 : (10 ^ Impl.numDigits b - 1) * (10 ^ Impl.numDigits b + 1) = 10 ^ (2 * Impl.numDigits b) - 1 := by
      rw [nat_diff_of_squares _ hpow_pos, ← Nat.pow_two, ← Nat.pow_mul, Nat.mul_comm]
    have h4 : 10 ^ (2 * Impl.numDigits b) - 1 < 10 ^ (2 * Impl.numDigits b) := by
      have : 10 ^ (2 * Impl.numDigits b) ≥ 1 := Nat.one_le_pow _ 10 (by decide); omega
    omega
  exact numDigits_unique (Impl.toInvalid b) (2 * Impl.numDigits b) htoi_pos (by omega) lower upper

/-- Soundness: toInvalid produces numbers that satisfy the mathematical characterization. -/
lemma toInvalid_satisfies_math (b : Nat) (hb : b > 0) :
    isInvalidMath (Impl.toInvalid b) = true := by
  simp only [isInvalidMath]
  have htoi_digits := toInvalid_numDigits b hb
  have hk_pos : Impl.numDigits b > 0 := numDigits_pos b
  have ⟨b_lo, b_hi⟩ := numDigits_bounds b hb
  have maxK_ge : (Impl.numDigits (Impl.toInvalid b) + 1) / 2 ≥ Impl.numDigits b := by
    rw [htoi_digits]; omega
  apply List.any_eq_true.mpr
  refine ⟨Impl.numDigits b - 1, ?_, ?_⟩
  · simp only [List.mem_range]; omega
  · have hsimp : Impl.numDigits b - 1 + 1 = Impl.numDigits b := Nat.sub_add_cancel hk_pos
    simp only [hsimp, Impl.pow10]
    have hdiv : Impl.toInvalid b % (10 ^ Impl.numDigits b + 1) = 0 := toInvalid_divisible b
    simp only [hdiv, beq_self_eq_true, Bool.true_and]
    have hquot : Impl.toInvalid b / (10 ^ Impl.numDigits b + 1) = b := toInvalid_div b
    simp only [hquot]
    simp only [Impl.pow10] at b_lo b_hi
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · split <;> simp only [decide_eq_true_eq]
      · omega
      · exact b_lo
    · exact b_hi

/-- Completeness: Numbers satisfying isInvalidMath can be expressed via toInvalid. -/
lemma isInvalidMath_iff_toInvalid (n : Nat) :
    isInvalidMath n = true ↔ ∃ b : Nat, b > 0 ∧ Impl.toInvalid b = n := by
  constructor
  · intro h
    simp only [isInvalidMath] at h
    have ⟨idx, hidx_mem, hpred⟩ := List.any_eq_true.mp h
    simp only [List.mem_range] at hidx_mem
    simp only [Bool.and_eq_true, beq_iff_eq, Impl.pow10] at hpred
    obtain ⟨hdiv, hbounds⟩ := hpred
    have hhi : n / (10 ^ (idx + 1) + 1) < 10 ^ (idx + 1) := by
      simp only [decide_eq_true_eq] at hbounds
      exact hbounds.2
    have hlo_raw := hbounds.1
    refine ⟨n / (10 ^ (idx + 1) + 1), ?_, ?_⟩
    · simp only [Nat.add_sub_cancel] at hlo_raw
      split at hlo_raw
      · have := of_decide_eq_true hlo_raw; omega
      · have hpow : 10 ^ idx ≥ 1 := Nat.one_le_pow _ 10 (by decide)
        have := of_decide_eq_true hlo_raw
        omega
    · simp only [Nat.add_sub_cancel] at hlo_raw
      have hb_pos : n / (10 ^ (idx + 1) + 1) > 0 := by
        split at hlo_raw
        · have := of_decide_eq_true hlo_raw; omega
        · have hpow : 10 ^ idx ≥ 1 := Nat.one_le_pow _ 10 (by decide)
          have := of_decide_eq_true hlo_raw
          omega
      have hb_digits : Impl.numDigits (n / (10 ^ (idx + 1) + 1)) = idx + 1 := by
        apply numDigits_unique _ _ hb_pos (by omega : idx + 1 > 0)
        · simp only [Impl.pow10, Nat.add_sub_cancel]
          split at hlo_raw
          · rename_i hidx_eq
            have hidx_zero : idx = 0 := by omega
            simp only [hidx_zero, Nat.pow_zero] at *
            have := of_decide_eq_true hlo_raw
            omega
          · exact of_decide_eq_true hlo_raw
        · simp only [Impl.pow10]; exact hhi
      simp only [Impl.toInvalid, Impl.pow10]
      rw [hb_digits]
      exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
  · intro ⟨b, hb_pos, hb_eq⟩
    rw [← hb_eq]
    exact toInvalid_satisfies_math b hb_pos

/-- Helper: taking s.length chars from (s ++ t) gives s.
    Used by: isInvalid_eq_isInvalidMath -/
lemma String.take_append_left (s t : String) : (s ++ t).take s.length = s := by
  rw [String.take_eq, String.data_append]
  have h : s.length = s.data.length := String.length_data.symm
  rw [h, List.take_left]
  simp only [String.mk_eq_asString, String.asString_data]

/-- Helper: dropping s.length chars from (s ++ t) gives t.
    Used by: isInvalid_eq_isInvalidMath -/
lemma String.drop_append_left (s t : String) : (s ++ t).drop s.length = t := by
  rw [String.drop_eq, String.data_append]
  have h : s.length = s.data.length := String.length_data.symm
  rw [h, List.drop_left]
  simp only [String.mk_eq_asString, String.asString_data]

/-- Concatenating take and drop reconstructs the original string.
    Used by: repr_repeated_implies_isInvalidMath -/
lemma String.take_append_drop_eq (s : String) (n : Nat) : s.take n ++ s.drop n = s := by
  rw [String.congr_append, String.data_take, String.data_drop]
  simp only [List.take_append_drop]
  rw [String.mk_eq_asString, String.asString_data]

/-- If the string representation of n has equal halves, then the digit list has form L ++ L.
    Used by: repr_repeated_implies_isInvalidMath -/
lemma digits_doubled_of_repr_halves_eq (n k : Nat) (hn : n > 0)
    (hdig_len : (Nat.digits 10 n).length = 2 * k)
    (hdata_eq : (Nat.repr n).data.take k = (Nat.repr n).data.drop k) :
    Nat.digits 10 n = (Nat.digits 10 n).take k ++ (Nat.digits 10 n).take k := by
  -- Key insight: repr.data = (digits.reverse.map digitChar), so equality of halves in
  -- repr.data implies equality of halves in digits.reverse.
  set D := Nat.digits 10 n with hD_def
  -- Step 1: repr.data = D.reverse.map digitChar
  have hrepr_data : (Nat.repr n).data = D.reverse.map Nat.digitChar := by
    simp only [Nat.repr, List.data_asString]
    rw [toDigits_eq_digits_reverse_map n hn]
  -- Step 2: From hdata_eq, derive equality on D.reverse
  have hrev_take_eq_drop : D.reverse.take k = D.reverse.drop k := by
    -- (D.reverse.map digitChar).take k = (D.reverse.map digitChar).drop k
    rw [hrepr_data] at hdata_eq
    rw [← List.map_take, ← List.map_drop] at hdata_eq
    -- Prove lists equal by extensionality
    apply List.ext_getElem
    · -- lengths are equal
      rw [List.length_take, List.length_drop]
      simp only [List.length_reverse, hdig_len]
      omega
    · -- elements are equal
      intro i h1 h2
      have htake_len : (D.reverse.take k).length = k := by
        rw [List.length_take, List.length_reverse, hdig_len]; omega
      have hmapped_eq := congrArg (fun l => l[i]?) hdata_eq
      simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
        Option.map_some, Option.some.injEq] at hmapped_eq
      -- digitChar is injective on valid digits
      have ha_lt : (D.reverse.take k)[i] < 10 := by
        apply Nat.digits_lt_base (by omega)
        exact List.mem_reverse.mp (List.mem_of_mem_take (List.getElem_mem ..))
      have hb_lt : (D.reverse.drop k)[i] < 10 := by
        apply Nat.digits_lt_base (by omega)
        exact List.mem_reverse.mp (List.mem_of_mem_drop (List.getElem_mem ..))
      -- digitChar d = '0' + d for d < 10, so equality of chars implies equality of nats
      have hchar_a : Nat.digitChar (D.reverse.take k)[i] = Char.ofNat (48 + (D.reverse.take k)[i]) := by
        simp only [Nat.digitChar]; interval_cases (D.reverse.take k)[i] <;> rfl
      have hchar_b : Nat.digitChar (D.reverse.drop k)[i] = Char.ofNat (48 + (D.reverse.drop k)[i]) := by
        simp only [Nat.digitChar]; interval_cases (D.reverse.drop k)[i] <;> rfl
      rw [hchar_a, hchar_b] at hmapped_eq
      -- Extract equality of underlying nat values
      have hva : (48 + (D.reverse.take k)[i]).isValidChar := by
        simp only [Nat.isValidChar]; omega
      have hvb : (48 + (D.reverse.drop k)[i]).isValidChar := by
        simp only [Nat.isValidChar]; omega
      simp only [Char.ofNat, hva, hvb, ↓reduceDIte, Char.ofNatAux, Char.mk.injEq] at hmapped_eq
      have hval := congrArg (fun u : UInt32 => u.toBitVec.toNat) hmapped_eq
      simp_all
  -- Step 3: D.reverse has form A ++ A where A = D.reverse.take k
  have hrev_doubled : D.reverse = D.reverse.take k ++ D.reverse.take k := by
    conv_lhs => rw [← List.take_append_drop k D.reverse]
    rw [hrev_take_eq_drop]
  -- Step 4: D = (D.reverse).reverse = (A ++ A).reverse = A.reverse ++ A.reverse
  have hD_eq : D = (D.reverse.take k).reverse ++ (D.reverse.take k).reverse := by
    conv_lhs => rw [← List.reverse_reverse D, hrev_doubled]
    rw [List.reverse_append]
  -- Step 5: D.take k = A.reverse
  have hA_len : (D.reverse.take k).length = k := by
    rw [List.length_take, List.length_reverse, hdig_len]; omega
  have hArev_len : ((D.reverse.take k).reverse).length = k := by simp [hA_len]
  -- Step 6: Show D.take k = A.reverse and conclude
  set A := D.reverse.take k with hA_def
  have htake_eq : D.take k = A.reverse := by
    have h1 : D = A.reverse ++ A.reverse := hD_eq
    have h2 : A.reverse.length = k := hArev_len
    rw [h1, List.take_append_of_le_length (by omega), ← h2, List.take_length]
  calc D = A.reverse ++ A.reverse := hD_eq
    _ = D.take k ++ D.take k := by rw [← htake_eq]

/-- The last element of (digits 10 n).take k equals a specific digit, which is nonzero.
    Used by: repr_repeated_implies_isInvalidMath -/
lemma digits_take_getLast_eq (n k : Nat) (hn : n > 0) (_hk : k > 0)
    (_hdig_len : (Nat.digits 10 n).length = 2 * k)
    (hdig_doubled : Nat.digits 10 n = (Nat.digits 10 n).take k ++ (Nat.digits 10 n).take k)
    (hL_ne : (Nat.digits 10 n).take k ≠ []) :
    ((Nat.digits 10 n).take k).getLast hL_ne ≠ 0 := by
  -- Let L = (digits 10 n).take k
  set L := (Nat.digits 10 n).take k with hL_def
  -- Since n > 0, the last digit of n is nonzero
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hdigits_ne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
  have hlast_ne_zero : (Nat.digits 10 n).getLast hdigits_ne ≠ 0 :=
    Nat.getLast_digit_ne_zero 10 hne
  -- Since digits 10 n = L ++ L and L ≠ [], the last element of L ++ L equals L.getLast
  have hLL_ne : L ++ L ≠ [] := by simp [hL_ne]
  have hLast_eq : (L ++ L).getLast hLL_ne = L.getLast hL_ne :=
    List.getLast_append_of_ne_nil _ hL_ne
  -- The last element of digits 10 n equals the last element of L ++ L
  have hdigits_eq_LL : (Nat.digits 10 n).getLast hdigits_ne = (L ++ L).getLast hLL_ne := by
    congr 1
  -- Chain: L.getLast = (L ++ L).getLast = (digits 10 n).getLast ≠ 0
  rw [← hLast_eq, ← hdigits_eq_LL]
  exact hlast_ne_zero

/-- Elements of (digits 10 n).take k are all less than 10.
    Used by: repr_repeated_implies_isInvalidMath -/
lemma digits_take_lt_base (n k : Nat) (d : Nat) (hd : d ∈ (Nat.digits 10 n).take k) :
    d < 10 := by
  have hmem : d ∈ Nat.digits 10 n := List.mem_of_mem_take hd
  exact Nat.digits_lt_base (by omega) hmem

/-- If L is nonempty with all elements < 10 and last element nonzero, then ofDigits 10 L > 0.
    Used by: repr_repeated_implies_isInvalidMath -/
lemma ofDigits_pos_of_valid (L : List Nat) (hne : L ≠ [])
    (_hvalid : ∀ d ∈ L, d < 10) (hlast : L.getLast hne ≠ 0) :
    Nat.ofDigits 10 L > 0 := by
  -- Use contrapositive: if ofDigits = 0, then all elements are 0
  by_contra h
  push_neg at h
  have h0 : Nat.ofDigits 10 L = 0 := Nat.eq_zero_of_le_zero h
  -- ofDigits 10 L = 0, so all elements are 0
  have hall_zero := Nat.digits_zero_of_eq_zero (by decide : (10 : Nat) ≠ 0) h0
  -- But the last element is nonzero, contradiction
  exact hlast (hall_zero (L.getLast hne) (List.getLast_mem hne))

/-- If a number's string representation is a repeated pattern (s ++ s),
    then the number satisfies isInvalidMath. -/
lemma repr_repeated_implies_isInvalidMath (n : Nat)
    (hlen_pos : (toString n).length > 0)
    (hlen_even : (toString n).length % 2 = 0)
    (hhalves_eq : (toString n).take ((toString n).length / 2) =
                  (toString n).drop ((toString n).length / 2)) :
    isInvalidMath n = true := by
  -- Strategy: Find b such that toInvalid b = n, then use isInvalidMath_iff_toInvalid
  rw [isInvalidMath_iff_toInvalid]
  -- Let k = half length
  set k := (toString n).length / 2 with hk_def
  -- Establish basic facts
  have hn_pos : n > 0 := by
    by_contra h
    push_neg at h
    interval_cases n
    have : (toString (0 : Nat)).length = 1 := by native_decide
    omega
  have hlen_2k : (toString n).length = 2 * k := by
    have h := Nat.div_add_mod (toString n).length 2
    simp only [hlen_even, Nat.add_zero] at h
    omega
  have hk_pos : k > 0 := by omega
  have hdig_len : (Nat.digits 10 n).length = 2 * k := by
    have hrepr_len : (Nat.repr n).length = (Nat.digits 10 n).length := by
      simp only [Nat.repr, String.length, List.data_asString]
      rw [toDigits_eq_digits_reverse_map n hn_pos, List.length_map, List.length_reverse]
    have htoString_eq : (toString n).length = (Nat.repr n).length := rfl
    omega
  -- Define L = first half of digit list
  set L := (Nat.digits 10 n).take k with hL_def
  have hL_len : L.length = k := by rw [hL_def, List.length_take, hdig_len]; omega
  have hL_ne : L ≠ [] := by intro h; rw [h] at hL_len; simp at hL_len; omega
  -- Key: the digit list has the form L ++ L (use helper lemma)
  have hdata_eq : (Nat.repr n).data.take k = (Nat.repr n).data.drop k := by
    -- toString n = Nat.repr n for Nat, so their data are equal
    have hrepr_data : (Nat.repr n).data = (toString n).data := rfl
    rw [hrepr_data]
    have h2 : (toString n).data.take k = ((toString n).take k).data :=
      (String.data_take (toString n) k).symm
    have h3 : (toString n).data.drop k = ((toString n).drop k).data :=
      (String.data_drop (toString n) k).symm
    rw [h2, h3, hhalves_eq]
  have hdig_doubled : Nat.digits 10 n = L ++ L := by
    rw [hL_def]
    exact digits_doubled_of_repr_halves_eq n k hn_pos hdig_len hdata_eq
  -- n = ofDigits 10 (L ++ L) = ofDigits 10 L * (10^k + 1)
  have hn_eq_prod : n = Nat.ofDigits 10 L * (10 ^ k + 1) := by
    calc n = Nat.ofDigits 10 (Nat.digits 10 n) := (Nat.ofDigits_digits 10 n).symm
         _ = Nat.ofDigits 10 (L ++ L) := by rw [hdig_doubled]
         _ = Nat.ofDigits 10 L + 10 ^ L.length * Nat.ofDigits 10 L := Nat.ofDigits_append
         _ = Nat.ofDigits 10 L * (10 ^ L.length + 1) := by ring
         _ = Nat.ofDigits 10 L * (10 ^ k + 1) := by rw [hL_len]
  -- Set b = ofDigits 10 L
  set b := Nat.ofDigits 10 L with hb_def
  -- L is a valid digit list
  have hL_valid : ∀ d ∈ L, d < 10 := fun d hd => digits_take_lt_base n k d (hL_def ▸ hd)
  -- Last element of L is nonzero (use helper lemma)
  have hL_take_ne : (Nat.digits 10 n).take k ≠ [] := hL_def ▸ hL_ne
  have hL_last_nonzero : L.getLast hL_ne ≠ 0 := by
    have h := digits_take_getLast_eq n k hn_pos hk_pos hdig_len (hL_def ▸ hdig_doubled) hL_take_ne
    simp only [← hL_def] at h
    convert h
  -- digits 10 b = L
  have hdig_b : Nat.digits 10 b = L := by
    rw [hb_def]
    have hlast_forall : ∀ (h : L ≠ []), L.getLast h ≠ 0 := fun _ => hL_last_nonzero
    exact Nat.digits_ofDigits 10 (by omega) L hL_valid hlast_forall
  -- numDigits b = k
  have hnd_b : Impl.numDigits b = k := by
    rw [numDigits_eq_digits_length]
    · rw [hdig_b, hL_len]
    · exact ofDigits_pos_of_valid L hL_ne hL_valid hL_last_nonzero
  -- Provide witness b
  use b
  constructor
  · -- b > 0
    exact ofDigits_pos_of_valid L hL_ne hL_valid hL_last_nonzero
  · -- toInvalid b = n
    rw [Impl.toInvalid, hnd_b]
    exact hn_eq_prod.symm

/-- The string-based isInvalid equals the mathematical characterization.
    This is the core lemma connecting the spec to the implementation. -/
lemma isInvalid_eq_isInvalidMath (n : Nat) :
    Spec.isInvalid n = isInvalidMath n := by
  -- Both are Bool, so prove equality by showing ↔ on true cases
  apply Bool.eq_iff_iff.mpr
  constructor
  · -- Direction 1: Spec.isInvalid n = true → isInvalidMath n = true
    intro hspec
    simp only [Spec.isInvalid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hspec
    obtain ⟨⟨hlen_pos, hlen_even⟩, hhalves_eq⟩ := hspec
    exact repr_repeated_implies_isInvalidMath n hlen_pos hlen_even hhalves_eq
  · intro hmath
    have ⟨b, hb_pos, hb_eq⟩ := isInvalidMath_iff_toInvalid n |>.mp hmath
    rw [← hb_eq]
    -- Now show Spec.isInvalid (toInvalid b) = true
    simp only [Spec.isInvalid]
    have hrep := repr_toInvalid b hb_pos
    -- toString n = Nat.repr n for Nat
    have hts : toString (Impl.toInvalid b) = Nat.repr (Impl.toInvalid b) := rfl
    have htsb : toString b = Nat.repr b := rfl
    rw [hts, hrep]
    -- Now goal is about (repr b ++ repr b)
    -- Need to show: length > 0 ∧ length even ∧ first half = second half
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hne : b ≠ 0 := by omega
    have hlen_pos : (Nat.repr b).length > 0 := by
      simp only [Nat.repr]
      have hdig : Nat.digits 10 b ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
      rw [toDigits_eq_digits_reverse_map b hb_pos]
      rw [List.length_asString, List.length_map, List.length_reverse]
      exact List.length_pos_of_ne_nil hdig
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- length > 0
      simp only [String.length_append]
      omega
    · -- length is even
      simp only [String.length_append]
      omega
    · -- first half = second half
      have hlen : (Nat.repr b ++ Nat.repr b).length = 2 * (Nat.repr b).length := by
        simp only [String.length_append]; ring
      have hdiv : (Nat.repr b ++ Nat.repr b).length / 2 = (Nat.repr b).length := by
        rw [hlen]; omega
      rw [hdiv]
      -- (s ++ s).take s.length = s and (s ++ s).drop s.length = s
      rw [String.take_append_left, String.drop_append_left]

/-- Spec.isInvalid n = true iff n = toInvalid b for some b > 0. -/
lemma isInvalid_iff_toInvalid (n : Nat) :
    Spec.isInvalid n = true ↔ ∃ b : Nat, b > 0 ∧ Impl.toInvalid b = n := by
  rw [isInvalid_eq_isInvalidMath]
  exact isInvalidMath_iff_toInvalid n

/-! ## Summation equivalence -/

/-- Helper: Spec.sumInvalidInRange.go accumulates sum of invalids in range.
    Used by: sumInvalidInRange_eq -/
lemma sumInvalidInRange_go_acc (cur hi acc : Nat) :
    Spec.sumInvalidInRange.go cur hi acc = acc + Spec.sumInvalidInRange.go cur hi 0 := by
  generalize hm : hi + 1 - cur = m
  induction m generalizing cur acc with
  | zero =>
    have hgt : cur > hi := by omega
    unfold Spec.sumInvalidInRange.go
    simp only [hgt, ↓reduceIte, Nat.add_zero]
  | succ n ih =>
    by_cases hgt : cur > hi
    · unfold Spec.sumInvalidInRange.go
      simp only [hgt, ↓reduceIte, Nat.add_zero]
    · unfold Spec.sumInvalidInRange.go
      simp only [hgt, ↓reduceIte]
      have hn : hi + 1 - (cur + 1) = n := by omega
      split
      · rw [ih (cur + 1) (acc + cur) hn, ih (cur + 1) (0 + cur) hn]
        omega
      · rw [ih (cur + 1) acc hn, ih (cur + 1) 0 hn]

/-- Helper: Impl.sumInvalidInRange accumulates correctly.
    Used by: sumInvalidInRange_eq -/
lemma impl_sumInvalidInRange_acc (invalids : List Nat) (r : Range) (acc : Nat) :
    invalids.foldl (fun a n => if r.lo ≤ n && n ≤ r.hi then a + n else a) acc =
    acc + Impl.sumInvalidInRange invalids r := by
  simp only [Impl.sumInvalidInRange]
  induction invalids generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    split
    · rw [ih, ih (acc := 0 + h)]
      ring
    · rw [ih, ih (acc := 0)]

/-- Helper: Impl sum equals list sum over filtered elements.
    Used by: sumInvalidInRange_eq -/
lemma impl_sumInvalidInRange_eq_filter (invalids : List Nat) (r : Range) :
    Impl.sumInvalidInRange invalids r =
    (invalids.filter (fun n => r.lo ≤ n && n ≤ r.hi)).sum := by
  induction invalids with
  | nil => simp [Impl.sumInvalidInRange]
  | cons h t ih =>
    simp only [Impl.sumInvalidInRange, List.foldl_cons]
    rw [List.filter_cons]
    split
    · simp only [List.sum_cons]
      rw [impl_sumInvalidInRange_acc, ← ih]
      simp only [Impl.sumInvalidInRange]
      ring
    · exact ih

/-- Helper: Spec.sumInvalidInRange.go equals sum over filtered range.
    Used by: sumInvalidInRange_eq -/
lemma spec_go_eq_filter_sum (cur hi : Nat) :
    Spec.sumInvalidInRange.go cur hi 0 =
    ((List.range' cur (hi + 1 - cur)).filter Spec.isInvalid).sum := by
  generalize hm : hi + 1 - cur = m
  induction m generalizing cur with
  | zero =>
    have hgt : cur > hi := by omega
    unfold Spec.sumInvalidInRange.go
    simp only [hgt, ↓reduceIte]
    -- List.range' cur 0 = [] by definition
    rfl
  | succ n ih =>
    by_cases hgt : cur > hi
    · unfold Spec.sumInvalidInRange.go
      simp only [hgt, ↓reduceIte]
      have : hi + 1 - cur = 0 := by omega
      omega
    · unfold Spec.sumInvalidInRange.go
      simp only [hgt, ↓reduceIte]
      have hn : hi + 1 - (cur + 1) = n := by omega
      -- range' cur (n+1) = cur :: range' (cur+1) n
      rw [List.range'_succ, List.filter_cons]
      split
      · simp only [List.sum_cons]
        rw [sumInvalidInRange_go_acc, ih (cur + 1) hn]
        ring
      · rw [sumInvalidInRange_go_acc, ih (cur + 1) hn]
        simp

/-- Helper: Spec.sumInvalidInRange equals sum over filtered range.
    Used by: sumInvalidInRange_eq -/
lemma spec_sumInvalidInRange_eq_filter (r : Range) :
    Spec.sumInvalidInRange r =
    ((List.range' r.lo (r.hi + 1 - r.lo)).filter Spec.isInvalid).sum := by
  simp only [Spec.sumInvalidInRange]
  split
  · -- r.hi < r.lo case
    have : r.hi + 1 - r.lo = 0 := by omega
    simp [this]
  · -- normal case
    exact spec_go_eq_filter_sum r.lo r.hi

/-- Helper: membership in range' list.
    Used by: sumInvalidInRange_eq -/
lemma mem_range'_iff (n start len : Nat) :
    n ∈ List.range' start len ↔ start ≤ n ∧ n < start + len := by
  simp only [List.mem_range']
  constructor
  · intro ⟨i, hi_lt, heq⟩
    omega
  · intro ⟨hlo, hhi⟩
    exact ⟨n - start, by omega, by omega⟩

/-- Both summation methods produce equal results.
    The key insight is that both methods sum the same set of numbers:
    {n ∈ [lo, hi] : isInvalid n}.
    Used by: impl_eq_spec

    PROOF STRATEGY:
    - Spec iterates [lo, hi] and sums those where isInvalid
    - Impl iterates invalids and sums those in [lo, hi]
    - By completeness: every invalid in [lo, hi] is in the invalids list
    - By soundness: every item in invalids is invalid
    - By nodup: no duplicates in invalids
    - Therefore both sum the same set: {n : lo ≤ n ≤ hi ∧ isInvalid n} -/
lemma sumInvalidInRange_eq (r : Range) (invalids : List Nat)
    (hcomplete : ∀ n, r.lo ≤ n → n ≤ r.hi → Spec.isInvalid n = true → n ∈ invalids)
    (hsound : ∀ n, n ∈ invalids → Spec.isInvalid n = true)
    (hnodup : invalids.Nodup) :
    Spec.sumInvalidInRange r = Impl.sumInvalidInRange invalids r := by
  -- Convert both to filtered list sums
  rw [spec_sumInvalidInRange_eq_filter, impl_sumInvalidInRange_eq_filter]
  -- Define the two filtered lists
  set specList := (List.range' r.lo (r.hi + 1 - r.lo)).filter Spec.isInvalid with hspec
  set implList := invalids.filter (fun n => r.lo ≤ n && n ≤ r.hi) with himpl
  -- Show they have the same elements (as Finsets, since both are nodup)
  -- First show both are nodup
  have hspec_nodup : specList.Nodup := List.Nodup.filter _ (List.nodup_range' ..)
  have himpl_nodup : implList.Nodup := List.Nodup.filter _ hnodup
  -- Show same elements: n ∈ specList ↔ n ∈ implList
  have hmem : ∀ n, n ∈ specList ↔ n ∈ implList := by
    intro n
    simp only [hspec, himpl, List.mem_filter, mem_range'_iff, Bool.and_eq_true,
               decide_eq_true_eq]
    constructor
    · intro ⟨⟨hlo, hhi⟩, hinv⟩
      have hle : n ≤ r.hi := by omega
      exact ⟨hcomplete n hlo hle hinv, hlo, hle⟩
    · intro ⟨hmem, hlo, hhi⟩
      exact ⟨⟨hlo, by omega⟩, hsound n hmem⟩
  -- Two nodup lists with same elements have the same sum
  have hperm : specList.Perm implList :=
    (List.perm_ext_iff_of_nodup hspec_nodup himpl_nodup).mpr hmem
  exact List.Perm.sum_eq hperm

/-- Helper: b is in basesWithKDigits (numDigits b) for any positive b.
    Used by: allInvalids_complete -/
lemma mem_basesWithKDigits_self (b : Nat) (hb : b > 0) :
    b ∈ Impl.basesWithKDigits (Impl.numDigits b) := by
  have hk_pos : Impl.numDigits b > 0 := numDigits_pos b
  have ⟨hlo, hhi⟩ := numDigits_bounds b hb
  simp only [Impl.basesWithKDigits]
  have hk_ne : (Impl.numDigits b == 0) = false := by simp; omega
  simp only [hk_ne, Bool.false_eq_true, ↓reduceIte]
  -- Need to find i such that i < hi - lo and i + lo = b
  by_cases hk1 : Impl.numDigits b = 1
  · -- k = 1 case: lo = 1, hi = 10
    simp only [hk1, beq_self_eq_true, ↓reduceIte,
               Impl.pow10, List.mem_map, List.mem_range]
    simp only [Impl.pow10, hk1] at hlo hhi
    refine ⟨b - 1, ?_, ?_⟩ <;> omega
  · -- k > 1 case: lo = 10^(k-1), hi = 10^k
    have hk_ne1 : (Impl.numDigits b == 1) = false := by simp; omega
    simp only [hk_ne1, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_range]
    simp only [Impl.pow10] at hlo hhi ⊢
    refine ⟨b - 10 ^ (Impl.numDigits b - 1), ?_, ?_⟩ <;> omega

/-- The invalid list generated by Impl contains all invalid numbers up to the max. -/
lemma allInvalids_complete (maxK : Nat) (n : Nat) (hn : Spec.isInvalid n = true)
    (hdigits : Impl.numDigits n ≤ 2 * maxK) :
    n ∈ Impl.allInvalidsUpToKDigitBase maxK := by
  -- Get b such that n = toInvalid b
  have ⟨b, hb_pos, hb_eq⟩ := isInvalid_iff_toInvalid n |>.mp hn
  -- numDigits n = 2 * numDigits b
  have hn_digits : Impl.numDigits n = 2 * Impl.numDigits b := by
    rw [← hb_eq]
    exact toInvalid_numDigits b hb_pos
  -- So numDigits b ≤ maxK
  have hb_digits : Impl.numDigits b ≤ maxK := by omega
  -- b is in basesWithKDigits (numDigits b)
  have hb_mem : b ∈ Impl.basesWithKDigits (Impl.numDigits b) := mem_basesWithKDigits_self b hb_pos
  -- n = toInvalid b is in allInvalidsUpToKDigitBase maxK
  simp only [Impl.allInvalidsUpToKDigitBase, List.mem_flatMap, List.mem_range, List.mem_map]
  -- Need k < maxK with b ∈ basesWithKDigits (k + 1) and toInvalid b = n
  -- Use k = numDigits b - 1
  have hk_pos : Impl.numDigits b > 0 := numDigits_pos b
  refine ⟨Impl.numDigits b - 1, ?_, b, ?_, ?_⟩
  · omega  -- numDigits b - 1 < maxK
  · simp only [Nat.sub_add_cancel hk_pos]; exact hb_mem
  · exact hb_eq

/-- Helper: bases in basesWithKDigits are positive.
    Used by: allInvalids_sound -/
lemma basesWithKDigits_pos (k : Nat) (_ : k > 0) (b : Nat)
    (hb : b ∈ Impl.basesWithKDigits k) : b > 0 := by
  simp only [Impl.basesWithKDigits] at hb
  split at hb
  · simp at hb  -- k = 0 case: empty list, contradiction
  · -- k ≠ 0 case
    rename_i hk_ne
    simp only [List.mem_map, List.mem_range] at hb
    rcases hb with ⟨i, _, rfl⟩
    -- b = i + lo, where lo ≥ 1
    have hlo : (if (k == 1) = true then 1 else Impl.pow10 (k - 1)) ≥ 1 := by
      split
      · omega
      · exact Nat.one_le_pow _ 10 (by decide)
    omega

/-- Helper: if isInvalidMath n = true, then Spec.isInvalid n = true.
    This is direction 2 of isInvalid_eq_isInvalidMath, extracted for use before that equality is fully proved.
    Used by: allInvalids_sound -/
lemma isInvalidMath_implies_isInvalid (n : Nat) (h : isInvalidMath n = true) :
    Spec.isInvalid n = true := by
  -- By isInvalidMath_iff_toInvalid, ∃ b > 0 with n = toInvalid b
  -- By repr_toInvalid, toString n = toString b ++ toString b
  -- This satisfies the Spec.isInvalid predicate
  have ⟨b, hb_pos, hb_eq⟩ := isInvalidMath_iff_toInvalid n |>.mp h
  rw [← hb_eq]
  simp only [Spec.isInvalid]
  have hrep := repr_toInvalid b hb_pos
  have hts : toString (Impl.toInvalid b) = Nat.repr (Impl.toInvalid b) := rfl
  rw [hts, hrep]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hne : b ≠ 0 := by omega
  have hlen_pos : (Nat.repr b).length > 0 := by
    simp only [Nat.repr]
    have hdig : Nat.digits 10 b ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
    rw [toDigits_eq_digits_reverse_map b hb_pos]
    rw [List.length_asString, List.length_map, List.length_reverse]
    exact List.length_pos_of_ne_nil hdig
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [String.length_append]; omega
  · simp only [String.length_append]; omega
  · have hlen : (Nat.repr b ++ Nat.repr b).length = 2 * (Nat.repr b).length := by
      simp only [String.length_append]; ring
    have hdiv : (Nat.repr b ++ Nat.repr b).length / 2 = (Nat.repr b).length := by
      rw [hlen]; omega
    rw [hdiv, String.take_append_left, String.drop_append_left]

/-- All numbers in the invalid list satisfy isInvalid.
    Used by: impl_eq_spec -/
lemma allInvalids_sound (maxK : Nat) (n : Nat)
    (hmem : n ∈ Impl.allInvalidsUpToKDigitBase maxK) :
    Spec.isInvalid n = true := by
  -- Extract b from membership: n = toInvalid b for some b in basesWithKDigits
  simp only [Impl.allInvalidsUpToKDigitBase, List.mem_flatMap, List.mem_range,
             List.mem_map] at hmem
  obtain ⟨k, hk_lt, b, hb_mem, heq⟩ := hmem
  -- b is positive since it's in basesWithKDigits (k + 1) and k + 1 > 0
  have hb_pos : b > 0 := basesWithKDigits_pos (k + 1) (by omega) b hb_mem
  -- toInvalid b satisfies isInvalidMath
  have hmath : isInvalidMath (Impl.toInvalid b) = true := toInvalid_satisfies_math b hb_pos
  -- Since n = toInvalid b, isInvalidMath n = true
  rw [heq] at hmath
  -- By isInvalidMath_implies_isInvalid, Spec.isInvalid n = true
  exact isInvalidMath_implies_isInvalid n hmath

/-- Helper: toInvalid is injective for positive bases.
    Used by: allInvalids_nodup -/
lemma toInvalid_injective (b1 b2 : Nat) (hb1 : b1 > 0) (hb2 : b2 > 0)
    (heq : Impl.toInvalid b1 = Impl.toInvalid b2) : b1 = b2 := by
  simp only [Impl.toInvalid, Impl.pow10] at heq
  -- toInvalid b = b * (10^k + 1) where k = numDigits b
  -- If b1 * (10^k1 + 1) = b2 * (10^k2 + 1), we need k1 = k2 and b1 = b2
  -- First show k1 = k2 using numDigits equality via toInvalid_numDigits
  have hd1 : Impl.numDigits (Impl.toInvalid b1) = 2 * Impl.numDigits b1 := toInvalid_numDigits b1 hb1
  have hd2 : Impl.numDigits (Impl.toInvalid b2) = 2 * Impl.numDigits b2 := toInvalid_numDigits b2 hb2
  have hd_eq : Impl.numDigits (Impl.toInvalid b1) = Impl.numDigits (Impl.toInvalid b2) := by
    simp only [Impl.toInvalid, Impl.pow10] at heq ⊢
    rw [heq]
  rw [hd1, hd2] at hd_eq
  have hk_eq : Impl.numDigits b1 = Impl.numDigits b2 := by omega
  -- Now with k1 = k2, we have b1 * (10^k + 1) = b2 * (10^k + 1)
  -- So b1 = b2
  rw [hk_eq] at heq
  have hdiv_pos : 10 ^ Impl.numDigits b2 + 1 > 0 := by
    have : 10 ^ Impl.numDigits b2 > 0 := Nat.pow_pos (by decide)
    omega
  exact Nat.eq_of_mul_eq_mul_right hdiv_pos heq

/-- Helper: basesWithKDigits produces a nodup list.
    Used by: allInvalids_nodup -/
lemma basesWithKDigits_nodup (k : Nat) : (Impl.basesWithKDigits k).Nodup := by
  simp only [Impl.basesWithKDigits]
  split
  · exact List.nodup_nil
  · split
    · apply List.Nodup.map (fun a b h => by omega) List.nodup_range
    · apply List.Nodup.map (fun a b h => by omega) List.nodup_range

/-- Helper: toInvalid is injective on elements of basesWithKDigits.
    Used by: basesWithKDigits_map_toInvalid_nodup -/
lemma toInvalid_injective_on_basesWithKDigits (k : Nat) (hk : k > 0) (b1 b2 : Nat)
    (hb1 : b1 ∈ Impl.basesWithKDigits k) (hb2 : b2 ∈ Impl.basesWithKDigits k)
    (heq : Impl.toInvalid b1 = Impl.toInvalid b2) : b1 = b2 := by
  have hb1_pos : b1 > 0 := basesWithKDigits_pos k hk b1 hb1
  have hb2_pos : b2 > 0 := basesWithKDigits_pos k hk b2 hb2
  exact toInvalid_injective b1 b2 hb1_pos hb2_pos heq

/-- Helper: map of toInvalid on basesWithKDigits is nodup.
    Used by: allInvalids_nodup -/
lemma basesWithKDigits_map_toInvalid_nodup (k : Nat) (hk : k > 0) :
    ((Impl.basesWithKDigits k).map Impl.toInvalid).Nodup := by
  rw [List.nodup_map_iff_inj_on (basesWithKDigits_nodup k)]
  intro b1 hb1 b2 hb2 heq
  exact toInvalid_injective_on_basesWithKDigits k hk b1 b2 hb1 hb2 heq

/-- Helper: numDigits of bases in basesWithKDigits equals k.
    Used by: allInvalids_nodup -/
lemma basesWithKDigits_numDigits (k : Nat) (hk : k > 0) (b : Nat)
    (hb : b ∈ Impl.basesWithKDigits k) : Impl.numDigits b = k := by
  simp only [Impl.basesWithKDigits] at hb
  have hk_ne : (k == 0) = false := by simp; omega
  simp only [hk_ne, Bool.false_eq_true, ↓reduceIte] at hb
  simp only [List.mem_map, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  split at hi
  · -- k = 1 case: b = i + 1 where i < 9
    have hk1 : k = 1 := by simp_all
    subst hk1
    simp only [beq_self_eq_true, ↓reduceIte]
    have hb_pos : i + 1 > 0 := by omega
    simp only [Impl.pow10] at hi
    have hlo : 10 ^ (1 - 1) ≤ i + 1 := by simp
    have hhi : i + 1 < 10 ^ 1 := by simp; omega
    exact numDigits_unique (i + 1) 1 hb_pos (by omega) hlo hhi
  · -- k > 1 case: b = i + 10^(k-1) where i < 10^k - 10^(k-1)
    have hk_gt1 : k > 1 := by simp_all; omega
    have hk_ne1 : (k == 1) = false := by simp; omega
    simp only [hk_ne1, Bool.false_eq_true, ↓reduceIte]
    simp only [Impl.pow10] at hi
    have hb_pos : i + 10 ^ (k - 1) > 0 := by
      have : 10 ^ (k - 1) > 0 := Nat.pow_pos (by omega)
      omega
    have hlo : 10 ^ (k - 1) ≤ i + 10 ^ (k - 1) := by omega
    have hhi : i + 10 ^ (k - 1) < 10 ^ k := by omega
    exact numDigits_unique (i + 10 ^ (k - 1)) k hb_pos hk hlo hhi

/-- Helper: invalids from different digit classes don't overlap.
    Used by: allInvalids_nodup -/
lemma invalids_disjoint (k1 k2 : Nat) (hk1 : k1 > 0) (hk2 : k2 > 0) (hne : k1 ≠ k2)
    (n : Nat) (hn1 : n ∈ (Impl.basesWithKDigits k1).map Impl.toInvalid)
    (hn2 : n ∈ (Impl.basesWithKDigits k2).map Impl.toInvalid) : False := by
  simp only [List.mem_map] at hn1 hn2
  obtain ⟨b1, hb1_mem, hb1_eq⟩ := hn1
  obtain ⟨b2, hb2_mem, hb2_eq⟩ := hn2
  have hb1_pos : b1 > 0 := basesWithKDigits_pos k1 hk1 b1 hb1_mem
  have hb2_pos : b2 > 0 := basesWithKDigits_pos k2 hk2 b2 hb2_mem
  have hd1 : Impl.numDigits b1 = k1 := basesWithKDigits_numDigits k1 hk1 b1 hb1_mem
  have hd2 : Impl.numDigits b2 = k2 := basesWithKDigits_numDigits k2 hk2 b2 hb2_mem
  have heq : Impl.toInvalid b1 = Impl.toInvalid b2 := by rw [hb1_eq, hb2_eq]
  have hb_eq : b1 = b2 := toInvalid_injective b1 b2 hb1_pos hb2_pos heq
  rw [hb_eq, hd2] at hd1
  exact hne hd1.symm

/-- Helper: allInvalidsUpToKDigitBase produces a list with no duplicates.
    Used by: impl_eq_spec -/
lemma allInvalids_nodup (maxK : Nat) : (Impl.allInvalidsUpToKDigitBase maxK).Nodup := by
  simp only [Impl.allInvalidsUpToKDigitBase]
  rw [List.nodup_flatMap]
  constructor
  · -- Each inner list is nodup
    intro k hk
    simp only [List.mem_range] at hk
    exact basesWithKDigits_map_toInvalid_nodup (k + 1) (by omega)
  · -- Inner lists are pairwise disjoint
    apply List.Pairwise.imp _ List.pairwise_lt_range
    intro k1 k2 hlt
    simp only [Function.onFun]
    intro n hn1 hn2
    exact invalids_disjoint (k1 + 1) (k2 + 1) (by omega) (by omega) (by omega) n hn1 hn2

/-- Helper: numDigits is monotonic for positive numbers.
    Used by: impl_eq_spec -/
lemma numDigits_mono (n m : Nat) (hn : n > 0) (hle : n ≤ m) :
    Impl.numDigits n ≤ Impl.numDigits m := by
  by_cases hm : m = 0
  · omega
  · have hm_pos : m > 0 := by omega
    have ⟨nlo, nhi⟩ := numDigits_bounds n hn
    have ⟨mlo, mhi⟩ := numDigits_bounds m hm_pos
    -- n < 10^(numDigits n) and 10^(numDigits m - 1) ≤ m
    -- n ≤ m < 10^(numDigits m)
    -- So n < 10^(numDigits m)
    -- If numDigits n > numDigits m, then 10^(numDigits n - 1) ≤ n < 10^(numDigits m)
    -- which would require numDigits n - 1 < numDigits m, contradiction
    by_contra h
    push_neg at h
    have hlt : Impl.numDigits m < Impl.numDigits n := h
    have hpow : Impl.pow10 (Impl.numDigits n - 1) ≤ n := nlo
    have hpow2 : m < Impl.pow10 (Impl.numDigits m) := mhi
    have hpow3 : Impl.pow10 (Impl.numDigits m) ≤ Impl.pow10 (Impl.numDigits n - 1) := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 10)
      omega
    simp only [Impl.pow10] at *
    omega

/-- Helper: foldl sum with accumulator.
    Used by: foldl_sum_ranges_eq -/
lemma foldl_sum_add_acc (ranges : List Range) (f : Range → Nat) (acc : Nat) :
    ranges.foldl (fun a r => a + f r) acc = acc + ranges.foldl (fun a r => a + f r) 0 := by
  induction ranges generalizing acc with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih, ih (acc := f r)]
    omega

/-- Helper: foldl over ranges produces same sum when each range sums match.
    Used by: impl_eq_spec -/
lemma foldl_sum_ranges_eq (ranges : List Range) (invalids : List Nat)
    (h : ∀ r ∈ ranges, Spec.sumInvalidInRange r = Impl.sumInvalidInRange invalids r) :
    ranges.foldl (fun acc r => acc + Impl.sumInvalidInRange invalids r) 0 =
    ranges.foldl (fun acc r => acc + Spec.sumInvalidInRange r) 0 := by
  induction ranges with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    have hr : Spec.sumInvalidInRange r = Impl.sumInvalidInRange invalids r :=
      h r (by simp)
    have hrs : ∀ r' ∈ rs, Spec.sumInvalidInRange r' = Impl.sumInvalidInRange invalids r' :=
      fun r' hr' => h r' (by simp [hr'])
    rw [foldl_sum_add_acc rs (Impl.sumInvalidInRange invalids),
        foldl_sum_add_acc rs Spec.sumInvalidInRange]
    rw [hr, ih hrs]

/-- Helper: foldl max is monotonic with accumulator.
    Used by: maxVal_bounds -/
lemma foldl_max_mono (rs : List Range) (a b : Nat) (hab : a ≤ b) :
    rs.foldl (fun acc r => max acc r.hi) a ≤ rs.foldl (fun acc r => max acc r.hi) b := by
  induction rs generalizing a b with
  | nil => exact hab
  | cons r rs ih =>
    simp only [List.foldl_cons]
    apply ih
    exact max_le_max_right r.hi hab

/-- Helper: value is bounded by foldl max.
    Used by: maxVal_bounds -/
lemma le_foldl_max (rs : List Range) (a : Nat) :
    a ≤ rs.foldl (fun acc r => max acc r.hi) a := by
  induction rs generalizing a with
  | nil => exact Nat.le_refl _
  | cons r rs ih =>
    simp only [List.foldl_cons]
    calc a ≤ max a r.hi := Nat.le_max_left _ _
      _ ≤ rs.foldl (fun acc r => max acc r.hi) (max a r.hi) := ih _

/-- Helper: maxVal bounds all hi values in ranges.
    Used by: impl_eq_spec -/
lemma maxVal_bounds (ranges : List Range) (r : Range) (hr : r ∈ ranges) :
    r.hi ≤ ranges.foldl (fun acc r => max acc r.hi) 0 := by
  induction ranges with
  | nil => simp at hr
  | cons r' rs ih =>
    simp only [List.foldl_cons]
    cases hr with
    | head =>
      calc r.hi ≤ max 0 r.hi := Nat.le_max_right _ _
        _ ≤ rs.foldl (fun acc r => max acc r.hi) (max 0 r.hi) := le_foldl_max _ _
    | tail _ hmem =>
      calc r.hi ≤ rs.foldl (fun acc r => max acc r.hi) 0 := ih hmem
        _ ≤ rs.foldl (fun acc r => max acc r.hi) (max 0 r'.hi) :=
          foldl_max_mono rs _ _ (Nat.zero_le _)

/-- MAIN THEOREM: Implementation equals specification for all inputs. -/
theorem impl_eq_spec (ranges : List Range) :
    Impl.solve ranges = Spec.solve ranges := by
  -- Both solve functions fold over ranges, summing invalid numbers
  simp only [Impl.solve, Spec.solve]
  set maxVal := ranges.foldl (fun acc r => max acc r.hi) 0 with hmaxVal
  set maxK := (Impl.numDigits maxVal + 1) / 2 with hmaxK
  set invalids := Impl.allInvalidsUpToKDigitBase maxK with hinvalids
  -- Use foldl_sum_ranges_eq: suffices to show each range's sum matches
  apply foldl_sum_ranges_eq
  intro r hr
  -- For this range r, show Spec.sumInvalidInRange r = Impl.sumInvalidInRange invalids r
  apply sumInvalidInRange_eq
  · -- Completeness: every invalid n in [r.lo, r.hi] is in invalids
    intro n hlo hhi hn_invalid
    apply allInvalids_complete maxK n hn_invalid
    -- Need: numDigits n ≤ 2 * maxK
    -- n ≤ r.hi ≤ maxVal, so numDigits n ≤ numDigits maxVal
    -- numDigits maxVal ≤ 2 * maxK by definition of maxK
    by_cases hn_zero : n = 0
    · -- n = 0 is not invalid ("0" has odd length 1)
      subst hn_zero
      -- toString 0 = "0" has length 1, which is odd, so isInvalid 0 = false
      have : Spec.isInvalid 0 = false := by native_decide
      simp only [this] at hn_invalid
      exact absurd hn_invalid (by decide)
    · have hn_pos : n > 0 := Nat.pos_of_ne_zero hn_zero
      have hhi_bound : r.hi ≤ maxVal := maxVal_bounds ranges r hr
      have hn_bound : n ≤ maxVal := Nat.le_trans hhi hhi_bound
      by_cases hmaxVal_zero : maxVal = 0
      · omega
      · have hmaxVal_pos : maxVal > 0 := Nat.pos_of_ne_zero hmaxVal_zero
        have hnd_mono : Impl.numDigits n ≤ Impl.numDigits maxVal := numDigits_mono n maxVal hn_pos hn_bound
        have hmaxK_bound : Impl.numDigits maxVal ≤ 2 * maxK := by
          simp only [hmaxK]
          have hpos : Impl.numDigits maxVal > 0 := numDigits_pos maxVal
          omega
        omega
  · -- Soundness: every n in invalids is invalid
    intro n hmem
    exact allInvalids_sound maxK n hmem
  · -- No duplicates
    exact allInvalids_nodup maxK

end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
-------------------------------------------------------------------------------

def parseRange (s : String) : Option Range := do
  let parts := s.splitOn "-"
  if parts.length != 2 then none
  else
    let lo ← parts[0]!.toNat?
    let hi ← parts[1]!.toNat?
    some { lo, hi }

def parse (input : String) : List Range :=
  let input := input.trim
  (input.splitOn ",").filterMap parseRange

def solve (input : String) : Nat :=
  Impl.solve (parse input)

-- Note: We can still state correctness even with sorry in the proof
theorem solve_correct (input : String) :
    solve input = Spec.solve (parse input) :=
  Proof.impl_eq_spec (parse input)

def main : IO Unit := do
  let input ← IO.FS.readFile "inputs/day02.txt"
  IO.println s!"Answer: {solve input}"

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
-------------------------------------------------------------------------------

-- Test isInvalid on examples from problem
#guard Spec.isInvalid 55 = true
#guard Spec.isInvalid 6464 = true
#guard Spec.isInvalid 123123 = true
#guard Spec.isInvalid 99 = true
#guard Spec.isInvalid 1010 = true
#guard Spec.isInvalid 222222 = true
#guard Spec.isInvalid 446446 = true
#guard Spec.isInvalid 1188511885 = true
#guard Spec.isInvalid 38593859 = true

-- Test non-invalid numbers
#guard Spec.isInvalid 101 = false  -- 3 digits (odd)
#guard Spec.isInvalid 12 = false   -- 1 ≠ 2
#guard Spec.isInvalid 100 = false  -- 3 digits (odd)
#guard Spec.isInvalid 1234 = false -- 12 ≠ 34

-- Test implementation's toInvalid
#guard Impl.toInvalid 1 = 11
#guard Impl.toInvalid 5 = 55
#guard Impl.toInvalid 64 = 6464
#guard Impl.toInvalid 123 = 123123

-- Verify toInvalid produces numbers that pass the spec's string test (soundness)
#guard Spec.isInvalid (Impl.toInvalid 1) = true
#guard Spec.isInvalid (Impl.toInvalid 9) = true
#guard Spec.isInvalid (Impl.toInvalid 10) = true
#guard Spec.isInvalid (Impl.toInvalid 99) = true
#guard Spec.isInvalid (Impl.toInvalid 100) = true
#guard Spec.isInvalid (Impl.toInvalid 999) = true
#guard Spec.isInvalid (Impl.toInvalid 12345) = true

-- Test numDigits
#guard Impl.numDigits 1 = 1
#guard Impl.numDigits 9 = 1
#guard Impl.numDigits 10 = 2
#guard Impl.numDigits 99 = 2
#guard Impl.numDigits 100 = 3
#guard Impl.numDigits 999 = 3

-- Example from problem
def testInput := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

-- Verify expected invalid IDs in each range from example
#guard Spec.sumInvalidInRange ⟨11, 22⟩ = 11 + 22
#guard Spec.sumInvalidInRange ⟨95, 115⟩ = 99
#guard Spec.sumInvalidInRange ⟨998, 1012⟩ = 1010
#guard Spec.sumInvalidInRange ⟨1188511880, 1188511890⟩ = 1188511885
#guard Spec.sumInvalidInRange ⟨222220, 222224⟩ = 222222
#guard Spec.sumInvalidInRange ⟨1698522, 1698528⟩ = 0
#guard Spec.sumInvalidInRange ⟨446443, 446449⟩ = 446446
#guard Spec.sumInvalidInRange ⟨38593856, 38593862⟩ = 38593859

#guard solve testInput = 1227775554
-- Empirically verify impl = spec on test input
#guard Impl.solve (parse testInput) = Spec.solve (parse testInput)

-- Test on actual input
def actualInput : String := include_str "../inputs/day02.txt"
#guard solve actualInput = 23039913998

end Day02Part1
