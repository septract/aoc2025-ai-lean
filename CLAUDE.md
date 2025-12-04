# Advent of Code 2025 - Formally Verified Solutions

This repository contains solutions to Advent of Code 2025 problems in Lean 4, with **formal proofs** that the solutions are correct for ALL valid inputs.

## Core Principle

Each solution must prove: `∀ input, solve input = spec input`

This is stronger than testing—it mathematically guarantees correctness.

## Required File Structure

Each solution file MUST have these clearly separated sections:

```
-------------------------------------------------------------------------------
-- SECTION 1: SHARED TYPES
-------------------------------------------------------------------------------
-- Types used by both spec and implementation (e.g., Direction, Rotation)
-- Keep minimal—only what's needed to state the problem

-------------------------------------------------------------------------------
-- SECTION 2: FORMAL SPECIFICATION
-------------------------------------------------------------------------------
namespace Spec
-- Mathematical definition of the problem
-- Should be OBVIOUSLY CORRECT by inspection
-- Use rich types (Fin n, not Nat) to encode invariants
-- Prefer clarity over efficiency
end Spec

-------------------------------------------------------------------------------
-- SECTION 3: IMPLEMENTATION
-------------------------------------------------------------------------------
namespace Impl
-- Efficient solution
-- May use simpler types (Nat instead of Fin)
-- May use different algorithms (fold vs recursion)
end Impl

-------------------------------------------------------------------------------
-- SECTION 4: CORRECTNESS PROOF
-------------------------------------------------------------------------------
namespace Proof
-- Prove: ∀ input, Impl.solve input = Spec.solve input
-- NO `sorry` ALLOWED
-- Break into lemmas as needed
theorem impl_eq_spec (input : InputType) :
    Impl.solve input = Spec.solve input := by
  ...  -- Complete proof
end Proof

-------------------------------------------------------------------------------
-- SECTION 5: PARSING AND MAIN
-------------------------------------------------------------------------------
-- String parsing, file I/O, main entry point

-------------------------------------------------------------------------------
-- SECTION 6: TESTS
-------------------------------------------------------------------------------
-- #guard statements for sanity checking (not a substitute for proofs!)
```

## Specification Guidelines

The spec should be **obviously correct by inspection**:

```lean
namespace Spec

-- Use types that encode constraints
abbrev Dial := Fin 100  -- Not Nat!

-- Define operations clearly
def rotate (d : Dial) (n : Nat) : Dial := ...

-- The spec should read like the problem statement
def countZeros (rotations : List Rotation) : Nat :=
  (positions rotations).countP (· == zero)

end Spec
```

**Good spec properties:**
- A reader can verify it matches the problem statement
- Uses types that make invalid states unrepresentable
- Prefers recursion/list operations over folds (clearer)
- Doesn't optimize—that's what the implementation is for

## Implementation Guidelines

The implementation can be optimized:

```lean
namespace Impl

-- May use simpler types
def applyRotation (pos : Nat) (rot : Rotation) : Nat := ...

-- May use efficient algorithms
def countZeros (rotations : List Rotation) : Nat :=
  rotations.foldl (fun (pos, count) rot => ...) (50, 0) |>.2

end Impl
```

## Proof Guidelines

The proof connects implementation to specification:

```lean
namespace Proof

-- First prove component equivalence
theorem applyRotation_eq_rotate (d : Spec.Dial) (rot : Rotation) :
    Impl.applyRotation d.val rot = (Spec.rotate d rot).val := by
  ...

-- Then prove overall equivalence
theorem impl_eq_spec (rotations : List Rotation) :
    Impl.countZeros rotations = Spec.countZeros rotations := by
  ...

end Proof
```

**Proof strategies:**
- Prove building blocks first (operation equivalence)
- Use generalized induction for folds (`generalizing` keyword)
- Split on conditions when needed (`cases h : condition`)

## What's NOT Acceptable

| Bad | Why | Good |
|-----|-----|------|
| `sorry` | Incomplete proof | Complete the proof |
| `native_decide` on universally quantified theorem | Only works for specific values | Structural proof |
| `#guard` as proof | Only tests specific inputs | `theorem` with proof |
| Spec and Impl mixed together | Hard to verify spec is correct | Clear separation |
| Spec using implementation details | Defeats the purpose | Spec should be independent |

## File Naming Convention

Each day has two parts, so files are named:
- `Aoc01-1.lean` - Day 1, Part 1
- `Aoc01-2.lean` - Day 1, Part 2
- `Aoc02-1.lean` - Day 2, Part 1
- etc.

## Building and Checking

```bash
# Build all solutions (proofs checked at compile time)
lake build

# Check a specific file
lake env lean Aoc2025/Aoc01-1.lean

# Run a solution
lake env lean -r Aoc2025/Aoc01-1.lean
```

If any proof is incomplete, **compilation fails**.

## Example: Day 1 Part 1

See [Aoc2025/Aoc01-1.lean](Aoc2025/Aoc01-1.lean) for a complete example with:
- `Spec.countZeros`: Obviously correct specification using `Fin 100`
- `Impl.countZeros`: Efficient fold-based implementation using `Nat`
- `Proof.impl_eq_spec`: Complete proof with no `sorry`
