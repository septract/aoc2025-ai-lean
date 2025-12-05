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
-- IMPORTANT: Every solution MUST end with a #guard verifying the final answer:
def actualInput : String := include_str "../inputs/day01.txt"
#guard solve actualInput = 1076  -- The correct answer for this puzzle
```

## Specification Guidelines

The spec should be **obviously correct by inspection**, even if inefficient or "uncomputable" for large inputs. The spec exists to define *what* the answer is, not *how* to compute it efficiently.

**Key principle: The spec must be structurally different from the implementation.**

If your spec looks like your implementation, you haven't gained anything—you're just proving the code equals itself. A good spec is:
- **Naive**: Enumerate all possibilities, count them directly
- **Declarative**: Describe what the answer *is*, not how to compute it
- **Inefficient**: O(n²) or worse is fine—clarity over performance

```lean
namespace Spec

-- Use types that encode constraints
abbrev Dial := Fin 100  -- Not Nat!

-- GOOD: Enumerate every position visited (obviously correct, but O(n))
def positionsDuringRotation (d : Dial) (rot : Rotation) : List Dial :=
  -- Generate every single position the dial passes through
  (List.range rot.dist).map (fun i => ...)

-- GOOD: Count by filtering a list (obviously correct)
def countZeros (rotations : List Rotation) : Nat :=
  (allPositionsVisited rotations).countP (· == zero)

end Spec

namespace Impl

-- GOOD: Use efficient formula (needs proof it equals spec)
def countZerosInRotation (pos : Nat) (dist : Nat) : Nat :=
  (pos + dist) / 100  -- O(1) but not obviously correct

end Impl
```

**Good spec properties:**
- A reader can verify it matches the problem statement
- Uses types that make invalid states unrepresentable
- Prefers recursion/list operations over folds (clearer)
- Doesn't optimize—that's what the implementation is for
- **Is structurally different from the implementation**

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

### Theorem vs Lemma Naming

Use `theorem` only for **top-level properties the user cares about**:
- `impl_eq_spec` - the main correctness theorem
- `solve_correct` - correctness of the solve function

Use `lemma` for **helper facts** used to build up to theorems:
- Arithmetic identities
- Intermediate equivalences
- Technical lemmas about data structures

```lean
-- GOOD: Clear distinction
lemma applyRotation_eq_rotate (d : Dial) (rot : Rotation) : ...  -- Helper
lemma fold_equiv (d : Dial) (rotations : List Rotation) : ...    -- Helper
theorem impl_eq_spec (rotations : List Rotation) : ...           -- Main result

-- BAD: Everything called theorem
theorem applyRotation_eq_rotate ...  -- This is just a helper!
```

### Top-Down Proof Development (IMPORTANT)

**Always develop proofs top-down: start from the main theorem, then create helper lemmas as needed.**

This prevents orphan lemmas (unused lemmas) and speculative work:

1. **Start with the main theorem** (`impl_eq_spec`)
2. **Write the callsite first** - when you need a helper lemma, write its usage in the parent proof before creating it
3. **Then create the helper lemma** to satisfy that callsite
4. **Never create speculative lemmas** - every lemma must have a callsite before it's written

```lean
-- WORKFLOW EXAMPLE:

-- Step 1: Start with main theorem, sketch the proof structure
theorem impl_eq_spec (input : Input) : Impl.solve input = Spec.solve input := by
  -- Will need: foo_preserves_bar to show the foo step is correct
  -- Will need: something about list length preservation
  sorry

-- Step 2: Create helpers that were noted above
-- Each helper documents WHO USES IT (the reverse dependency)
/-- Used by: impl_eq_spec -/
lemma foo_preserves_bar (x : X) : foo x = bar x := by
  -- Will need: baz_property for the base case
  sorry

-- Step 3: Continue down the chain
/-- Used by: foo_preserves_bar -/
lemma baz_property (n : Nat) : baz n > 0 := by
  ...
```

**Rules:**
- ✅ Every lemma must be noted in a higher-level proof before being created (comment or actual callsite)
- ✅ A comment like `-- Will need: helper_lemma for X` counts as a callsite
- ✅ Every helper lemma must document its caller with `Used by:` in its docstring
- ❌ Never create a lemma "because we might need it"
- ❌ Never create a lemma without first noting where it will be used

### Lemma Stubbing

**NEVER leave interior `sorry` statements inside proof tactics.** If you get stuck on a proof:

1. **Write the callsite** in the parent proof first
2. **Extract the needed fact as a separate lemma** with `sorry`
3. The parent proof should be complete modulo the stubbed lemmas

```lean
-- BAD: Interior sorry (and no clear callsite structure)
theorem main_theorem : P := by
  have h1 : A := by sorry  -- Interior sorry!
  have h2 : B := by
    ...
    sorry  -- Another interior sorry!
  exact ...

-- GOOD: Top-down with stubbed helpers
-- Main theorem written first, with clear callsites
theorem main_theorem : P := by
  have h1 : A := helper_A  -- Callsite for helper_A
  have h2 : B := helper_B x  -- Callsite for helper_B
  exact ...  -- Main proof is complete!

-- Helpers created AFTER their callsites exist, documenting their caller
/-- Used by: main_theorem -/
lemma helper_A : A := by sorry

/-- Used by: main_theorem -/
lemma helper_B (x : X) : B x := by sorry
```

**Benefits:**
- Every lemma has a purpose (no orphans)
- Clear visibility of what's incomplete (all sorrys at theorem level)
- Main proof structure is preserved and verified
- Bidirectional traceability: callers note what they need, helpers note who uses them
- No speculative work on lemmas that might not be needed

## What's NOT Acceptable

| Bad | Why | Good |
|-----|-----|------|
| `sorry` | Incomplete proof | Complete the proof |
| `native_decide` on universally quantified theorem | Only works for specific values | Structural proof |
| `#guard` as proof | Only tests specific inputs | `theorem` with proof |
| Spec and Impl mixed together | Hard to verify spec is correct | Clear separation |
| Spec using implementation details | Defeats the purpose | Spec should be independent |
| Linter warnings (non-sorry) | Code quality issues | Fix immediately |

### Linter Errors

**Fix all non-sorry linter errors immediately.** This includes:
- Unused simp arguments
- Unused variables
- Style warnings

Don't let linter warnings accumulate. Fix them as soon as they appear before moving on to other tasks.

## File Naming Convention

Each day has two parts, so files are named:
- `Aoc01-1.lean` - Day 1, Part 1
- `Aoc01-2.lean` - Day 1, Part 2
- `Aoc02-1.lean` - Day 2, Part 1
- etc.

### Companion Documentation Files

For solutions with incomplete proofs or complex proof strategies, create a companion markdown file with the same base name:
- `Aoc02-1.lean` → `Aoc02-1.md`

The companion file should document:
- **Proof status**: Which proofs are complete vs stubbed
- **Core gaps**: The key lemmas that need work
- **Proof strategy**: Recommended approach for completing proofs
- **Dependencies**: Which lemmas depend on which

This keeps CLAUDE.md focused on general conventions while solution-specific notes stay with their solutions.

## File Structure and Namespaces

**Each solution file must be self-contained and wrapped in a unique namespace.**

Do NOT share types or definitions between files. Each file defines its own `Direction`, `Rotation`, etc. This avoids import conflicts when building all solutions together.

```lean
/-
  Advent of Code 2025, Day N Part M
  Formally verified solution in Lean 4
-/

namespace Day01Part1  -- Unique namespace per file

-- All sections go here...

end Day01Part1
```

**Why namespaces?**
- Files can be imported together without conflicts
- No dependencies between solution files
- Each solution is completely self-contained

**Adding solutions to the build:**
After creating a new solution file, add it to `Aoc2025.lean`:
```lean
import «Aoc2025».«Aoc01-1»
import «Aoc2025».«Aoc01-2»
-- Add new files here
```

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
