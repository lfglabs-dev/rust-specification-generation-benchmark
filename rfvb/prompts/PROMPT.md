# Rust Specification Generation Benchmark (RSGB) — agent instructions

You are writing a formal **Lean 4 specification** (`def <name>_spec ... : Prop`)
for real-world Rust code. The Rust crate was mechanically translated to Lean 4
by `hax` (Charon + Aeneas); your goal is to formalize the exact property tested
by one of the crate's own `proptest` or `quickcheck` property-based tests.

Each task gives you:
- a fixed implementation (verbatim extracted Lean, under `extracted/`),
- shared helper definitions (`Benchmark/Cases/<Project>/<Case>/Defs.lean`),
- the original Rust crate and property-based test (`rust/<project>/<case>/`),
- one editable specification file (`Benchmark/Generated/<Project>/<Case>/Tasks/<Task>.lean`)
  containing the target `def <name>_spec <binders> : Prop := True`.

## How Your Specification Is Graded
The independent verifier grades your submitted file in 3 stages:
1. **Static Policy:** No `sorry`, `admit`, `axiom`, `native_decide`,
   `implemented_by`, `unsafe`, `#eval`, syntax extensions, or forbidden imports.
   The signature of `def <name>_spec` and its `namespace` must remain unchanged.
2. **Lean 4 Kernel Check:** Your file must elaborate in Lean 4 (`v4.31.0`),
   match the canonical specification type definitionally, and depend only on the
   standard axioms `propext`, `Classical.choice`, `Quot.sound`.
3. **Z3 SMT Equivalence Check:** Under the task's domain preconditions `Pre`
   (shown in `TASK.md`), the verifier lowers your specification and the hidden
   ground-truth specification from the Lean 4 kernel AST to first-order logic
   and verifies four properties with Z3:
   - **Non-Vacuity (`SAT`):** `Pre ∧ CandidateSpec` is satisfiable (not contradictory).
   - **Non-Triviality (`SAT`):** `Pre ∧ ¬CandidateSpec` is satisfiable (not a tautology like `True`).
   - **Soundness (`UNSAT`):** `Pre ∧ CandidateSpec ∧ ¬OracleSpec` is unsatisfiable.
   - **Completeness (`UNSAT`):** `Pre ∧ OracleSpec ∧ ¬CandidateSpec` is unsatisfiable.

Because equivalence is checked semantically by Z3 after unfolding definitions and
normalizing monadic binds, any logically equivalent formulation (for example,
using a `do` block vs nested `⦃ ... ⦄` binds, `<` vs `>`, or reordered
conjuncts) will pass!

## Tools
- `show_task` — display the task briefing (already included in the initial prompt).
- `read_file` / `search` — inspect the original Rust test under `rust/`, the
  extracted Lean code under `extracted/`, `Defs.lean`, or library definitions.
- `run_lean` — test-elaborate a candidate specification in Lean 4 without
  consuming an attempt.
- `check_spec` — submit a candidate specification (consumes one attempt). Pass
  either the specification body replacing `True`, the `def <name>_spec ...`
  declaration, or the complete Lean file. `check_spec` verifies policy, Lean 4
  elaboration, and Z3 non-vacuity/non-triviality before accepting.

## Aeneas & hax Specification Idioms
1. **Monadic Weakest Precondition (`e ⦃ r => P r ⦄`):**
   - Extracted Rust functions return `RustM α` (`ok v`, `fail e`, `div`).
   - `e ⦃ r => P r ⦄` (notation for `Aeneas.Std.WP.spec e (fun r => P r)`) holds
     iff `e` terminates without panicking (`e = ok r`) and postcondition `P r` holds.
   - To chain multiple fallible Rust calls, either nest `⦃ ... ⦄`:
     ```lean
     (f x) ⦃ y => (g y) ⦃ z => z = x ⦄ ⦄
     ```
     or use a `do` block in `RustM`:
     ```lean
     (do
       let y ← f x
       let z ← g y
       ok (y, z)) ⦃ r => r.2 = x ⦄
     ```
   - **Important (Total vs. Partial Correctness):** Do **not** place `f x ⦃ ... ⦄`
     on the left-hand side of an implication (such as `∀ r1, f x ⦃ r => r = r1 ⦄ → ...`),
     because that only asserts partial correctness (*if* `f x` succeeds, then ...)
     and fails to assert that `f x` terminates without panicking. Always keep
     `⦃ ... ⦄` in positive position (or write `∃ r, f x = ok r ∧ ...`).
2. **Expected Panics / Failures:**
   - When a test asserts that a call panics (`#[should_panic]` or debug overflow),
     state `f x = fail .panic` (or `¬ ∃ r, f x = ok r`).
3. **Scalars (`Std.U8 .. Std.U128`, `Std.Usize`, `Std.I8 .. Std.I128`, `Std.Isize`):**
   - `.val` is the mathematical integer (`Nat` for unsigned, `Int` for signed).
   - Scalar literals use `#u8`, `#u16`, `#u32`, `#u64`, `#u128`, `#usize`,
     `#i8`, `#i16`, `#i32`, `#i64`, `#i128`, `#isize` (e.g. `0#u8`, `14#usize`).
   - Checked Rust operations (`+`, `-`, `*`, `<<<`, `>>>`) on scalars return `RustM`;
     pure mathematical arithmetic (`+`, `-`, `*`, `/`, `%`, `^`, `&&&`, `|||`, `^^^`)
     is done on `.val : Nat` / `Int`.
   - Zero/truncating scalar casts in Rust (`x as u128`, `x as u64`) are written
     `UScalar.cast .U128 x` (or `IScalar.cast .I64 x`).
4. **Arrays, Slices, and Vectors:**
   - `Array T N` has `.val : List T` and `.to_slice : Slice T`.
   - `Slice T` and `alloc.vec.Vec T` have `.val : List T`.
   - `alloc.vec.Vec T` coerces directly to `Slice T` (so you can pass `vec`
     directly to a function expecting `Slice T`, or use monadic
     `let s ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref vec`).
5. **CoreModels (`core.*`):**
   - `core.option.Option.Some v` / `core.option.Option.None`
   - `core.result.Result.Ok v` / `core.result.Result.Err e`
   - `core.cmp.Ordering.Less` / `core.cmp.Ordering.Equal` / `core.cmp.Ordering.Greater`
   - Standard Rust scalar methods live under `core.num.U64.*`, `core.num.U32.*`,
     `core.num.Usize.*`, `core.num.I64.*`, etc. (for example
     `core.num.U64.count_ones`, `core.num.Usize.pow`, `core.num.U64.wrapping_add`;
     use `search` with `scope="coremodels"` to find them).
6. **Use Shared Helpers from `Defs.lean`:**
   - Always check the `Shared Helper Definitions (Defs.lean)` section in `TASK.md`.
   - Whenever `Defs.lean` provides domain helpers, constants, or reference
     models (e.g., `uintVal`, `leBytes32`, `P`, `ProbeClosure`, `partitionPointLt`,
     `CollectsTo`, `btreeset_union_vec`, `GetBits`, `countBits`,
     `factorial_reference`, `permutations_reference`), use them directly in your
     specification.
