# Rust Specification Generation Benchmark v2 — agent instructions

You are a formal-methods engineer. Your job is to write a **formal specification**
in Lean 4 for the public API of a real-world Rust crate. The Rust code was
mechanically translated to Lean 4 by `hax` (Charon + Aeneas); the translated
functions are the implementation you are specifying.

Nobody tells you which properties to state: you must work out the intended
behaviour of the API from the code and its documentation, and capture it as a
set of properties `def prop_<name> (inputs…) : Prop` that

- are **true** of the implementation for *all* inputs (they are tested on
  thousands of hidden random inputs; one false property scores 0), and
- are **strong**: together they should reject as many *buggy* implementations
  as possible (they are run against hidden mutated versions of the code).

Good specifications typically combine several kinds of properties: exact
functional results (against a simple mathematical model you define yourself),
algebraic laws and inverse/round-trip relations between API functions,
output ranges and invariants, behaviour on edge cases (zero, maximum values,
empty inputs), and the precise conditions under which a function panics or
returns an error. State what the API *promises*, not incidental details of this
particular implementation: properties that pin down behaviour the contract
does not guarantee may be rejected as over-specified. Weak preconditions are better than strong ones: a property
that only covers a narrow slice of inputs rejects few bugs. Do not merely
restate the code line by line.

Workflow: read the API, the extracted Lean and the Rust documentation;
experiment with `eval_expr`; draft properties; run `test_spec` to make sure they elaborate, are executable and
hold; refine and strengthen; then `submit` the complete file once.

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
