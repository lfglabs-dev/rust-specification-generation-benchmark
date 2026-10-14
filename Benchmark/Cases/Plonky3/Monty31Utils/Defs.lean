import Plonky3Monty31Utils.Extraction

/-!
# Plonky3 `p3-monty-31` Montgomery helpers — specifications

Implementation: `extracted/Plonky3Monty31Utils` (verbatim `cargo hax extract
plonky3-monty31-utils` output for Plonky3/Plonky3@6468485f, crate `monty-31`,
functions of `monty-31/src/utils.rs`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics, failed
`debug_assert!`s panic), which is the configuration `cargo test` runs the
original property tests under.

## Montgomery parameters

The functions under test are generic over `MP: MontyParameters`; the property
tests (module `utils::tests`, monty-31/src/utils.rs:224-567) instantiate them
with two test-local unit structs:

```rust
struct KB;
impl MontyParameters for KB {
    const PRIME: u32 = 0x7f000001; // 2^31 - 2^24 + 1
    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x81000001;
}
struct BB;
impl MontyParameters for BB {
    const PRIME: u32 = 0x78000001; // 2^31 - 2^27 + 1
    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x88000001;
}
```

Neither impl overrides the provided constant
`MONTY_MASK = ((1u64 << Self::MONTY_BITS) - 1) as u32`. In the extraction a
`MontyParameters` instance is a record of these four constants (as `RustM Std.U32`
values) plus the supertrait instances (`Copy`, `Default`, `Debug`, `Eq`,
`PartialEq`, `Hash`), which none of the functions under test uses. The test
structs themselves live in `#[cfg(test)]` code and are not extracted; the
predicates `KBParams` / `BBParams` below state exactly what their impls define,
and every theorem quantifies over *any* instance satisfying them (in particular
the test's own `KB` / `BB`).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Plonky3.Monty31Utils

open p3_monty_31

/-- `impl MontyParameters for KB` (monty-31/src/utils.rs:230-236): `PRIME = 0x7f000001`,
`MONTY_BITS = 32`, `MONTY_MU = 0x81000001`, and `MONTY_MASK` is the trait's provided
default (monty-31/src/data_traits.rs:23). -/
def KBParams {MP : Type} (inst : data_traits.MontyParameters MP) : Prop :=
  inst.PRIME = ok 2130706433#u32 ∧            -- 0x7f000001
  inst.MONTY_BITS = ok 32#u32 ∧
  inst.MONTY_MU = ok 2164260865#u32 ∧         -- 0x81000001
  inst.MONTY_MASK = data_traits.MontyParameters.MONTY_MASK.default inst

/-- `impl MontyParameters for BB` (monty-31/src/utils.rs:238-244): `PRIME = 0x78000001`,
`MONTY_BITS = 32`, `MONTY_MU = 0x88000001`, and `MONTY_MASK` is the trait's provided
default (monty-31/src/data_traits.rs:23). -/
def BBParams {MP : Type} (inst : data_traits.MontyParameters MP) : Prop :=
  inst.PRIME = ok 2013265921#u32 ∧            -- 0x78000001
  inst.MONTY_BITS = ok 32#u32 ∧
  inst.MONTY_MU = ok 2281701377#u32 ∧         -- 0x88000001
  inst.MONTY_MASK = data_traits.MontyParameters.MONTY_MASK.default inst

/-! ## Conversions into / out of Montgomery form -/

end Benchmark.Cases.Plonky3.Monty31Utils
