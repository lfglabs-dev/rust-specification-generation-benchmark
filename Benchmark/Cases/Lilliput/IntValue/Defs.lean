import LilliputIntValue.Extraction

/-!
# lilliput-core integer values and zig-zag coding — specifications

Implementation: `extracted/LilliputIntValue` (verbatim `cargo hax extract
lilliput-int-value` output for lilliput/lilliput@dd247bd3, crate `lilliput-core`,
roots `lilliput_core::value::int` and `lilliput_core::num::zigzag`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic, shifts
and casts follow Rust debug-build semantics (the configuration `cargo test` runs
the property tests under).

The `eq`/`ord` property tests build, for a generated `u8`/`i8` value `x`, the array
of the four width variants of `x` (`U8(x), U16(x as u16), U32(x as u32), U64(x as u64)`,
resp. `I8(x), I16(x as i16), ...`) and check every pair of variants. The arrays are
reproduced by `unsignedValues` / `signedValues` below, with Rust's `as` widening
casts modelled by Aeneas' `UScalar.cast` (zero extension) / `IScalar.cast` (sign
extension), which is how the extraction translates `as`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Lilliput.IntValue

open lilliput_core

/-- `[UnsignedIntValue::U8(x), UnsignedIntValue::U16(x as u16),
UnsignedIntValue::U32(x as u32), UnsignedIntValue::U64(x as u64)]` -/
def unsignedValues (x : Std.U8) : List value.int.unsigned.UnsignedIntValue :=
  [.U8 x, .U16 (UScalar.cast .U16 x), .U32 (UScalar.cast .U32 x), .U64 (UScalar.cast .U64 x)]

/-- `[SignedIntValue::I8(x), SignedIntValue::I16(x as i16),
SignedIntValue::I32(x as i32), SignedIntValue::I64(x as i64)]` -/
def signedValues (x : Std.I8) : List value.int.signed.SignedIntValue :=
  [.I8 x, .I16 (IScalar.cast .I16 x), .I32 (IScalar.cast .I32 x), .I64 (IScalar.cast .I64 x)]

end Benchmark.Cases.Lilliput.IntValue
