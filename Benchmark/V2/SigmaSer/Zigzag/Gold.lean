import Benchmark.V2.Prelude
import SigmaSerZigzag.Extraction

/-! Hidden gold specification for target `sigma_ser/zigzag`.

Reference model (independent of the bit tricks in the implementation):
ZigZag maps `0, -1, 1, -2, 2, …` to `0, 1, 2, 3, 4, …`, i.e. `v ↦ 2v` for
`v ≥ 0` and `v ↦ -2v - 1` for `v < 0`.

`encode_i32` returns the 32-bit ZigZag code *as an `i32` sign-extended to
`u64`* (documented: "we need to use u64 due to the signed Int used for result
in Scala version"; the crate's own test vectors check `encode_i32(0x7FFF_FFFF)
as i32 == 0xFFFF_FFFE`). So codes `≥ 2^31` come out as `code + 2^64 - 2^32`.
`decode_u32` only looks at the low 32 bits of its argument.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM sigma_ser RSGB

namespace Benchmark.V2.SigmaSer.Zigzag.Gold

/-- ZigZag code of an integer. -/
def zz (v : Int) : Nat := if 0 ≤ v then 2 * v.toNat else 2 * (-v).toNat - 1

/-- Inverse of `zz`. -/
def unzz (n : Nat) : Int := if n % 2 = 0 then ((n / 2 : Nat) : Int) else -(((n + 1) / 2 : Nat) : Int)

/-- A 32-bit pattern read as `i32` and sign-extended to 64 bits (as an unsigned value). -/
def sext32 (z : Nat) : Nat := if z < 2^31 then z else z + (2^64 - 2^32)

/-! ## 64-bit -/

/-- `encode_i64` is total and equals the ZigZag code. -/
def gold_encode_i64_exact (v : Std.I64) : Prop :=
  zig_zag_encode.encode_i64 v ⦃ r => r.val = zz v.val ⦄

/-- `decode_u64` is total and inverts the ZigZag code on all of `u64`. -/
def gold_decode_u64_exact (n : Std.U64) : Prop :=
  zig_zag_encode.decode_u64 n ⦃ r => r.val = unzz n.val ⦄

/-- `decode_u64 ∘ encode_i64 = id` (upstream property). -/
def gold_i64_roundtrip (v : Std.I64) : Prop :=
  (do let e ← zig_zag_encode.encode_i64 v; zig_zag_encode.decode_u64 e) ⦃ r => r = v ⦄

/-- `encode_i64 ∘ decode_u64 = id`: the encoding is a bijection `i64 ≃ u64`. -/
def gold_u64_roundtrip (n : Std.U64) : Prop :=
  (do let d ← zig_zag_encode.decode_u64 n; zig_zag_encode.encode_i64 d) ⦃ r => r = n ⦄

/-- Small magnitudes give small codes (the point of ZigZag for varints). -/
def gold_encode_i64_small (v : Std.I64) : Prop :=
  zig_zag_encode.encode_i64 v ⦃ r => r.val ≤ 2 * v.val.natAbs ∧ 2 * v.val.natAbs ≤ r.val + 1 ⦄

/-! ## 32-bit -/

/-- `encode_i32` is total; it returns the 32-bit ZigZag code read as `i32` and
sign-extended to `u64`. -/
def gold_encode_i32_exact (v : Std.I32) : Prop :=
  zig_zag_encode.encode_i32 v ⦃ r => r.val = sext32 (zz v.val) ⦄

/-- The low 32 bits of `encode_i32` are always the 32-bit ZigZag code, and for
`|v| < 2^30` the result is exactly that code (the same as `encode_i64`). -/
def gold_encode_i32_vs_i64 (v : Std.I32) : Prop :=
  (do
    let a ← zig_zag_encode.encode_i32 v
    let b ← zig_zag_encode.encode_i64 (mkI .I64 v.val)
    ok (a, b)) ⦃ (a, b) => a.val % 2^32 = b.val ∧ (b.val < 2^31 → a = b) ⦄

/-- `decode_u32` is total and decodes the ZigZag code held in the low 32 bits. -/
def gold_decode_u32_exact (n : Std.U64) : Prop :=
  zig_zag_encode.decode_u32 n ⦃ r => r.val = unzz (n.val % 2^32) ⦄

/-- `decode_u32` ignores the upper 32 bits. -/
def gold_decode_u32_low_bits (n : Std.U64) : Prop :=
  zig_zag_encode.decode_u32 n = zig_zag_encode.decode_u32 (mkU .U64 (n.val % 2^32))

/-- `decode_u32 ∘ encode_i32 = id` (upstream property). -/
def gold_i32_roundtrip (v : Std.I32) : Prop :=
  (do let e ← zig_zag_encode.encode_i32 v; zig_zag_encode.decode_u32 e) ⦃ r => r = v ⦄

/-- `encode_i32 ∘ decode_u32` recovers the low 32 bits (sign-extended). -/
def gold_u32_roundtrip (n : Std.U64) : Prop :=
  (do let d ← zig_zag_encode.decode_u32 n; zig_zag_encode.encode_i32 d)
    ⦃ r => r.val = sext32 (n.val % 2^32) ⦄

/-- `decode_u32` also accepts the (unextended) 64-bit encoding of an `i32` value. -/
def gold_decode_u32_of_encode_i64 (v : Std.I32) : Prop :=
  (do let e ← zig_zag_encode.encode_i64 (mkI .I64 v.val); zig_zag_encode.decode_u32 e) ⦃ r => r = v ⦄

/-! Differential-testing probes. -/

def diff_encode_i32 (v : Std.I32) := zig_zag_encode.encode_i32 v
def diff_decode_u32 (n : Std.U64) := zig_zag_encode.decode_u32 n
def diff_encode_i64 (v : Std.I64) := zig_zag_encode.encode_i64 v
def diff_decode_u64 (n : Std.U64) := zig_zag_encode.decode_u64 n

end Benchmark.V2.SigmaSer.Zigzag.Gold
