import Benchmark.Cases.SigmaSer.Zigzag.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sigma_ser
open Benchmark.Cases.SigmaSer.Zigzag

namespace Benchmark.Cases.SigmaSer.Zigzag.Oracle

/-- PBT `zig_zag_encode::tests::encode_i64_roundtrip`
(sigma-ser/src/zig_zag_encode.rs:81):
`decode_u64(encode_i64(i)) == i` for `i` over the full `i64` domain
(`i64::ANY` strategy: no bounds). -/
def encode_i64_roundtrip_spec (i : Std.I64) : Prop :=
  (do
    let enc ← zig_zag_encode.encode_i64 i
    zig_zag_encode.decode_u64 enc) ⦃ dec => dec.val = i.val ⦄

/-- PBT `zig_zag_encode::tests::encode_i32_roundtrip`
(sigma-ser/src/zig_zag_encode.rs:75):
`decode_u32(encode_i32(i)) == i` for `i` over the full `i32` domain
(`i32::ANY` strategy: no bounds). -/
def encode_i32_roundtrip_spec (i : Std.I32) : Prop :=
  (do
    let enc ← zig_zag_encode.encode_i32 i
    zig_zag_encode.decode_u32 enc) ⦃ dec => dec.val = i.val ⦄

axiom encode_i32_roundtrip (i : Std.I32) :
    encode_i32_roundtrip_spec i

axiom encode_i64_roundtrip (i : Std.I64) :
    encode_i64_roundtrip_spec i

end Benchmark.Cases.SigmaSer.Zigzag.Oracle
