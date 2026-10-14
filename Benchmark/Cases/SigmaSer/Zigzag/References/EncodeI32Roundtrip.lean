import Benchmark.Cases.SigmaSer.Zigzag.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sigma_ser

namespace Benchmark.Cases.SigmaSer.Zigzag

/-- ZigZag-encoding an `i32` and decoding the result never panics and returns
the original value. -/
def encode_i32_roundtrip_spec (i : Std.I32) : Prop :=
  (do
    let enc ← zig_zag_encode.encode_i32 i
    zig_zag_encode.decode_u32 enc) ⦃ dec => dec.val = i.val ⦄

end Benchmark.Cases.SigmaSer.Zigzag
