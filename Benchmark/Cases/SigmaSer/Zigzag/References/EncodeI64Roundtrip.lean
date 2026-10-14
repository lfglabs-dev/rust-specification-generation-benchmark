import Benchmark.Cases.SigmaSer.Zigzag.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open sigma_ser

namespace Benchmark.Cases.SigmaSer.Zigzag

/-- ZigZag-encoding an `i64` and decoding the result never panics and returns
the original value. -/
def encode_i64_roundtrip_spec (i : Std.I64) : Prop :=
  (do
    let enc ← zig_zag_encode.encode_i64 i
    zig_zag_encode.decode_u64 enc) ⦃ dec => dec.val = i.val ⦄

end Benchmark.Cases.SigmaSer.Zigzag
