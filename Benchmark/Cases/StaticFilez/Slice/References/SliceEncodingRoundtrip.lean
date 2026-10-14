import Benchmark.Cases.StaticFilez.Slice.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open static_filez

namespace Benchmark.Cases.StaticFilez.Slice

/-- Packing an (offset, length) pair of `u32`-range `usize`s into one `u64` with
`pack_in_u64` and unpacking it again with `unpack_from_u64` never panics and
returns exactly the original pair. -/
def slice_encoding_roundtrip_spec (i l : Std.U32) : Prop :=
  (do
    let packed ← slice.pack_in_u64 (UScalar.cast .Usize i) (UScalar.cast .Usize l)
    slice.unpack_from_u64 packed)
    ⦃ r => r = (UScalar.cast .Usize i, UScalar.cast .Usize l) ⦄

end Benchmark.Cases.StaticFilez.Slice
