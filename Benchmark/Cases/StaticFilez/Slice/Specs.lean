import Benchmark.Cases.StaticFilez.Slice.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open static_filez
open Benchmark.Cases.StaticFilez.Slice

namespace Benchmark.Cases.StaticFilez.Slice.Oracle

/-- PBT `slice::tests::slice_encoding_roundtrip` (src/slice.rs:15-18):
`prop_assert_eq!((i as usize, l as usize),
unpack_from_u64(pack_in_u64(i as usize, l as usize)))`.
The test's own `i as usize` / `l as usize` casts are modelled with
`UScalar.cast .Usize`, the operation the extraction uses for Rust `as usize`. -/
def slice_encoding_roundtrip_spec (i l : Std.U32) : Prop :=
  (do
    let packed ← slice.pack_in_u64 (UScalar.cast .Usize i) (UScalar.cast .Usize l)
    slice.unpack_from_u64 packed)
    ⦃ r => r = (UScalar.cast .Usize i, UScalar.cast .Usize l) ⦄

axiom slice_encoding_roundtrip (i l : Std.U32) :
    slice_encoding_roundtrip_spec i l

end Benchmark.Cases.StaticFilez.Slice.Oracle
