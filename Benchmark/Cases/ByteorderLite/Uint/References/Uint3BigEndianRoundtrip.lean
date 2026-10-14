import Benchmark.Cases.ByteorderLite.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder_lite

namespace Benchmark.Cases.ByteorderLite.Uint

/-- Writing any `n < 2^24` with `BigEndian::write_uint(&mut buf, n, 3)` into a zeroed 16-byte buffer and reading the first 3 bytes back with `BigEndian::read_uint(&buf[..3], 3)` never panics and returns the same value. -/
def uint_3_big_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← BigEndian.Insts.Byteorder_liteByteOrder.write_uint s n 3#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..3]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 3#usize }
    BigEndian.Insts.Byteorder_liteByteOrder.read_uint s2 3#usize) ⦃ r => n = r ⦄

end Benchmark.Cases.ByteorderLite.Uint
