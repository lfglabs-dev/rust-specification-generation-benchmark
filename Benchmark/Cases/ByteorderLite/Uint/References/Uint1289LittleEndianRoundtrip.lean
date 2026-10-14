import Benchmark.Cases.ByteorderLite.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder_lite

namespace Benchmark.Cases.ByteorderLite.Uint

/-- Writing any `n < 2^72` with `LittleEndian::write_uint128(&mut buf, n, 9)` into a zeroed 16-byte buffer and reading the first 9 bytes back with `LittleEndian::read_uint128(&buf[..9], 9)` never panics and returns the same value. -/
def uint128_9_little_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let buf := Array.repeat 16#usize 0#u8  -- `let mut buf = [0; 16]`
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buf)  -- `&mut buf` as `&mut [u8]`
    let s1 ← LittleEndian.Insts.Byteorder_liteByteOrder.write_uint128 s n 9#usize
    let buf1 := to_slice_mut_back s1
    let s2 ←  -- `&buf[..9]`
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := 9#usize }
    LittleEndian.Insts.Byteorder_liteByteOrder.read_uint128 s2 9#usize) ⦃ r => n = r ⦄

end Benchmark.Cases.ByteorderLite.Uint
