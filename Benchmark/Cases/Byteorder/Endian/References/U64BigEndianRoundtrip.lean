import Benchmark.Cases.Byteorder.Endian.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder

namespace Benchmark.Cases.Byteorder.Endian

/-- Writing any `u64` with `BigEndian::write_u64` into a zeroed 16-byte buffer (right-aligned: `buf[16 - size_of::<u64>()..]`) and reading it back with `BigEndian::read_u64` never panics and returns the same value. -/
def u64_big_endian_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let start ← 16#usize - 8#usize  -- `16 - size_of::<u64>()`, size 8
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { start }
    let s1 ← BigEndian.Insts.ByteorderByteOrder.write_u64 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { start }
    BigEndian.Insts.ByteorderByteOrder.read_u64 s2) ⦃ r => n = r ⦄

end Benchmark.Cases.Byteorder.Endian
