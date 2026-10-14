import Benchmark.Cases.Byteorder.Endian.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder

namespace Benchmark.Cases.Byteorder.Endian

/-- Writing any `u128` with `LittleEndian::write_u128` into a zeroed 16-byte buffer (left-aligned: `buf[..size_of::<u128>()]`) and reading it back with `LittleEndian::read_u128` never panics and returns the same value. -/
def u128_little_endian_roundtrip_spec (n : Std.U128) : Prop :=
  (do
    let bytes := 16#usize  -- `size_of::<Wi128<u128>>()`
    let buf := Array.repeat 16#usize 0#u8  -- `[0; 16]`
    let (s, index_mut_back) ←
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf { «end» := bytes }
    let s1 ← LittleEndian.Insts.ByteorderByteOrder.write_u128 s n
    let buf1 := index_mut_back s1
    let s2 ←
      core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
        buf1 { «end» := bytes }
    LittleEndian.Insts.ByteorderByteOrder.read_u128 s2) ⦃ r => n = r ⦄

end Benchmark.Cases.Byteorder.Endian
