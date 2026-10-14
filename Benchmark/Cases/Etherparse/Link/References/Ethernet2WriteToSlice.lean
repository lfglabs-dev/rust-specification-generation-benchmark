import Benchmark.Cases.Etherparse.Link.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

/-- Writing an Ethernet II header into a 14-byte buffer succeeds and leaves
`to_bytes()`; a shorter prefix returns `SliceWriteSpaceError` for that length. -/
def ethernet2_write_to_slice_spec (input : link.ethernet2_header.Ethernet2Header) : Prop :=
  (do
    let buf := Array.repeat 14#usize 0#u8
    let (s, backArr) ← lift (Array.to_slice_mut buf)
    let (r, back) ← link.ethernet2_header.Ethernet2Header.write_to_slice input s
    let full := back r
    let arr := backArr full
    let expected ← link.ethernet2_header.Ethernet2Header.to_bytes input
    ok (r, arr, expected))
    ⦃ t => ∃ rest, t.1 = core.result.Result.Ok rest ∧ t.2.1 = t.2.2 ⦄ ∧
  (∀ len : Std.Usize, len.val < 14 →
    (do
      let buf := Array.repeat 14#usize 0#u8
      let (s, _backArr) ←
        core.Array.Insts.CoreOpsIndexIndexMut.index_mut
          (core.Slice.Insts.CoreOpsIndexIndexMut
            (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8))
          buf { «end» := len }
      let (r, _back) ← link.ethernet2_header.Ethernet2Header.write_to_slice input s
      ok r)
      ⦃ r => r = core.result.Result.Err {
        required_len := link.ethernet2_header.Ethernet2Header.LEN,
        len := len,
        layer := err.layer.Layer.Ethernet2Header,
        layer_start_offset := 0#usize } ⦄)

end Benchmark.Cases.Etherparse.Link
