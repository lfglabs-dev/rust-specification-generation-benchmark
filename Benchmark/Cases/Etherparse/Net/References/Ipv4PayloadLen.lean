import Benchmark.Cases.Etherparse.Net.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

/-- `Ipv4Header::payload_len` equals `total_len - 20 - options.len() as u16` when
the total length covers the header, and returns `LenError` for every smaller
`total_len`. -/
def ipv4_payload_len_spec (header : net.ipv4_header.Ipv4Header) : Prop :=
  (do
    let r ← net.ipv4_header.Ipv4Header.payload_len header
    let olen ← net.ipv4_options.Ipv4Options.impl.len header.options
    let olen16 ← lift (UScalar.cast .U16 olen)
    let a ← header.total_len - 20#u16
    let b ← a - olen16
    ok (r, b))
    ⦃ t => ∃ v, t.1 = core.result.Result.Ok v ∧ v = t.2 ⦄ ∧
  (do
    let hl ← net.ipv4_header.Ipv4Header.header_len header
    let hl16 ← lift (UScalar.cast .U16 hl)
    ok hl16)
    ⦃ hl16 => ∀ bad : Std.U16, bad.val < hl16.val →
      (do
        let h := { header with total_len := bad }
        let err ← net.ipv4_header.Ipv4Header.payload_len h
        let req ← net.ipv4_header.Ipv4Header.header_len h
        let lenU ←
          core.convert.Into.Blanket.into core.Usize.Insts.CoreConvertFromU16 bad
        ok (err, req, lenU))
        ⦃ t => t.1 = core.result.Result.Err {
          required_len := t.2.1,
          len := t.2.2,
          len_source := len_source.LenSource.Ipv4HeaderTotalLen,
          layer := err.layer.Layer.Ipv4Packet,
          layer_start_offset := 0#usize } ⦄ ⦄

end Benchmark.Cases.Etherparse.Net
