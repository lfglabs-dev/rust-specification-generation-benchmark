import Benchmark.Cases.Etherparse.Net.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse
open Benchmark.Cases.Etherparse.Net

namespace Benchmark.Cases.Etherparse.Net.Oracle

/-- PBT `net::ipv4_header::test::payload_len`
(etherparse/src/net/ipv4_header.rs:978-1003):
```
assert_eq!(header.payload_len().unwrap(),
  header.total_len - 20 - (header.options.len() as u16));
for bad_len in 0u16..(header.header_len() as u16) {
  let mut header = header.clone();
  header.total_len = bad_len;
  assert_eq!(header.payload_len().unwrap_err(),
    LenError { required_len: header.header_len(), len: bad_len.into(),
      len_source: LenSource::Ipv4HeaderTotalLen, layer: Layer::Ipv4Packet,
      layer_start_offset: 0 }); }
```
The reference subtraction is the extracted `u16` subtraction (it panics on
overflow, so a header with `total_len` below the header length falsifies the
spec). `bad_len.into()` is `U16` to `Usize`, which cannot fail; it is the
`UScalar.cast`. `header.clone()` is `header`. Witness: `options.len = 0`,
`total_len = 20`, `dscp = 0`, `fragment_offset = 0`. -/
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

/-- PBT `net::ipv6_header::test::set_dscp`
(etherparse/src/net/ipv6_header.rs:477-487):
```
assert_eq!(header.dscp(), IpDscp::try_new(header.traffic_class >> 2).unwrap());
header.set_dscp(dscp);
assert_eq!(dscp, IpDscp::try_new(header.traffic_class >> 2).unwrap());
assert_eq!(header.dscp(), dscp);
```
`>> 2` is the extracted `u8` shift by `2i32`. `try_new` / `unwrap` require
`Ok`. `set_dscp(&mut self)` returns the updated header. Witness: `dscp = 0`,
`flow_label = 0`. -/
def ipv6_set_dscp_spec (header : net.ipv6_header.Ipv6Header)
    (dscp : net.ip_dscp.IpDscp) : Prop :=
  (do
    let before ← net.ipv6_header.Ipv6Header.dscp header
    let shifted ← header.traffic_class >>> 2#i32
    let decoded ← net.ip_dscp.IpDscp.try_new shifted
    let header1 ← net.ipv6_header.Ipv6Header.set_dscp header dscp
    let shifted1 ← header1.traffic_class >>> 2#i32
    let decoded1 ← net.ip_dscp.IpDscp.try_new shifted1
    let after ← net.ipv6_header.Ipv6Header.dscp header1
    ok (before, decoded, decoded1, after))
    ⦃ t =>
      (∃ v, t.2.1 = core.result.Result.Ok v ∧ t.1 = v) ∧
      (∃ v, t.2.2.1 = core.result.Result.Ok v ∧ v = dscp) ∧
      t.2.2.2 = dscp ⦄

/-- PBT `net::ipv6_raw_ext_header::test::new_raw`
(etherparse/src/net/ipv6_raw_ext_header.rs:298-342):
```
let actual = Ipv6RawExtHeader::new_raw(header.next_header, header.payload()).unwrap();
assert_eq!(actual.next_header, header.next_header);
assert_eq!(actual.payload(), header.payload());
for len in 0..MIN_PAYLOAD_LEN {
  assert_eq!(new_raw(header.next_header, &header.payload()[..len]).unwrap_err(), TooSmall(len)); }
let bytes = [0u8; MAX_PAYLOAD_LEN + 1];
assert_eq!(new_raw(header.next_header, &bytes).unwrap_err(), TooBig(bytes.len()));
// unaligned: to_bytes, pop twice, then for offset in 1..8, if offset + header_len < MAX_LEN,
// push 0 and expect Unaligned(bytes.len())
```
`[0u8; MAX_PAYLOAD_LEN + 1]` is the 2047-byte zero array (`MAX_PAYLOAD_LEN` is
`0xff * 8 + 6`). `&payload[..len]` is `Index` for `RangeTo`. The unaligned
block builds its slice with `to_bytes` (`arrayvec::ArrayVec`, not extracted:
unknown identifier `arrayvec.arrayvec.ArrayVec`). `new_raw`'s `Err` arms return
before reading bytes and depend only on the length; after two `pop`s the
buffer length is `payload().len()` and each `push` adds one, so the call is
`new_raw` on a slice of length `payload().len() + offset` (a prefix of a
2053-byte zero array). `header_len` and `MAX_LEN` are the extracted functions. -/
def ipv6_raw_ext_new_raw_spec (header : net.ipv6_raw_ext_header.Ipv6RawExtHeader) : Prop :=
  (do
    let p ← net.ipv6_raw_ext_header.Ipv6RawExtHeader.payload header
    let actual ←
      net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw header.next_header p
    ok (p, actual))
    ⦃ t => ∃ h, t.2 = core.result.Result.Ok h ∧ h.next_header = header.next_header ∧
      net.ipv6_raw_ext_header.Ipv6RawExtHeader.payload h ⦃ p2 => p2 = t.1 ⦄ ⦄ ∧
  (∀ len : Std.Usize, len.val < 6 →
    (do
      let p ← net.ipv6_raw_ext_header.Ipv6RawExtHeader.payload header
      let pref ←
        core.Slice.Insts.CoreOpsIndexIndex.index
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
          p { «end» := len }
      net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw header.next_header pref)
      ⦃ r => r = core.result.Result.Err
        (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.TooSmall len) ⦄) ∧
  (net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw header.next_header
    (Array.to_slice (Array.repeat 2047#usize 0#u8)))
    ⦃ r => r = core.result.Result.Err
      (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.TooBig 2047#usize) ⦄ ∧
  (∀ offset : Std.Usize, 1 ≤ offset.val ∧ offset.val < 8 →
    (do
      let hlen ← net.ipv6_raw_ext_header.Ipv6RawExtHeader.header_len header
      let sum ← offset + hlen
      let maxl ← net.ipv6_raw_ext_header.Ipv6RawExtHeader.MAX_LEN
      ok (sum.val < maxl.val))
      ⦃ cond => cond →
        (do
          let p ← net.ipv6_raw_ext_header.Ipv6RawExtHeader.payload header
          let plen ← core.slice.Slice.len p
          let n ← plen + offset
          let s ←
            Array.subslice (Array.repeat 2053#usize 0#u8)
              { start := 0#usize, «end» := n }
          let r ←
            net.ipv6_raw_ext_header.Ipv6RawExtHeader.new_raw header.next_header s
          ok (n, r))
          ⦃ t => t.2 = core.result.Result.Err
            (err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError.Unaligned t.1) ⦄ ⦄)

axiom ipv4_payload_len (header : net.ipv4_header.Ipv4Header)
    (h_dscp : header.dscp.val ≤ 63)
    (h_frag : header.fragment_offset.val < 2^13)
    (h_options_len : header.options.len.val ≤ 36 ∧ header.options.len.val % 4 = 0)
    (h_total_lo : 20 + header.options.len.val ≤ header.total_len.val)
    (h_total_hi : header.total_len.val < 2^16 - 1) :
    ipv4_payload_len_spec header

axiom ipv6_raw_ext_new_raw (header : net.ipv6_raw_ext_header.Ipv6RawExtHeader) :
    ipv6_raw_ext_new_raw_spec header

axiom ipv6_set_dscp (header : net.ipv6_header.Ipv6Header) (dscp : net.ip_dscp.IpDscp)
    (h_dscp : dscp.val ≤ 63) (h_flow : header.flow_label.val ≤ 2^20 - 1) :
    ipv6_set_dscp_spec header dscp

end Benchmark.Cases.Etherparse.Net.Oracle
