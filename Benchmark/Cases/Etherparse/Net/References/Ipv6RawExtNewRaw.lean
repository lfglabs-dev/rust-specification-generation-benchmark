import Benchmark.Cases.Etherparse.Net.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

/-- `Ipv6RawExtHeader::new_raw` round-trips `payload()`, rejects prefixes shorter
than 6 bytes, rejects a 2047-byte payload, and rejects the unaligned lengths
the test builds by extending the serialized header. -/
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

end Benchmark.Cases.Etherparse.Net
