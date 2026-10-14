import Benchmark.Cases.Etherparse.Transport.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Transport

/-- `set_flags` stores the low 4 bits of `value` in the high nibble of
`raw_byte_8` and leaves the low nibble unchanged. -/
def igmp_flags_set_spec (raw_byte_8 value : Std.U8) : Prop :=
  (do
    let header : transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader := {
      max_response_code := 0#u8,
      group_address := { octets := Array.repeat 4#usize 0#u8 },
      raw_byte_8 := raw_byte_8,
      qqic := 0#u8,
      num_of_sources := 0#u16 }
    let header1 ←
      transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_flags
        header value
    let f ←
      transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.flags
        header1
    let mask :=
      transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_FLAGS
    let kept ← lift (~~~mask)
    let low1 ← lift (header1.raw_byte_8 &&& kept)
    let low0 ← lift (raw_byte_8 &&& kept)
    let expect ← lift (value &&& 15#u8)
    ok (f, low1, low0, expect))
    ⦃ t => t.1 = t.2.2.2 ∧ t.2.1 = t.2.2.1 ⦄

end Benchmark.Cases.Etherparse.Transport
