import Benchmark.Cases.Etherparse.Transport.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse
open Benchmark.Cases.Etherparse.Transport

namespace Benchmark.Cases.Etherparse.Transport.Oracle

/-- PBT `transport::igmp::membership_query_with_sources_header::test::flags_set`
(etherparse/src/transport/igmp/membership_query_with_sources_header.rs:135-155):
```
let mut header = MembershipQueryWithSourcesHeader {
  max_response_code: MaxResponseCode(0),
  group_address: GroupAddress::new([0, 0, 0, 0]),
  raw_byte_8, qqic: 0, num_of_sources: 0 };
header.set_flags(value);
prop_assert_eq!(header.flags(), value & 0b0000_1111);
prop_assert_eq!(
  header.raw_byte_8 & !RAW_BYTE_8_MASK_FLAGS,
  raw_byte_8 & !RAW_BYTE_8_MASK_FLAGS);
```
`set_flags(&mut self)` returns the updated header. `!` is bitwise complement
and `&` is bitwise and, both on `u8`. -/
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

axiom igmp_flags_set (raw_byte_8 value : Std.U8) :
    igmp_flags_set_spec raw_byte_8 value

end Benchmark.Cases.Etherparse.Transport.Oracle
