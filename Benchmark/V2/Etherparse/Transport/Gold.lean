import Benchmark.V2.Prelude
import Benchmark.V2.Etherparse.Transport.Instances
import EtherparseTransport.Extraction

/-! Hidden gold specification for target `etherparse/transport`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM etherparse RSGB

namespace Benchmark.V2.Etherparse.Transport.Gold

abbrev MQ := transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader
abbrev UH := transport.udp_header.UdpHeader

/-! ## Reference model -/

def mq (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16) : MQ :=
  { max_response_code := mrc, group_address := { octets := ga }, raw_byte_8 := raw, qqic := qqic,
    num_of_sources := n }

def uh (sp dp len cs : Std.U16) : UH :=
  { source_port := sp, destination_port := dp, length := len, checksum := cs }

def withRaw (h : MQ) (r : Nat) : MQ := { h with raw_byte_8 := mkU .U8 r }

/-- Big-endian bytes of a 16-bit value. -/
def be16 (x : Nat) : List Std.U8 := [mkU .U8 (x / 256 % 256), mkU .U8 (x % 256)]

def beAt (l : List Std.U8) (i : Nat) : Std.U16 := mkU .U16 (256 * (l.getD i 0#u8).val + (l.getD (i+1) 0#u8).val)

/-- Lexicographic comparison of natural-number lists. -/
def lexCmp : List Nat → List Nat → core.cmp.Ordering
  | [], [] => .Equal
  | [], _ => .Less
  | _, [] => .Greater
  | a :: xs, b :: ys => if a < b then .Less else if b < a then .Greater else lexCmp xs ys

def fieldsOf (h : UH) : List Nat :=
  [h.source_port.val, h.destination_port.val, h.length.val, h.checksum.val]

/-- Second header: per field, either equal to the first one or the alternative value. -/
def uh2 (sp dp len cs : Std.U16) (d : Std.U8) (sp' dp' len' cs' : Std.U16) : UH :=
  uh (if d.val % 2 = 1 then sp' else sp) (if d.val / 2 % 2 = 1 then dp' else dp)
     (if d.val / 4 % 2 = 1 then len' else len) (if d.val / 8 % 2 = 1 then cs' else cs)

def MAXP : Nat := 65535 - 8

/-! ## IGMP membership query header: `raw_byte_8` accessors -/

def gold_flags (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16) : Prop :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.flags
    (mq mrc ga raw qqic n) = ok (mkU .U8 (raw.val / 16))

/-- `set_flags` stores the low nibble of `value` in the high nibble of `raw_byte_8`
and changes nothing else. -/
def gold_set_flags (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16)
    (v : Std.U8) : Prop :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_flags
    (mq mrc ga raw qqic n) v = ok (withRaw (mq mrc ga raw qqic n) (raw.val % 16 + 16 * (v.val % 16)))

def gold_flags_after_set (raw v : Std.U8) : Prop :=
  (do
    let h ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_flags
      (mq 0#u8 (Array.repeat 4#usize 0#u8) raw 0#u8 0#u16) v
    let f ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.flags h
    let s ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.s_flag h
    let q ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.qrv h
    ok (f, s, q)) ⦃ r => r.1.val = v.val % 16 ∧ r.2.1 = decide (raw.val / 8 % 2 = 1) ∧ r.2.2.val = raw.val % 8 ⦄

def gold_s_flag (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16) : Prop :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.s_flag
    (mq mrc ga raw qqic n) = ok (decide (raw.val / 8 % 2 = 1))

/-- `set_s_flag` sets / clears exactly bit 3 of `raw_byte_8`. -/
def gold_set_s_flag (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16)
    (b : Bool) : Prop :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_s_flag
    (mq mrc ga raw qqic n) b =
    ok (withRaw (mq mrc ga raw qqic n) (raw.val / 16 * 16 + (if b then 8 else 0) + raw.val % 8))

def gold_s_flag_after_set (raw : Std.U8) (b : Bool) : Prop :=
  (do
    let h ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_s_flag
      (mq 0#u8 (Array.repeat 4#usize 0#u8) raw 0#u8 0#u16) b
    let s ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.s_flag h
    let f ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.flags h
    let q ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.qrv h
    ok (s, f, q)) ⦃ r => r.1 = b ∧ r.2.1.val = raw.val / 16 ∧ r.2.2.val = raw.val % 8 ⦄

/-- `qrv` never panics and returns the low three bits. -/
def gold_qrv (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16) : Prop :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.qrv
    (mq mrc ga raw qqic n) = ok (mkU .U8 (raw.val % 8))

/-- `set_qrv` (with a valid QRV, `≤ 7`) replaces exactly the low three bits. -/
def gold_set_qrv (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16)
    (q : Std.U8) : Prop :=
  let q' := q.val % 8
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_qrv
    (mq mrc ga raw qqic n) (mkU .U8 q') = ok (withRaw (mq mrc ga raw qqic n) (raw.val / 8 * 8 + q'))

def gold_qrv_after_set (raw q : Std.U8) : Prop :=
  (do
    let h ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_qrv
      (mq 0#u8 (Array.repeat 4#usize 0#u8) raw 0#u8 0#u16) (mkU .U8 (q.val % 8))
    let q2 ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.qrv h
    let f ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.flags h
    let s ← transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.s_flag h
    ok (q2, f, s)) ⦃ r => r.1.val = q.val % 8 ∧ r.2.1.val = raw.val / 16 ∧ r.2.2 = decide (raw.val / 8 % 2 = 1) ⦄

def gold_igmp_constants (_x : Std.U8) : Prop :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.LEN = 12#usize ∧
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_FLAGS = 0xF0#u8 ∧
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_OFFSET_FLAGS = 4#u8 ∧
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_S_FLAG = 0x08#u8 ∧
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_QRV = 0x07#u8

/-- Derived `PartialEq` of the IGMP header is field-wise equality. -/
def gold_mq_eq (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16)
    (d : Std.U8) (mrc' : Std.U8) (ga' : Std.Array Std.U8 4#usize) (raw' qqic' : Std.U8) (n' : Std.U16) : Prop :=
  let a := mq mrc ga raw qqic n
  let b := mq (if d.val % 2 = 1 then mrc' else mrc) (if d.val / 2 % 2 = 1 then ga' else ga)
              (if d.val / 4 % 2 = 1 then raw' else raw) (if d.val / 8 % 2 = 1 then qqic' else qqic)
              (if d.val / 16 % 2 = 1 then n' else n)
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.Insts.CoreCmpPartialEqMembershipQueryWithSourcesHeader.eq a b
    = ok (decide (a = b))

def gold_mq_clone (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16) : Prop :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.Insts.CoreCloneClone.clone
    (mq mrc ga raw qqic n) = ok (mq mrc ga raw qqic n)

/-! ## UDP header -/

/-- `without_ipv4_checksum`: error iff the total length does not fit into `u16`;
otherwise length = payload + 8 and checksum 0. -/
def gold_udp_new (sp dp : Std.U16) (p : Std.Usize) : Prop :=
  transport.udp_header.UdpHeader.without_ipv4_checksum sp dp p =
    ok (if p.val > MAXP then
          .Err { actual := p, max_allowed := mkU .Usize MAXP,
                 value_type := err.value_type.ValueType.UdpPayloadLengthIpv4 }
        else .Ok (uh sp dp (mkU .U16 (p.val + 8)) 0#u16))

/-- The same around the boundary `65527`. -/
def gold_udp_new_boundary (sp dp : Std.U16) (k : Std.U8) : Prop :=
  gold_udp_new sp dp (mkU .Usize (MAXP - 8 + k.val % 16))

/-- The same for moderately sized payloads. -/
def gold_udp_new_small (sp dp : Std.U16) (k : Std.U32) : Prop :=
  gold_udp_new sp dp (mkU .Usize (k.val % 70000))

def gold_udp_to_bytes (sp dp len cs : Std.U16) : Prop :=
  transport.udp_header.UdpHeader.to_bytes (uh sp dp len cs) ⦃ b =>
    b.val = be16 sp.val ++ be16 dp.val ++ be16 len.val ++ be16 cs.val ⦄

def gold_udp_from_bytes (b : Std.Array Std.U8 8#usize) : Prop :=
  transport.udp_header.UdpHeader.from_bytes b =
    ok (uh (beAt b.val 0) (beAt b.val 2) (beAt b.val 4) (beAt b.val 6))

def gold_udp_roundtrip (sp dp len cs : Std.U16) : Prop :=
  (do
    let b ← transport.udp_header.UdpHeader.to_bytes (uh sp dp len cs)
    transport.udp_header.UdpHeader.from_bytes b) = ok (uh sp dp len cs)

def gold_udp_roundtrip_bytes (b : Std.Array Std.U8 8#usize) : Prop :=
  (do
    let h ← transport.udp_header.UdpHeader.from_bytes b
    transport.udp_header.UdpHeader.to_bytes h) = ok b

def gold_udp_header_len (sp dp len cs : Std.U16) : Prop :=
  transport.udp_header.UdpHeader.header_len (uh sp dp len cs) = ok 8#usize ∧
  transport.udp_header.UdpHeader.header_len_u16 (uh sp dp len cs) = ok 8#u16

def gold_udp_constants (_x : Std.U8) : Prop :=
  transport.udp_header.UdpHeader.LEN = 8#usize ∧ transport.udp_header.UdpHeader.LEN_U16 = 8#u16 ∧
  transport.udp_header.UdpHeader.SERIALIZED_SIZE = 8#usize ∧
  transport.udp_header.UdpHeader.Insts.CoreDefaultDefault.default = ok (uh 0#u16 0#u16 0#u16 0#u16)

def gold_udp_eq (sp dp len cs : Std.U16) (d : Std.U8) (sp' dp' len' cs' : Std.U16) : Prop :=
  transport.udp_header.UdpHeader.Insts.CoreCmpPartialEqUdpHeader.eq (uh sp dp len cs)
      (uh2 sp dp len cs d sp' dp' len' cs') =
    ok (decide (uh sp dp len cs = uh2 sp dp len cs d sp' dp' len' cs'))

/-- Derived `Ord`: lexicographic in field declaration order; `partial_cmp` agrees. -/
def gold_udp_cmp (sp dp len cs : Std.U16) (d : Std.U8) (sp' dp' len' cs' : Std.U16) : Prop :=
  let a := uh sp dp len cs
  let b := uh2 sp dp len cs d sp' dp' len' cs'
  transport.udp_header.UdpHeader.Insts.CoreCmpOrd.cmp a b = ok (lexCmp (fieldsOf a) (fieldsOf b)) ∧
  transport.udp_header.UdpHeader.Insts.CoreCmpPartialOrdUdpHeader.partial_cmp a b =
    ok (some (lexCmp (fieldsOf a) (fieldsOf b)))

def gold_udp_clone (sp dp len cs : Std.U16) : Prop :=
  transport.udp_header.UdpHeader.Insts.CoreCloneClone.clone (uh sp dp len cs) = ok (uh sp dp len cs)

/-! ## Differential-testing probes -/

def diff_flags (raw : Std.U8) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.flags
    (mq 1#u8 (Array.repeat 4#usize 7#u8) raw 3#u8 5#u16)
def diff_set_flags (mrc : Std.U8) (raw qqic v : Std.U8) (n : Std.U16) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_flags
    (mq mrc (Array.repeat 4#usize mrc) raw qqic n) v
def diff_s_flag (raw : Std.U8) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.s_flag
    (mq 1#u8 (Array.repeat 4#usize 7#u8) raw 3#u8 5#u16)
def diff_set_s_flag (mrc raw qqic : Std.U8) (n : Std.U16) (b : Bool) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_s_flag
    (mq mrc (Array.repeat 4#usize mrc) raw qqic n) b
def diff_qrv (raw : Std.U8) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.qrv
    (mq 1#u8 (Array.repeat 4#usize 7#u8) raw 3#u8 5#u16)
def diff_set_qrv (mrc raw qqic : Std.U8) (n : Std.U16) (q : Std.U8) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.set_qrv
    (mq mrc (Array.repeat 4#usize mrc) raw qqic n) (mkU .U8 (q.val % 8))
def diff_mq_eq (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16)
    (d : Std.U8) (mrc' : Std.U8) (ga' : Std.Array Std.U8 4#usize) (raw' qqic' : Std.U8) (n' : Std.U16) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.Insts.CoreCmpPartialEqMembershipQueryWithSourcesHeader.eq
    (mq mrc ga raw qqic n)
    (mq (if d.val % 2 = 1 then mrc' else mrc) (if d.val / 2 % 2 = 1 then ga' else ga)
        (if d.val / 4 % 2 = 1 then raw' else raw) (if d.val / 8 % 2 = 1 then qqic' else qqic)
        (if d.val / 16 % 2 = 1 then n' else n))
def diff_mq_clone (mrc : Std.U8) (ga : Std.Array Std.U8 4#usize) (raw qqic : Std.U8) (n : Std.U16) :=
  transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.Insts.CoreCloneClone.clone
    (mq mrc ga raw qqic n)
def diff_igmp_constants (_x : Std.U8) :=
  (transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.LEN,
   transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_FLAGS,
   transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_OFFSET_FLAGS,
   transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_S_FLAG,
   transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader.RAW_BYTE_8_MASK_QRV)
def diff_udp_new (sp dp : Std.U16) (p : Std.Usize) :=
  transport.udp_header.UdpHeader.without_ipv4_checksum sp dp p
def diff_udp_new_boundary (sp dp : Std.U16) (k : Std.U8) :=
  transport.udp_header.UdpHeader.without_ipv4_checksum sp dp (mkU .Usize (MAXP - 8 + k.val % 16))
def diff_udp_new_small (sp dp : Std.U16) (k : Std.U32) :=
  transport.udp_header.UdpHeader.without_ipv4_checksum sp dp (mkU .Usize (k.val % 70000))
def diff_udp_to_bytes (sp dp len cs : Std.U16) :=
  transport.udp_header.UdpHeader.to_bytes (uh sp dp len cs)
def diff_udp_from_bytes (b : Std.Array Std.U8 8#usize) :=
  transport.udp_header.UdpHeader.from_bytes b
def diff_udp_header_len (sp dp len cs : Std.U16) :=
  (transport.udp_header.UdpHeader.header_len (uh sp dp len cs),
   transport.udp_header.UdpHeader.header_len_u16 (uh sp dp len cs))
def diff_udp_constants (_x : Std.U8) :=
  (transport.udp_header.UdpHeader.LEN, transport.udp_header.UdpHeader.LEN_U16,
   transport.udp_header.UdpHeader.Insts.CoreDefaultDefault.default)
def diff_udp_eq (sp dp len cs : Std.U16) (d : Std.U8) (sp' dp' len' cs' : Std.U16) :=
  transport.udp_header.UdpHeader.Insts.CoreCmpPartialEqUdpHeader.eq (uh sp dp len cs)
    (uh2 sp dp len cs d sp' dp' len' cs')
def diff_udp_cmp (sp dp len cs : Std.U16) (d : Std.U8) (sp' dp' len' cs' : Std.U16) :=
  (transport.udp_header.UdpHeader.Insts.CoreCmpOrd.cmp (uh sp dp len cs) (uh2 sp dp len cs d sp' dp' len' cs'),
   transport.udp_header.UdpHeader.Insts.CoreCmpPartialOrdUdpHeader.partial_cmp (uh sp dp len cs)
     (uh2 sp dp len cs d sp' dp' len' cs'))
def diff_udp_clone (sp dp len cs : Std.U16) :=
  transport.udp_header.UdpHeader.Insts.CoreCloneClone.clone (uh sp dp len cs)

end Benchmark.V2.Etherparse.Transport.Gold
