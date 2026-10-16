import Benchmark.V2.Prelude
import Benchmark.V2.Etherparse.Link.Instances
import EtherparseLink.Extraction

/-! Hidden gold specification for target `etherparse/link`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM etherparse RSGB

/-! Model helpers live outside the `Benchmark` namespace so that the test driver
does not unfold them (it only unfolds `Prop` definitions of `Benchmark.*`). -/
namespace RSGBGold.EtherparseLink

abbrev E2 := link.ethernet2_header.Ethernet2Header
abbrev SLL := link.linux_sll_header.LinuxSllHeader
abbrev PT := link.linux_sll_protocol_type.LinuxSllProtocolType
abbrev HE := err.linux_sll.header_error.HeaderError
abbrev SWE := err.slice_write_space_error.SliceWriteSpaceError

/-! ## Reference model -/

def be16 (x : Nat) : List Std.U8 := [mkU .U8 (x / 256 % 256), mkU .U8 (x % 256)]

def beAt (l : List Std.U8) (i : Nat) : Std.U16 :=
  mkU .U16 (256 * (l.getD i 0#u8).val + (l.getD (i+1) 0#u8).val)

def mkArr (n : Std.Usize) (l : List Std.U8) : Std.Array Std.U8 n :=
  if h : l.length = n.val then ⟨l, h⟩ else ⟨List.replicate n.val 0#u8, by simp⟩

def mkSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

/-- Linux non-standard ether types (`if_ether.h`, ids below 1500). -/
def nonstandard : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 16, 17, 21, 22, 23, 24, 25, 26, 27, 28,
   245, 246, 247, 248, 249, 250]

/-- ARP hardware ids supported by the SLL protocol-type field:
NETLINK, IPGRE, IEEE80211_RADIOTAP, FRAD, ETHERNET. -/
def supportedArp : List Nat := [824, 778, 803, 770, 1]

def protoModel (arp p : Std.U16) : core.result.Result PT HE :=
  if arp.val = 824 then .Ok (.NetlinkProtocolType p)
  else if arp.val = 778 then .Ok (.GenericRoutingEncapsulationProtocolType p)
  else if arp.val = 803 ∨ arp.val = 770 then .Ok (.Ignored p)
  else if arp.val = 1 then
    (if p.val ∈ nonstandard then .Ok (.LinuxNonstandardEtherType p) else .Ok (.EtherType p))
  else .Err (.UnsupportedArpHardwareId arp)

def protoVal : PT → Std.U16
  | .Ignored v => v
  | .NetlinkProtocolType v => v
  | .GenericRoutingEncapsulationProtocolType v => v
  | .EtherType v => v
  | .LinuxNonstandardEtherType v => v

def e2 (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) : E2 :=
  { source := src, destination := dst, ether_type := et }

def encodeE2 (h : E2) : List Std.U8 := h.destination.val ++ h.source.val ++ be16 h.ether_type.val

def encodeSll (h : SLL) : List Std.U8 :=
  be16 h.packet_type.val ++ be16 h.arp_hrd_type.val ++ be16 h.sender_address_valid_length.val ++
    h.sender_address.val ++ be16 (protoVal h.protocol_type).val

def decodeSll (b : List Std.U8) : core.result.Result SLL HE :=
  let pt := beAt b 0
  let arp := beAt b 2
  if pt.val > 7 then .Err (.UnsupportedPacketTypeField pt)
  else match protoModel arp (beAt b 14) with
    | .Err e => .Err e
    | .Ok p => .Ok { packet_type := pt, arp_hrd_type := arp, sender_address_valid_length := beAt b 4,
                     sender_address := mkArr 8#usize ((b.drop 6).take 8), protocol_type := p }

/-- A *valid* SLL header built from scalars: packet type `≤ 7`, a supported ARP
hardware id and the protocol type `try_from` gives for it. -/
def validSll (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16) (small : Bool) : SLL :=
  let arp := mkU .U16 (supportedArp.getD (a.val % 5) 1)
  let pv := if small then mkU .U16 (p.val % 256) else p
  let proto := match protoModel arp pv with
    | .Ok x => x
    | .Err _ => .Ignored pv
  { packet_type := mkU .U16 (pt.val % 8), arp_hrd_type := arp, sender_address_valid_length := sal,
    sender_address := addr, protocol_type := proto }

/-- SLL bytes with a packet-type / ARP field that is often (not always) valid. -/
def sllBytes (pt : Std.U16) (ptOk : Bool) (a : Std.U16) (arpOk : Bool) (rest : Std.Array Std.U8 10#usize)
    (p : Std.U16) (small : Bool) : Std.Array Std.U8 16#usize :=
  let ptv := if ptOk then pt.val % 8 else pt.val
  let arpv := if arpOk then supportedArp.getD (a.val % 5) 1 else a.val
  let pv := if small then p.val % 256 else p.val
  mkArr 16#usize (be16 ptv ++ be16 arpv ++ rest.val ++ be16 pv)

def intoU16 (arp pv : Std.U16) : RustM Std.U16 := do
  let r ← link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from
    (arp, pv)
  match r with
  | .Ok x => U16.Insts.CoreConvertFromLinuxSllProtocolType.from x
  | .Err _ => fail .panic

def isOk {α β} : core.result.Result α β → Bool
  | .Ok _ => true
  | .Err _ => false

def reencodeSll (b : Std.Array Std.U8 16#usize) : RustM (Std.Array Std.U8 16#usize) :=
  match decodeSll b.val with
  | .Ok h => link.linux_sll_header.LinuxSllHeader.to_bytes h
  | .Err _ => fail .panic

def mkProto (k : Nat) (x : Std.U16) : PT :=
  match k % 5 with
  | 0 => .Ignored x | 1 => .NetlinkProtocolType x | 2 => .GenericRoutingEncapsulationProtocolType x
  | 3 => .EtherType x | _ => .LinuxNonstandardEtherType x

def runWrite (h : E2) (s : Slice Std.U8) :=
  (do
    let (r, back) ← link.ethernet2_header.Ethernet2Header.write_to_slice h s
    ok (r, back r, back (.Ok (mkSlice (s.val.drop 14).reverse))))
def runWriteSll (h : SLL) (s : Slice Std.U8) :=
  (do
    let (r, back) ← link.linux_sll_header.LinuxSllHeader.write_to_slice h s
    ok (r, back r, back (.Ok (mkSlice (s.val.drop 16).reverse))))

end RSGBGold.EtherparseLink

namespace Benchmark.V2.Etherparse.Link.Gold

open RSGBGold.EtherparseLink

/-! ## Ethernet II header -/

def gold_e2_constants (_x : Std.U8) : Prop :=
  link.ethernet2_header.Ethernet2Header.LEN = 14#usize ∧
  link.ethernet2_header.Ethernet2Header.SERIALIZED_SIZE = 14#usize

/-- `to_bytes`: destination ‖ source ‖ big-endian ether type. -/
def gold_e2_to_bytes (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) : Prop :=
  link.ethernet2_header.Ethernet2Header.to_bytes (e2 src dst et) ⦃ b => b.val = encodeE2 (e2 src dst et) ⦄

def gold_e2_from_bytes (b : Std.Array Std.U8 14#usize) : Prop :=
  link.ethernet2_header.Ethernet2Header.from_bytes b =
    ok (e2 (mkArr 6#usize ((b.val.drop 6).take 6)) (mkArr 6#usize (b.val.take 6)) (beAt b.val 12))

def gold_e2_roundtrip (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) : Prop :=
  (do
    let b ← link.ethernet2_header.Ethernet2Header.to_bytes (e2 src dst et)
    link.ethernet2_header.Ethernet2Header.from_bytes b) = ok (e2 src dst et)

def gold_e2_roundtrip_bytes (b : Std.Array Std.U8 14#usize) : Prop :=
  (do
    let h ← link.ethernet2_header.Ethernet2Header.from_bytes b
    link.ethernet2_header.Ethernet2Header.to_bytes h) = ok b

/-- `write_to_slice`: error (slice unchanged) iff the slice is shorter than 14 bytes;
otherwise the header is written to the first 14 bytes and the rest of the slice
is returned (writes through it reach the original slice). -/
def e2WriteOk (h : E2) (s : Slice Std.U8) : Prop :=
  (do
    let (r, back) ← link.ethernet2_header.Ethernet2Header.write_to_slice h s
    let t := mkSlice (s.val.drop 14).reverse
    ok (r, back r, back (.Ok t))) ⦃ p =>
      (s.val.length < 14 →
        p.1 = .Err ({ required_len := 14#usize, len := mkU .Usize s.val.length,
                      layer := .Ethernet2Header, layer_start_offset := 0#usize } : SWE) ∧
        p.2.1 = s) ∧
      (14 ≤ s.val.length →
        p.1 = .Ok (mkSlice (s.val.drop 14)) ∧
        p.2.1.val = encodeE2 h ++ s.val.drop 14 ∧
        p.2.2.val = encodeE2 h ++ (s.val.drop 14).reverse) ⦄

def gold_e2_write (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) (s : Slice Std.U8) : Prop :=
  e2WriteOk (e2 src dst et) s

/-- The same around the length boundary (slices of 11 … 17 bytes). -/
def gold_e2_write_boundary (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) (k : Std.U8)
    (fill : Std.Array Std.U8 17#usize) : Prop :=
  e2WriteOk (e2 src dst et) (mkSlice (fill.val.take (11 + k.val % 7)))

def gold_e2_header_len (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) : Prop :=
  link.ethernet2_header.Ethernet2Header.header_len (e2 src dst et) = ok 14#usize

def gold_e2_eq (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) (d : Std.U8)
    (src' dst' : Std.Array Std.U8 6#usize) (et' : Std.U16) : Prop :=
  let a := e2 src dst et
  let b := e2 (if d.val % 2 = 1 then src' else src) (if d.val / 2 % 2 = 1 then dst' else dst)
              (if d.val / 4 % 2 = 1 then et' else et)
  link.ethernet2_header.Ethernet2Header.Insts.CoreCmpPartialEqEthernet2Header.eq a b = ok (decide (a = b))

def gold_e2_clone_default (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) : Prop :=
  link.ethernet2_header.Ethernet2Header.Insts.CoreCloneClone.clone (e2 src dst et) = ok (e2 src dst et) ∧
  link.ethernet2_header.Ethernet2Header.Insts.CoreDefaultDefault.default =
    ok (e2 (Array.repeat 6#usize 0#u8) (Array.repeat 6#usize 0#u8) 0#u16)

/-! ## Linux SLL field types -/

def gold_packet_type_try_from (v : Std.U16) : Prop :=
  link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from v =
    ok (if v.val ≤ 7 then .Ok v else .Err (.UnsupportedPacketTypeField v))

def gold_packet_type_try_from_small (k : Std.U8) : Prop :=
  gold_packet_type_try_from (mkU .U16 (k.val % 16))

def gold_packet_type_constants (_x : Std.U8) : Prop :=
  [link.linux_sll_packet_type.LinuxSllPacketType.HOST, link.linux_sll_packet_type.LinuxSllPacketType.BROADCAST,
   link.linux_sll_packet_type.LinuxSllPacketType.MULTICAST, link.linux_sll_packet_type.LinuxSllPacketType.OTHERHOST,
   link.linux_sll_packet_type.LinuxSllPacketType.OUTGOING, link.linux_sll_packet_type.LinuxSllPacketType.LOOPBACK,
   link.linux_sll_packet_type.LinuxSllPacketType.USER, link.linux_sll_packet_type.LinuxSllPacketType.KERNEL].map (·.val)
    = [0, 1, 2, 3, 4, 5, 6, 7]

def gold_nonstandard_try_from (v : Std.U16) : Prop :=
  link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.Insts.CoreConvertTryFromU16Tuple.try_from v =
    ok (if v.val ∈ nonstandard then .Ok v else .Err ())

def gold_nonstandard_try_from_small (k : Std.U16) : Prop :=
  gold_nonstandard_try_from (mkU .U16 (k.val % 300))

def gold_nonstandard_constants (_x : Std.U8) : Prop :=
  [link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.N802_3,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.AX25,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.ALL,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.N802_2,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.SNAP,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.DDCMP,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.WAN_PPP,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.PPP_MP,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.LOCALTALK,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CAN,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CANFD,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CANXL,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.PPPTALK,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.TR_802_2,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.MOBITEX,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CONTROL,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.IRDA,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.ECONET,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.HDLC,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.ARCNET,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.DSA,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.TRAILER,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.PHONET,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.IEEE802154,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.CAIF,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.XDSA,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.MAP,
   link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.MCTP].map (·.val) = nonstandard

def gold_protocol_try_from (arp p : Std.U16) : Prop :=
  link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from
    (arp, p) = ok (protoModel arp p)

/-- The same with a supported ARP id and (often) a small protocol value. -/
def gold_protocol_try_from_supported (a : Std.U8) (p : Std.U16) (small : Bool) : Prop :=
  gold_protocol_try_from (mkU .U16 (supportedArp.getD (a.val % 5) 1)) (if small then mkU .U16 (p.val % 300) else p)

/-- `u16::from(LinuxSllProtocolType)` returns the carried value; conversion back
from a supported ARP id restores the variant. -/
def gold_protocol_into_u16 (a : Std.U8) (p : Std.U16) (small : Bool) : Prop :=
  let arp := mkU .U16 (supportedArp.getD (a.val % 5) 1)
  let pv := if small then mkU .U16 (p.val % 300) else p
  intoU16 arp pv = ok pv

def gold_protocol_eq (k1 k2 : Std.U8) (v : Std.U16) (same : Bool) (w : Std.U16) : Prop :=
  let a := mkProto k1.val v
  let b := mkProto k2.val (if same then v else w)
  link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreCmpPartialEqLinuxSllProtocolType.eq a b
    = ok (decide (a = b))

def gold_u16_conversions (v : Std.U16) : Prop :=
  net.arp_hardware_id.ArpHardwareId.Insts.CoreConvertFromU16.from v = ok v ∧
  U16.Insts.CoreConvertFromArpHardwareId.from v = ok v ∧
  U16.Insts.CoreConvertFromLinuxSllPacketType.from v = ok v ∧
  U16.Insts.CoreConvertFromEtherType.from v = ok v ∧
  U16.Insts.CoreConvertFromLinuxNonstandardEtherType.from v = ok v

/-! ## Linux SLL header -/

def gold_sll_constants (_x : Std.U8) : Prop :=
  link.linux_sll_header.LinuxSllHeader.LEN = 16#usize

def gold_sll_to_bytes (pt arp sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (k : Std.U8) (v : Std.U16) : Prop :=
  let proto := mkProto k.val v
  let h : SLL := { packet_type := pt, arp_hrd_type := arp, sender_address_valid_length := sal,
                   sender_address := addr, protocol_type := proto }
  link.linux_sll_header.LinuxSllHeader.to_bytes h ⦃ b => b.val = encodeSll h ⦄

/-- `from_bytes` agrees with the reference decoder (random bytes). -/
def gold_sll_from_bytes (b : Std.Array Std.U8 16#usize) : Prop :=
  link.linux_sll_header.LinuxSllHeader.from_bytes b = ok (decodeSll b.val)

/-- … and on bytes whose packet type / ARP id are often valid. -/
def gold_sll_from_bytes_mixed (pt : Std.U16) (ptOk : Bool) (a : Std.U16) (arpOk : Bool)
    (rest : Std.Array Std.U8 10#usize) (p : Std.U16) (small : Bool) : Prop :=
  let b := sllBytes pt ptOk a arpOk rest p small
  link.linux_sll_header.LinuxSllHeader.from_bytes b = ok (decodeSll b.val)

/-- Valid headers survive `to_bytes` / `from_bytes`. -/
def gold_sll_roundtrip (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16)
    (small : Bool) : Prop :=
  (do
    let b ← link.linux_sll_header.LinuxSllHeader.to_bytes (validSll pt a sal addr p small)
    link.linux_sll_header.LinuxSllHeader.from_bytes b) = ok (.Ok (validSll pt a sal addr p small))

/-- Bytes that parse are reproduced by `to_bytes`. -/
def gold_sll_roundtrip_bytes (pt : Std.U16) (a : Std.U16) (rest : Std.Array Std.U8 10#usize)
    (p : Std.U16) (small : Bool) : Prop :=
  let b := sllBytes pt true a true rest p small
  isOk (decodeSll b.val) = true → reencodeSll b = ok b

def sllWriteOk (h : SLL) (s : Slice Std.U8) : Prop :=
  (do
    let (r, back) ← link.linux_sll_header.LinuxSllHeader.write_to_slice h s
    let t := mkSlice (s.val.drop 16).reverse
    ok (r, back r, back (.Ok t))) ⦃ p =>
      (s.val.length < 16 →
        p.1 = .Err ({ required_len := 16#usize, len := mkU .Usize s.val.length,
                      layer := .LinuxSllHeader, layer_start_offset := 0#usize } : SWE) ∧
        p.2.1 = s) ∧
      (16 ≤ s.val.length →
        p.1 = .Ok (mkSlice (s.val.drop 16)) ∧
        p.2.1.val = encodeSll h ++ s.val.drop 16 ∧
        p.2.2.val = encodeSll h ++ (s.val.drop 16).reverse) ⦄

def gold_sll_write (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16)
    (small : Bool) (s : Slice Std.U8) : Prop :=
  sllWriteOk (validSll pt a sal addr p small) s

def gold_sll_write_boundary (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16)
    (k : Std.U8) (fill : Std.Array Std.U8 19#usize) : Prop :=
  sllWriteOk (validSll pt a sal addr p false) (mkSlice (fill.val.take (13 + k.val % 7)))

def gold_sll_header_len (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16) : Prop :=
  link.linux_sll_header.LinuxSllHeader.header_len (validSll pt a sal addr p false) = ok 16#usize

def gold_sll_eq (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16) (d : Std.U8)
    (pt' a' : Std.U8) (sal' : Std.U16) (addr' : Std.Array Std.U8 8#usize) (p' : Std.U16) : Prop :=
  let x := validSll pt a sal addr p true
  let y0 := validSll pt' a' sal' addr' p' true
  let y : SLL := { packet_type := if d.val % 2 = 1 then y0.packet_type else x.packet_type,
                   arp_hrd_type := if d.val / 2 % 2 = 1 then y0.arp_hrd_type else x.arp_hrd_type,
                   sender_address_valid_length := if d.val / 4 % 2 = 1 then sal' else sal,
                   sender_address := if d.val / 8 % 2 = 1 then addr' else addr,
                   protocol_type := if d.val / 16 % 2 = 1 then y0.protocol_type else x.protocol_type }
  link.linux_sll_header.LinuxSllHeader.Insts.CoreCmpPartialEqLinuxSllHeader.eq x y = ok (decide (x = y))

def gold_sll_clone (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16) : Prop :=
  link.linux_sll_header.LinuxSllHeader.Insts.CoreCloneClone.clone (validSll pt a sal addr p true) =
    ok (validSll pt a sal addr p true)

/-! ## Differential-testing probes -/

def diff_e2_to_bytes (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) :=
  link.ethernet2_header.Ethernet2Header.to_bytes (e2 src dst et)
def diff_e2_from_bytes (b : Std.Array Std.U8 14#usize) :=
  link.ethernet2_header.Ethernet2Header.from_bytes b
def diff_e2_write (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) (s : Slice Std.U8) :=
  runWrite (e2 src dst et) s
def diff_e2_write_boundary (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) (k : Std.U8)
    (fill : Std.Array Std.U8 17#usize) :=
  runWrite (e2 src dst et) (mkSlice (fill.val.take (11 + k.val % 7)))
def diff_e2_misc (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) :=
  (link.ethernet2_header.Ethernet2Header.header_len (e2 src dst et),
   link.ethernet2_header.Ethernet2Header.Insts.CoreCloneClone.clone (e2 src dst et),
   link.ethernet2_header.Ethernet2Header.Insts.CoreDefaultDefault.default,
   link.ethernet2_header.Ethernet2Header.LEN, link.ethernet2_header.Ethernet2Header.SERIALIZED_SIZE)
def diff_e2_eq (src dst : Std.Array Std.U8 6#usize) (et : Std.U16) (d : Std.U8)
    (src' dst' : Std.Array Std.U8 6#usize) (et' : Std.U16) :=
  link.ethernet2_header.Ethernet2Header.Insts.CoreCmpPartialEqEthernet2Header.eq (e2 src dst et)
    (e2 (if d.val % 2 = 1 then src' else src) (if d.val / 2 % 2 = 1 then dst' else dst)
        (if d.val / 4 % 2 = 1 then et' else et))
def diff_packet_type (v : Std.U16) :=
  link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from v
def diff_packet_type_small (k : Std.U8) :=
  link.linux_sll_packet_type.LinuxSllPacketType.Insts.CoreConvertTryFromU16HeaderError.try_from (mkU .U16 (k.val % 16))
def diff_nonstandard (k : Std.U16) :=
  link.linux_nonstandard_ether_type.LinuxNonstandardEtherType.Insts.CoreConvertTryFromU16Tuple.try_from (mkU .U16 (k.val % 300))
def diff_protocol (arp p : Std.U16) :=
  link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from (arp, p)
def diff_protocol_supported (a : Std.U8) (p : Std.U16) (small : Bool) :=
  link.linux_sll_protocol_type.LinuxSllProtocolType.Insts.CoreConvertTryFromPairArpHardwareIdU16HeaderError.try_from
    (mkU .U16 (supportedArp.getD (a.val % 5) 1), if small then mkU .U16 (p.val % 300) else p)
def diff_sll_to_bytes (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16) (small : Bool) :=
  link.linux_sll_header.LinuxSllHeader.to_bytes (validSll pt a sal addr p small)
def diff_sll_from_bytes (b : Std.Array Std.U8 16#usize) :=
  link.linux_sll_header.LinuxSllHeader.from_bytes b
def diff_sll_from_bytes_mixed (pt : Std.U16) (ptOk : Bool) (a : Std.U16) (arpOk : Bool)
    (rest : Std.Array Std.U8 10#usize) (p : Std.U16) (small : Bool) :=
  link.linux_sll_header.LinuxSllHeader.from_bytes (sllBytes pt ptOk a arpOk rest p small)
def diff_sll_write (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16)
    (small : Bool) (s : Slice Std.U8) :=
  runWriteSll (validSll pt a sal addr p small) s
def diff_sll_write_boundary (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16)
    (k : Std.U8) (fill : Std.Array Std.U8 19#usize) :=
  runWriteSll (validSll pt a sal addr p false) (mkSlice (fill.val.take (13 + k.val % 7)))
def diff_sll_misc (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16) :=
  (link.linux_sll_header.LinuxSllHeader.header_len (validSll pt a sal addr p false),
   link.linux_sll_header.LinuxSllHeader.Insts.CoreCloneClone.clone (validSll pt a sal addr p true),
   link.linux_sll_header.LinuxSllHeader.LEN)
def diff_sll_eq (pt a : Std.U8) (sal : Std.U16) (addr : Std.Array Std.U8 8#usize) (p : Std.U16) (d : Std.U8)
    (pt' a' : Std.U8) (sal' : Std.U16) (addr' : Std.Array Std.U8 8#usize) (p' : Std.U16) :=
  let x := validSll pt a sal addr p true
  let y0 := validSll pt' a' sal' addr' p' true
  link.linux_sll_header.LinuxSllHeader.Insts.CoreCmpPartialEqLinuxSllHeader.eq x
    { packet_type := if d.val % 2 = 1 then y0.packet_type else x.packet_type,
      arp_hrd_type := if d.val / 2 % 2 = 1 then y0.arp_hrd_type else x.arp_hrd_type,
      sender_address_valid_length := if d.val / 4 % 2 = 1 then sal' else sal,
      sender_address := if d.val / 8 % 2 = 1 then addr' else addr,
      protocol_type := if d.val / 16 % 2 = 1 then y0.protocol_type else x.protocol_type }

end Benchmark.V2.Etherparse.Link.Gold
