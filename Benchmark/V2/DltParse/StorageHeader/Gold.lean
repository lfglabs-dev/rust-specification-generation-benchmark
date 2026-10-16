import Benchmark.V2.Prelude
import DltParseStorageHeader.Extraction

/-! Hidden gold specification for target `dlt_parse/storage_header`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM dlt_parse RSGB

namespace Benchmark.V2.DltParse.StorageHeader.Gold

abbrev SH := storage.storage_header.StorageHeader
abbrev PErr := error.storage_header_start_pattern_error.StorageHeaderStartPatternError

/-! ## Independent reference model -/

/-- The DLT storage-header magic `"DLT" 0x01`. -/
def magic : List Nat := [0x44, 0x4C, 0x54, 0x01]

def bytesOf (l : List Nat) : List Std.U8 := l.map (mkU .U8)

/-- Little-endian bytes of a 32-bit value. -/
def le32 (x : Nat) : List Nat := [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256]

/-- Little-endian decoding of (up to) four bytes. -/
def ofLe (l : List Std.U8) : Nat :=
  l.foldr (fun b acc => b.val + 256 * acc) 0

def mkArr (n : Std.Usize) (l : List Std.U8) : Std.Array Std.U8 n :=
  if h : l.length = n.val then ⟨l, h⟩ else ⟨List.replicate n.val 0#u8, by simp⟩

def hdr (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) : SH :=
  { timestamp_seconds := ts, timestamp_microseconds := tms, ecu_id := ecu }

/-- Model of the wire encoding. -/
def encode (h : SH) : List Std.U8 :=
  bytesOf (magic ++ le32 h.timestamp_seconds.val ++ le32 h.timestamp_microseconds.val) ++ h.ecu_id.val

/-- Model of the decoder. -/
def decode (b : List Std.U8) : core.result.Result SH PErr :=
  if (b.take 4).map (·.val) = magic then
    .Ok { timestamp_seconds := mkU .U32 (ofLe ((b.drop 4).take 4)),
          timestamp_microseconds := mkU .U32 (ofLe ((b.drop 8).take 4)),
          ecu_id := mkArr 4#usize ((b.drop 12).take 4) }
  else .Err { actual_pattern := mkArr 4#usize (b.take 4) }

/-- 16 bytes starting with the magic. -/
def withMagic (rest : Std.Array Std.U8 12#usize) : Std.Array Std.U8 16#usize :=
  mkArr 16#usize (bytesOf magic ++ rest.val)

/-- 16 bytes starting with the magic, except byte `k < 4` replaced by `v`. -/
def nearMagic (rest : Std.Array Std.U8 12#usize) (k : Nat) (v : Std.U8) : Std.Array Std.U8 16#usize :=
  mkArr 16#usize ((bytesOf magic).set k v ++ rest.val)

/-! ## Constants -/

def gold_constants (_x : Std.U8) : Prop :=
  storage.storage_header.StorageHeader.PATTERN_AT_START.val = bytesOf magic ∧
  storage.storage_header.StorageHeader.BYTE_LEN = 16#usize

/-! ## `to_bytes` -/

/-- `to_bytes` never panics and produces magic ‖ LE(seconds) ‖ LE(microseconds) ‖ ecu_id. -/
def gold_to_bytes_exact (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) : Prop :=
  storage.storage_header.StorageHeader.to_bytes (hdr ts tms ecu) ⦃ b => b.val = encode (hdr ts tms ecu) ⦄

/-- The serialised header starts with `PATTERN_AT_START` and is `BYTE_LEN` long. -/
def gold_to_bytes_pattern (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) : Prop :=
  storage.storage_header.StorageHeader.to_bytes (hdr ts tms ecu) ⦃ b =>
    b.val.take 4 = storage.storage_header.StorageHeader.PATTERN_AT_START.val ∧
    b.val.length = storage.storage_header.StorageHeader.BYTE_LEN.val ⦄

/-! ## `from_bytes` -/

/-- `from_bytes` never panics and agrees with the reference decoder (arbitrary bytes:
almost always the error branch). -/
def gold_from_bytes_exact (b : Std.Array Std.U8 16#usize) : Prop :=
  storage.storage_header.StorageHeader.from_bytes b = ok (decode b.val)

/-- On input carrying the correct start pattern, `from_bytes` decodes the
little-endian fields and the ECU id. -/
def gold_from_bytes_ok (rest : Std.Array Std.U8 12#usize) : Prop :=
  storage.storage_header.StorageHeader.from_bytes (withMagic rest) =
    ok (.Ok { timestamp_seconds := mkU .U32 (ofLe (rest.val.take 4)),
              timestamp_microseconds := mkU .U32 (ofLe ((rest.val.drop 4).take 4)),
              ecu_id := mkArr 4#usize (rest.val.drop 8) })

/-- A single wrong byte in the start pattern yields the pattern error carrying
exactly the first four bytes. -/
def gold_from_bytes_near_pattern (rest : Std.Array Std.U8 12#usize) (i v : Std.U8) : Prop :=
  let k := i.val % 4
  v.val ≠ magic.getD k 0 →
    storage.storage_header.StorageHeader.from_bytes (nearMagic rest k v) =
      ok (.Err { actual_pattern := mkArr 4#usize ((bytesOf magic).set k v) })

/-! ## Round trips -/

def gold_roundtrip (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) : Prop :=
  (do
    let b ← storage.storage_header.StorageHeader.to_bytes (hdr ts tms ecu)
    storage.storage_header.StorageHeader.from_bytes b) ⦃ r => r = .Ok (hdr ts tms ecu) ⦄

/-- Every 16-byte buffer with the right start pattern is the encoding of the
header `from_bytes` returns for it. -/
def gold_roundtrip_bytes (rest : Std.Array Std.U8 12#usize) : Prop :=
  let h : SH := { timestamp_seconds := mkU .U32 (ofLe (rest.val.take 4)),
                  timestamp_microseconds := mkU .U32 (ofLe ((rest.val.drop 4).take 4)),
                  ecu_id := mkArr 4#usize (rest.val.drop 8) }
  storage.storage_header.StorageHeader.from_bytes (withMagic rest) = ok (.Ok h) ∧
  storage.storage_header.StorageHeader.to_bytes h = ok (withMagic rest)

/-! ## Derived `PartialEq` / `Clone` -/

/-- `eq` is field-wise equality (the second header differs from the first in the
fields selected by the flags). -/
def gold_eq (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) (d1 d2 d3 : Bool)
    (ts' tms' : Std.U32) (ecu' : Std.Array Std.U8 4#usize) : Prop :=
  let a := hdr ts tms ecu
  let b := hdr (if d1 then ts' else ts) (if d2 then tms' else tms) (if d3 then ecu' else ecu)
  storage.storage_header.StorageHeader.Insts.CoreCmpPartialEqStorageHeader.eq a b = ok (decide (a = b))

def gold_clone (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) : Prop :=
  storage.storage_header.StorageHeader.Insts.CoreCloneClone.clone (hdr ts tms ecu) = ok (hdr ts tms ecu)

/-! ## Differential-testing probes -/

def diff_to_bytes (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) :=
  storage.storage_header.StorageHeader.to_bytes (hdr ts tms ecu)
def diff_from_bytes (b : Std.Array Std.U8 16#usize) :=
  storage.storage_header.StorageHeader.from_bytes b
def diff_from_bytes_magic (rest : Std.Array Std.U8 12#usize) :=
  storage.storage_header.StorageHeader.from_bytes (withMagic rest)
def diff_from_bytes_near (rest : Std.Array Std.U8 12#usize) (i v : Std.U8) :=
  storage.storage_header.StorageHeader.from_bytes (nearMagic rest (i.val % 4) v)
def diff_eq (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) (d1 d2 d3 : Bool)
    (ts' tms' : Std.U32) (ecu' : Std.Array Std.U8 4#usize) :=
  storage.storage_header.StorageHeader.Insts.CoreCmpPartialEqStorageHeader.eq (hdr ts tms ecu)
    (hdr (if d1 then ts' else ts) (if d2 then tms' else tms) (if d3 then ecu' else ecu))
def diff_clone (ts tms : Std.U32) (ecu : Std.Array Std.U8 4#usize) :=
  storage.storage_header.StorageHeader.Insts.CoreCloneClone.clone (hdr ts tms ecu)
def diff_constants (_x : Std.U8) :=
  (storage.storage_header.StorageHeader.PATTERN_AT_START, storage.storage_header.StorageHeader.BYTE_LEN)

end Benchmark.V2.DltParse.StorageHeader.Gold
