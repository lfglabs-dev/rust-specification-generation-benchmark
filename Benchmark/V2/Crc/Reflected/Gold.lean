import Benchmark.V2.Prelude
import CrcReflected.Extraction

/-! Hidden gold specification for target `crc/reflected`.

API: crate `crc` 1.8.1 (mrhooray/crc-rs), modules `crc16`, `crc32`, `crc64`:
`make_table(poly)`, `update(value, &table, bytes)`, the catalogue checksums
(`checksum_x25`, `checksum_usb`, `checksum_ieee`, `checksum_castagnoli`,
`checksum_koopman`, `checksum_ecma`, `checksum_iso`) and the stateful
`Digest` (`new`, `new_with_initial`, `Hasher{16,32,64}::{write, reset, sum}`,
`core::hash::Hasher::{write, finish}`).

Contract. All CRCs of this crate are *reflected* (LSB-first) CRCs of width
`w ∈ {16, 32, 64}` whose polynomial is given in reflected form. With the
bitwise shift register `step(r) = r odd ? (r >> 1) ^ poly : r >> 1`,
`update(v, make_table(poly), bytes)` is the CRC register run started from the
complement of `v`, one byte at a time (`r ← step⁸(r ^ byte)`), complemented at
the end (so `v` is "the CRC of the data so far" and `update` continues it:
updating with `a` then `b` = updating with `a ++ b`; the standard
"init = xorout = all ones" catalogue CRCs are `update(0, …)`).
`make_table(poly)[i] = step⁸(i)`. The named checksums are the catalogue
algorithms CRC-16/X-25, CRC-16/USB, CRC-32 (ISO-HDLC), CRC-32C, CRC-32K
(Koopman), CRC-64/XZ (ECMA-182 reflected), CRC-64/GO-ISO; their check values
on "123456789" are the documented ones. A `Digest` keeps the running CRC:
`new(poly)` starts from 0, `new_with_initial(poly, init)` from `init`, `write`
continues it, `sum` reads it, `reset` returns to the initial value,
`Hasher::finish` is the sum zero-extended to `u64`. Nothing panics. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM crc RSGB

namespace RSGBGold.Crc.Reflected

def toSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

/-! Independent bitwise model of a reflected CRC on `Nat`. -/

def bitStep (poly r : Nat) : Nat := if r % 2 = 1 then (r / 2) ^^^ poly else r / 2

def step8 (poly r : Nat) : Nat := Nat.iterate (bitStep poly) 8 r

def byteStep (poly : Nat) (r : Nat) (b : Std.U8) : Nat := step8 poly (r ^^^ b.val)

def ones (w : Nat) : Nat := 2 ^ w - 1

/-- `update(v, table(poly), bytes)` for a width-`w` reflected CRC. -/
def model (w poly v : Nat) (bytes : List Std.U8) : Nat :=
  (bytes.foldl (byteStep poly) (v ^^^ ones w)) ^^^ ones w

/-- Little-endian bytes of the `w`-bit value `x`. -/
def leBytes (w x : Nat) : List Std.U8 :=
  (List.range (w / 8)).map (fun i => mkU .U8 (x / 2 ^ (8 * i)))

def check : List Std.U8 := [49, 50, 51, 52, 53, 54, 55, 56, 57].map (mkU .U8 ·)

/-! Digest operation scripts: `tag % 5` = 0 `Hasher*::write`, 1 `reset`,
2 record `sum`, 3 `core::hash::Hasher::write`, 4 record `finish`. -/

def modelOps (w poly init : Nat) : Nat → List (Std.U8 × List Std.U8) → List Nat
  | v, [] => [v]
  | v, (t, bs) :: rest =>
    match t.val % 5 with
    | 0 => modelOps w poly init (model w poly v bs) rest
    | 1 => modelOps w poly init init rest
    | 3 => modelOps w poly init (model w poly v bs) rest
    | _ => v :: modelOps w poly init v rest

def ops16 (d : crc16.Digest) : List (Std.U8 × List Std.U8) → RustM (List Nat)
  | [] => do let s ← crc16.Digest.Insts.CrcCrc16Hasher16.sum16 d; ok [s.val]
  | (t, bs) :: rest =>
    match t.val % 5 with
    | 0 => do let d ← crc16.Digest.Insts.CrcCrc16Hasher16.write d (toSlice bs); ops16 d rest
    | 1 => do let d ← crc16.Digest.Insts.CrcCrc16Hasher16.reset d; ops16 d rest
    | 3 => do let d ← crc16.Digest.Insts.CoreHashHasher.write d (toSlice bs); ops16 d rest
    | 4 => do let s ← crc16.Digest.Insts.CoreHashHasher.finish d; let r ← ops16 d rest; ok (s.val :: r)
    | _ => do let s ← crc16.Digest.Insts.CrcCrc16Hasher16.sum16 d; let r ← ops16 d rest; ok (s.val :: r)

def ops32 (d : crc32.Digest) : List (Std.U8 × List Std.U8) → RustM (List Nat)
  | [] => do let s ← crc32.Digest.Insts.CrcCrc32Hasher32.sum32 d; ok [s.val]
  | (t, bs) :: rest =>
    match t.val % 5 with
    | 0 => do let d ← crc32.Digest.Insts.CrcCrc32Hasher32.write d (toSlice bs); ops32 d rest
    | 1 => do let d ← crc32.Digest.Insts.CrcCrc32Hasher32.reset d; ops32 d rest
    | 3 => do let d ← crc32.Digest.Insts.CoreHashHasher.write d (toSlice bs); ops32 d rest
    | 4 => do let s ← crc32.Digest.Insts.CoreHashHasher.finish d; let r ← ops32 d rest; ok (s.val :: r)
    | _ => do let s ← crc32.Digest.Insts.CrcCrc32Hasher32.sum32 d; let r ← ops32 d rest; ok (s.val :: r)

def ops64 (d : crc64.Digest) : List (Std.U8 × List Std.U8) → RustM (List Nat)
  | [] => do let s ← crc64.Digest.Insts.CrcCrc64Hasher64.sum64 d; ok [s.val]
  | (t, bs) :: rest =>
    match t.val % 5 with
    | 0 => do let d ← crc64.Digest.Insts.CrcCrc64Hasher64.write d (toSlice bs); ops64 d rest
    | 1 => do let d ← crc64.Digest.Insts.CrcCrc64Hasher64.reset d; ops64 d rest
    | 3 => do let d ← crc64.Digest.Insts.CoreHashHasher.write d (toSlice bs); ops64 d rest
    | 4 => do let s ← crc64.Digest.Insts.CoreHashHasher.finish d; let r ← ops64 d rest; ok (s.val :: r)
    | _ => do let s ← crc64.Digest.Insts.CrcCrc64Hasher64.sum64 d; let r ← ops64 d rest; ok (s.val :: r)

/-! Fixed polynomials (catalogue ones first, then others); their tables and
digests are computed once per run (closed terms are evaluated once). -/

def polys16 : List Std.U16 := [0x8408#u16, 0xA001#u16, 0x1021#u16, 0x8005#u16, 0xFFFF#u16, 0x0001#u16, 0x8000#u16, 0xC867#u16]
def polys32 : List Std.U32 := [0xEDB88320#u32, 0x82F63B78#u32, 0xEB31D82E#u32, 0x04C11DB7#u32, 0xFFFFFFFF#u32,
  0x00000001#u32, 0x80000000#u32, 0xD5828281#u32]
def polys64 : List Std.U64 := [0xC96C5795D7870F42#u64, 0xD800000000000000#u64, 0x42F0E1EBA9EA3693#u64,
  0xFFFFFFFFFFFFFFFF#u64, 0x0000000000000001#u64, 0x8000000000000000#u64, 0x95AC9329AC4BC9B5#u64, 0x000000000000001B#u64]

def NPOLY : Nat := 8

def pol16 (k : Nat) : Std.U16 := polys16.getD (k % NPOLY) 0#u16
def pol32 (k : Nat) : Std.U32 := polys32.getD (k % NPOLY) 0#u32
def pol64 (k : Nat) : Std.U64 := polys64.getD (k % NPOLY) 0#u64

def tabs16 : List (RustM (Std.Array Std.U16 256#usize)) := polys16.map util.make_table_crc16
def tabs32 : List (RustM (Std.Array Std.U32 256#usize)) := polys32.map util.make_table_crc32
def tabs64 : List (RustM (Std.Array Std.U64 256#usize)) := polys64.map util.make_table_crc64

def tab16 (k : Nat) : RustM (Std.Array Std.U16 256#usize) := tabs16.getD (k % NPOLY) (fail .panic)
def tab32 (k : Nat) : RustM (Std.Array Std.U32 256#usize) := tabs32.getD (k % NPOLY) (fail .panic)
def tab64 (k : Nat) : RustM (Std.Array Std.U64 256#usize) := tabs64.getD (k % NPOLY) (fail .panic)

def upd16 (v : Std.U16) (k : Nat) (bs : List Std.U8) : RustM Std.U16 := do
  let t ← tab16 k; crc16.update v t (toSlice bs)
def upd32 (v : Std.U32) (k : Nat) (bs : List Std.U8) : RustM Std.U32 := do
  let t ← tab32 k; crc32.update v t (toSlice bs)
def upd64 (v : Std.U64) (k : Nat) (bs : List Std.U8) : RustM Std.U64 := do
  let t ← tab64 k; crc64.update v t (toSlice bs)

/-- Initial values used for `new_with_initial` (with the first four polynomials). -/
def inits16 : List Std.U16 := [0#u16, 0xFFFF#u16, 0x1D0F#u16]
def inits32 : List Std.U32 := [0#u32, 0xFFFFFFFF#u32, 0x12345678#u32]
def inits64 : List Std.U64 := [0#u64, 0xFFFFFFFFFFFFFFFF#u64, 0x0123456789ABCDEF#u64]

def pairs : List (Nat × Nat) := (List.range 4).flatMap (fun p => (List.range 3).map (fun i => (p, i)))

def digI16 : List (RustM crc16.Digest) :=
  pairs.map (fun (p, i) => crc16.Digest.new_with_initial (pol16 p) (inits16.getD i 0#u16))
def digI32 : List (RustM crc32.Digest) :=
  pairs.map (fun (p, i) => crc32.Digest.new_with_initial (pol32 p) (inits32.getD i 0#u32))
def digI64 : List (RustM crc64.Digest) :=
  pairs.map (fun (p, i) => crc64.Digest.new_with_initial (pol64 p) (inits64.getD i 0#u64))
def digN16 : List (RustM crc16.Digest) := (List.range 4).map (fun p => crc16.Digest.new (pol16 p))
def digN32 : List (RustM crc32.Digest) := (List.range 4).map (fun p => crc32.Digest.new (pol32 p))
def digN64 : List (RustM crc64.Digest) := (List.range 4).map (fun p => crc64.Digest.new (pol64 p))

end RSGBGold.Crc.Reflected

namespace Benchmark.V2.Crc.Reflected.Gold
open RSGBGold.Crc.Reflected

/-! ## `make_table` -/

/-- Every entry of the generated tables (eight polynomials) is `step⁸(i)`. -/
def gold_tables_model : Prop :=
  (∀ k < NPOLY, tab16 k ⦃ t => ∀ i < 256, (t.val[i]!).val = step8 (pol16 k).val i ⦄) ∧
  (∀ k < NPOLY, tab32 k ⦃ t => ∀ i < 256, (t.val[i]!).val = step8 (pol32 k).val i ⦄) ∧
  (∀ k < NPOLY, tab64 k ⦃ t => ∀ i < 256, (t.val[i]!).val = step8 (pol64 k).val i ⦄)

/-- Arbitrary polynomials (sampled sparsely: building a table is slow). -/
def gold_table_any (p16 : Std.U16) (p32 : Std.U32) (p64 : Std.U64) (i g : Std.U8) : Prop :=
  g.val % 64 = 0 →
    util.make_table_crc16 p16 ⦃ t => (t.val[i.val]!).val = step8 p16.val i.val ⦄ ∧
    util.make_table_crc32 p32 ⦃ t => (t.val[i.val]!).val = step8 p32.val i.val ⦄ ∧
    util.make_table_crc64 p64 ⦃ t => (t.val[i.val]!).val = step8 p64.val i.val ⦄

/-- The exported constants are the catalogue polynomials and the precomputed
tables used by the checksum functions are `make_table` of them. -/
def gold_constants : Prop :=
  crc16.X25 = 0x8408#u16 ∧ crc16.USB = 0xA001#u16 ∧ crc32.IEEE = 0xEDB88320#u32 ∧
  crc32.CASTAGNOLI = 0x82F63B78#u32 ∧ crc32.KOOPMAN = 0xEB31D82E#u32 ∧
  crc64.ECMA = 0xC96C5795D7870F42#u64 ∧ crc64.ISO = 0xD800000000000000#u64

def gold_precomputed_tables : Prop :=
  tab16 0 = ok crc16.X25_TABLE ∧ tab16 1 = ok crc16.USB_TABLE ∧
  tab32 0 = ok crc32.IEEE_TABLE ∧ tab32 1 = ok crc32.CASTAGNOLI_TABLE ∧ tab32 2 = ok crc32.KOOPMAN_TABLE ∧
  tab64 0 = ok crc64.ECMA_TABLE ∧ tab64 1 = ok crc64.ISO_TABLE

/-! ## `update` against the bitwise model (any start value) -/

def gold_update16_model (v : Std.U16) (k : Std.U8) (bs : List Std.U8) : Prop :=
  upd16 v k.val bs ⦃ r => r.val = model 16 (pol16 k.val).val v.val bs ⦄
def gold_update32_model (v : Std.U32) (k : Std.U8) (bs : List Std.U8) : Prop :=
  upd32 v k.val bs ⦃ r => r.val = model 32 (pol32 k.val).val v.val bs ⦄
def gold_update64_model (v : Std.U64) (k : Std.U8) (bs : List Std.U8) : Prop :=
  upd64 v k.val bs ⦃ r => r.val = model 64 (pol64 k.val).val v.val bs ⦄

/-- `update` with a table that is not a CRC table still follows the table-driven
recurrence (it only reads `table[(value ^ byte) & 0xff]`). -/
def gold_update32_any_table (v : Std.U32) (t : Std.Array Std.U32 256#usize) (bs : List Std.U8) : Prop :=
  crc32.update v t (toSlice bs) ⦃ r => r.val =
    (bs.foldl (fun (x : Nat) (b : Std.U8) => (t.val[(x ^^^ b.val) % 256]!).val ^^^ (x / 256)) (v.val ^^^ ones 32))
      ^^^ ones 32 ⦄

/-! ## `update` continues a CRC: incremental = one-shot -/

def gold_update16_concat (v : Std.U16) (k : Std.U8) (a b : List Std.U8) : Prop :=
  (do let x ← upd16 v k.val a; upd16 x k.val b) = upd16 v k.val (a ++ b)
def gold_update32_concat (v : Std.U32) (k : Std.U8) (a b : List Std.U8) : Prop :=
  (do let x ← upd32 v k.val a; upd32 x k.val b) = upd32 v k.val (a ++ b)
def gold_update64_concat (v : Std.U64) (k : Std.U8) (a b : List Std.U8) : Prop :=
  (do let x ← upd64 v k.val a; upd64 x k.val b) = upd64 v k.val (a ++ b)

/-- Appending the little-endian CRC of a message gives a residue that depends
only on the polynomial (not on the message or the start value). -/
def gold_residue16 (v : Std.U16) (k : Std.U8) (bs : List Std.U8) : Prop :=
  (do let c ← upd16 v k.val bs; upd16 v k.val (bs ++ leBytes 16 c.val)) = upd16 0#u16 k.val (leBytes 16 0)
def gold_residue32 (v : Std.U32) (k : Std.U8) (bs : List Std.U8) : Prop :=
  (do let c ← upd32 v k.val bs; upd32 v k.val (bs ++ leBytes 32 c.val)) = upd32 0#u32 k.val (leBytes 32 0)
def gold_residue64 (v : Std.U64) (k : Std.U8) (bs : List Std.U8) : Prop :=
  (do let c ← upd64 v k.val bs; upd64 v k.val (bs ++ leBytes 64 c.val)) = upd64 0#u64 k.val (leBytes 64 0)

/-! ## Catalogue checksums -/

def gold_x25 (bs : List Std.U8) : Prop :=
  crc16.checksum_x25 (toSlice bs) ⦃ r => r.val = model 16 0x8408 0 bs ⦄
def gold_usb (bs : List Std.U8) : Prop :=
  crc16.checksum_usb (toSlice bs) ⦃ r => r.val = model 16 0xA001 0 bs ⦄
def gold_ieee (bs : List Std.U8) : Prop :=
  crc32.checksum_ieee (toSlice bs) ⦃ r => r.val = model 32 0xEDB88320 0 bs ⦄
def gold_castagnoli (bs : List Std.U8) : Prop :=
  crc32.checksum_castagnoli (toSlice bs) ⦃ r => r.val = model 32 0x82F63B78 0 bs ⦄
def gold_koopman (bs : List Std.U8) : Prop :=
  crc32.checksum_koopman (toSlice bs) ⦃ r => r.val = model 32 0xEB31D82E 0 bs ⦄
def gold_ecma (bs : List Std.U8) : Prop :=
  crc64.checksum_ecma (toSlice bs) ⦃ r => r.val = model 64 0xC96C5795D7870F42 0 bs ⦄
def gold_iso (bs : List Std.U8) : Prop :=
  crc64.checksum_iso (toSlice bs) ⦃ r => r.val = model 64 0xD800000000000000 0 bs ⦄

/-- Documented check values on `"123456789"`. -/
def gold_check_values : Prop :=
  crc16.checksum_x25 (toSlice check) = ok 0x906E#u16 ∧
  crc16.checksum_usb (toSlice check) = ok 0xB4C8#u16 ∧
  crc32.checksum_ieee (toSlice check) = ok 0xCBF43926#u32 ∧
  crc32.checksum_castagnoli (toSlice check) = ok 0xE3069283#u32 ∧
  crc32.checksum_koopman (toSlice check) = ok 0x2D3DD0AE#u32 ∧
  crc64.checksum_ecma (toSlice check) = ok 0x995DC9BBDF1939FA#u64 ∧
  crc64.checksum_iso (toSlice check) = ok 0xB90956C775A41001#u64

/-! ## `Digest` (stateful, model-based) -/

def gold_digest16 (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) : Prop :=
  let j := k.val % 12; let (p, i) := pairs.getD j (0, 0); let init := (inits16.getD i 0#u16).val
  (do let d ← digI16.getD j (fail .panic); ops16 d ops) ⦃ r => r = modelOps 16 (pol16 p).val init init ops ⦄
def gold_digest32 (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) : Prop :=
  let j := k.val % 12; let (p, i) := pairs.getD j (0, 0); let init := (inits32.getD i 0#u32).val
  (do let d ← digI32.getD j (fail .panic); ops32 d ops) ⦃ r => r = modelOps 32 (pol32 p).val init init ops ⦄
def gold_digest64 (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) : Prop :=
  let j := k.val % 12; let (p, i) := pairs.getD j (0, 0); let init := (inits64.getD i 0#u64).val
  (do let d ← digI64.getD j (fail .panic); ops64 d ops) ⦃ r => r = modelOps 64 (pol64 p).val init init ops ⦄

def gold_digest_new (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) : Prop :=
  let p := k.val % 4
  (do let d ← digN16.getD p (fail .panic); ops16 d ops) ⦃ r => r = modelOps 16 (pol16 p).val 0 0 ops ⦄ ∧
  (do let d ← digN32.getD p (fail .panic); ops32 d ops) ⦃ r => r = modelOps 32 (pol32 p).val 0 0 ops ⦄ ∧
  (do let d ← digN64.getD p (fail .panic); ops64 d ops) ⦃ r => r = modelOps 64 (pol64 p).val 0 0 ops ⦄

/-- Arbitrary initial values (sparsely sampled: `new_with_initial` builds a table). -/
def gold_digest_any_initial (p : Std.U32) (i : Std.U32) (g : Std.U8) (ops : List (Std.U8 × List Std.U8)) : Prop :=
  g.val % 32 = 0 →
    (do let d ← crc32.Digest.new_with_initial p i; ops32 d ops) ⦃ r => r = modelOps 32 p.val i.val i.val ops ⦄

/-! Differential-testing probes. -/

def diff_tables (k : Std.U8) := (tab16 k.val, tab32 k.val, tab64 k.val)
def diff_update16 (v : Std.U16) (k : Std.U8) (bs : List Std.U8) := upd16 v k.val bs
def diff_update32 (v : Std.U32) (k : Std.U8) (bs : List Std.U8) := upd32 v k.val bs
def diff_update64 (v : Std.U64) (k : Std.U8) (bs : List Std.U8) := upd64 v k.val bs
def diff_cat (bs : List Std.U8) :=
  (crc16.checksum_x25 (toSlice bs), crc16.checksum_usb (toSlice bs), crc32.checksum_ieee (toSlice bs),
   crc32.checksum_castagnoli (toSlice bs), crc32.checksum_koopman (toSlice bs),
   crc64.checksum_ecma (toSlice bs), crc64.checksum_iso (toSlice bs))
def diff_consts (u : Std.U8) :=
  (crc16.X25, crc16.USB, crc32.IEEE, crc32.CASTAGNOLI, crc32.KOOPMAN, crc64.ECMA, crc64.ISO)
def diff_digest16 (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) :=
  (do let d ← digI16.getD (k.val % 12) (fail .panic); ops16 d ops)
def diff_digest32 (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) :=
  (do let d ← digI32.getD (k.val % 12) (fail .panic); ops32 d ops)
def diff_digest64 (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) :=
  (do let d ← digI64.getD (k.val % 12) (fail .panic); ops64 d ops)
def diff_digest_new (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) :=
  ((do let d ← digN16.getD (k.val % 4) (fail .panic); ops16 d ops),
   (do let d ← digN32.getD (k.val % 4) (fail .panic); ops32 d ops),
   (do let d ← digN64.getD (k.val % 4) (fail .panic); ops64 d ops))

end Benchmark.V2.Crc.Reflected.Gold
