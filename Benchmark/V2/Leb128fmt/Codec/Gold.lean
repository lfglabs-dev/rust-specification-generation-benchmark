import Benchmark.V2.Prelude
import Leb128fmtCodec.Extraction

/-! Hidden gold specification for target `leb128fmt/codec`.

Array-based LEB128 encoders/decoders of `leb128fmt` for 32 and 64 bits, unsigned
and signed, minimal and fixed-width. Independent model: 7-bit groups of the
mathematical value (`Nat` / `Int` with floor division). Decoding accepts any
(also non-minimal) encoding that terminates within `max_len` bytes and whose value
fits the bit width; the bytes after the written length of a minimal encoding are
not specified. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM leb128fmt RSGB

namespace RSGBGold.Leb128fmt.Codec

/-- Minimal unsigned LEB128. -/
def uBytes : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, v => if v < 128 then [v] else (v % 128 + 128) :: uBytes fuel (v / 128)

def uEnc (v : Nat) : List Nat := uBytes 20 v

/-- Minimal signed LEB128. -/
def sBytes : Nat → Int → List Nat
  | 0, _ => []
  | fuel + 1, v =>
    let b := (v % 128).toNat
    let v' := v / 128
    if (v' = 0 ∧ b < 64) ∨ (v' = -1 ∧ 64 ≤ b) then [b] else (b + 128) :: sBytes fuel v'

def sEnc (v : Int) : List Nat := sBytes 20 v

/-- Fixed-width encoding: all `L` groups, continuation bit on all but the last. -/
def fixedBytes (v : Int) (L : Nat) : List Nat :=
  (List.range L).map fun i =>
    let g := (v / (2 ^ (7 * i) : Nat) % 128).toNat
    if i + 1 < L then g + 128 else g

/-- Index of the first terminating byte (`< 0x80`) among the first `L` bytes. -/
def termIdx (l : List Nat) (L : Nat) : Option Nat :=
  ((List.range L).filter fun i => decide ((l.getD i 255) < 128)).head?

def rawVal (l : List Nat) (j : Nat) : Nat :=
  ((List.range (j + 1)).map fun i => (l.getD i 0 % 128) * 2 ^ (7 * i)).sum

/-- Unsigned decode model: value and number of bytes read. -/
def uDec (l : List Nat) (B L : Nat) : Option (Nat × Nat) :=
  match termIdx l L with
  | none => none
  | some j => let v := rawVal l j; if v < 2 ^ B then some (v, j + 1) else none

/-- Signed decode model (sign bit = bit 6 of the last byte). -/
def sDec (l : List Nat) (B L : Nat) : Option (Int × Nat) :=
  match termIdx l L with
  | none => none
  | some j =>
    let raw : Int := rawVal l j
    let v : Int := if l.getD j 0 ≥ 64 then raw - (2 ^ (7 * (j + 1)) : Nat) else raw
    if -((2 ^ (B - 1) : Nat) : Int) ≤ v ∧ v < ((2 ^ (B - 1) : Nat) : Int) then some (v, j + 1) else none

def bs {n : Std.Usize} (a : Std.Array Std.U8 n) : List Nat := a.val.map (·.val)

def toArr (l : List Nat) (n : Std.Usize) : Std.Array Std.U8 n :=
  let l' := ((l.map fun x => mkU .U8 x) ++ List.replicate n.val 0#u8).take n.val
  if h : l'.length = n.val then ⟨l', h⟩ else ⟨List.replicate n.val 0#u8, by simp⟩

/-- Checks for the minimal encoders. -/
def encOkU {n : Std.Usize} (r : core.option.Option (Std.Array Std.U8 n × Std.Usize)) (v : Nat) : Bool :=
  match r with
  | .Some (a, k) => k.val == (uEnc v).length && (bs a).take k.val == uEnc v
  | .None => false

def encOkS {n : Std.Usize} (r : core.option.Option (Std.Array Std.U8 n × Std.Usize)) (v : Int) : Bool :=
  match r with
  | .Some (a, k) => k.val == (sEnc v).length && (bs a).take k.val == sEnc v
  | .None => false

def fixOk {n : Std.Usize} (r : core.option.Option (Std.Array Std.U8 n)) (v : Int) : Bool :=
  match r with
  | .Some a => bs a == fixedBytes v n.val
  | .None => false

def decOkU {α} (r : core.option.Option (α × Std.Usize)) (val : α → Nat) (m : Option (Nat × Nat)) : Bool :=
  match r, m with
  | .Some (x, k), some (v, j) => val x == v && k.val == j
  | .None, none => true
  | _, _ => false

def decOkS {α} (r : core.option.Option (α × Std.Usize)) (val : α → Int) (m : Option (Int × Nat)) : Bool :=
  match r, m with
  | .Some (x, k), some (v, j) => val x == v && k.val == j
  | .None, none => true
  | _, _ => false

/-- Decoder inputs: raw arrays, or a (minimal / fixed / padded) encoding of a value
with optional tampering of one byte. -/
def decIn (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) (signed : Bool) (n : Std.Usize) :
    Std.Array Std.U8 n :=
  let sv : Int :=
    if signed then (if n.val == 5 then (mkI .I32 v.val).val else (mkI .I64 v.val).val)
    else (if n.val == 5 then v.val % 2 ^ 32 else v.val)
  let base : List Nat := match k.val % 5 with
    | 0 => bs a
    | 1 => (if signed then sEnc sv else uEnc sv.toNat) ++ bs a
    | 2 => fixedBytes sv n.val
    | 3 => (if signed then sEnc sv else uEnc sv.toNat).dropLast ++ [128] ++ bs a
    | _ => (List.replicate (k.val / 5 % n.val) 128) ++ [k.val / 5 % 128] ++ bs a
  let tampered := if k.val / 64 == 1 then base.set (n.val - 1) ((bs a).headD 0) else base
  toArr tampered n

end RSGBGold.Leb128fmt.Codec

namespace Benchmark.V2.Leb128fmt.Codec.Gold
open RSGBGold.Leb128fmt.Codec

/-! ## Unsigned -/

def gold_encode_u32 (v : Std.U32) : Prop := encode_u32 v ⦃ r => encOkU r v.val = true ⦄
def gold_encode_u64 (v : Std.U64) : Prop := encode_u64 v ⦃ r => encOkU r v.val = true ⦄
def gold_encode_fixed_u32 (v : Std.U32) : Prop := encode_fixed_u32 v ⦃ r => fixOk r v.val = true ⦄
def gold_encode_fixed_u64 (v : Std.U64) : Prop := encode_fixed_u64 v ⦃ r => fixOk r v.val = true ⦄

def gold_decode_u32 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) : Prop :=
  decode_u32 (decIn a v k false 5#usize) ⦃ r =>
    decOkU r (fun (x : Std.U32) => x.val) (uDec (bs (decIn a v k false 5#usize)) 32 5) = true ⦄

def gold_decode_u64 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) : Prop :=
  decode_u64 (decIn a v k false 10#usize) ⦃ r =>
    decOkU r (fun (x : Std.U64) => x.val) (uDec (bs (decIn a v k false 10#usize)) 64 10) = true ⦄

def gold_roundtrip_u32 (v : Std.U32) (pad : Std.Array Std.U8 10#usize) : Prop :=
  (do let r ← encode_u32 v
      match r with
      | .Some (a, k) => decode_u32 (toArr ((bs a).take k.val ++ bs pad) 5#usize)
      | .None => ok .None) = ok (.Some (v, mkU .Usize (uEnc v.val).length))

def gold_roundtrip_u64 (v : Std.U64) (pad : Std.Array Std.U8 10#usize) : Prop :=
  (do let r ← encode_u64 v
      match r with
      | .Some (a, k) => decode_u64 (toArr ((bs a).take k.val ++ bs pad) 10#usize)
      | .None => ok .None) = ok (.Some (v, mkU .Usize (uEnc v.val).length))

def gold_roundtrip_fixed_u32 (v : Std.U32) : Prop :=
  (do let r ← encode_fixed_u32 v
      match r with | .Some a => decode_u32 a | .None => ok .None) = ok (.Some (v, 5#usize))

def gold_roundtrip_fixed_u64 (v : Std.U64) : Prop :=
  (do let r ← encode_fixed_u64 v
      match r with | .Some a => decode_u64 a | .None => ok .None) = ok (.Some (v, 10#usize))

/-! ## Signed -/

def gold_encode_s32 (v : Std.I32) : Prop := encode_s32 v ⦃ r => encOkS r v.val = true ⦄
def gold_encode_s64 (v : Std.I64) : Prop := encode_s64 v ⦃ r => encOkS r v.val = true ⦄
def gold_encode_fixed_s32 (v : Std.I32) : Prop := encode_fixed_s32 v ⦃ r => fixOk r v.val = true ⦄
def gold_encode_fixed_s64 (v : Std.I64) : Prop := encode_fixed_s64 v ⦃ r => fixOk r v.val = true ⦄

def gold_decode_s32 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) : Prop :=
  decode_s32 (decIn a v k true 5#usize) ⦃ r =>
    decOkS r (fun (x : Std.I32) => x.val) (sDec (bs (decIn a v k true 5#usize)) 32 5) = true ⦄

def gold_decode_s64 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) : Prop :=
  decode_s64 (decIn a v k true 10#usize) ⦃ r =>
    decOkS r (fun (x : Std.I64) => x.val) (sDec (bs (decIn a v k true 10#usize)) 64 10) = true ⦄

def gold_roundtrip_s32 (v : Std.I32) (pad : Std.Array Std.U8 10#usize) : Prop :=
  (do let r ← encode_s32 v
      match r with
      | .Some (a, k) => decode_s32 (toArr ((bs a).take k.val ++ bs pad) 5#usize)
      | .None => ok .None) = ok (.Some (v, mkU .Usize (sEnc v.val).length))

def gold_roundtrip_s64 (v : Std.I64) (pad : Std.Array Std.U8 10#usize) : Prop :=
  (do let r ← encode_s64 v
      match r with
      | .Some (a, k) => decode_s64 (toArr ((bs a).take k.val ++ bs pad) 10#usize)
      | .None => ok .None) = ok (.Some (v, mkU .Usize (sEnc v.val).length))

def gold_roundtrip_fixed_s32 (v : Std.I32) : Prop :=
  (do let r ← encode_fixed_s32 v
      match r with | .Some a => decode_s32 a | .None => ok .None) = ok (.Some (v, 5#usize))

def gold_roundtrip_fixed_s64 (v : Std.I64) : Prop :=
  (do let r ← encode_fixed_s64 v
      match r with | .Some a => decode_s64 a | .None => ok .None) = ok (.Some (v, 10#usize))

/-! ## Differential-testing probes (minimal encoders: only the written prefix) -/

def diff_encode_u32 (v : Std.U32) := do
  let r ← encode_u32 v; ok (match r with | .Some (a, k) => some ((bs a).take k.val, k) | .None => none)
def diff_encode_u64 (v : Std.U64) := do
  let r ← encode_u64 v; ok (match r with | .Some (a, k) => some ((bs a).take k.val, k) | .None => none)
def diff_encode_s32 (v : Std.I32) := do
  let r ← encode_s32 v; ok (match r with | .Some (a, k) => some ((bs a).take k.val, k) | .None => none)
def diff_encode_s64 (v : Std.I64) := do
  let r ← encode_s64 v; ok (match r with | .Some (a, k) => some ((bs a).take k.val, k) | .None => none)
def diff_encode_fixed_u32 (v : Std.U32) := encode_fixed_u32 v
def diff_encode_fixed_u64 (v : Std.U64) := encode_fixed_u64 v
def diff_encode_fixed_s32 (v : Std.I32) := encode_fixed_s32 v
def diff_encode_fixed_s64 (v : Std.I64) := encode_fixed_s64 v
def diff_decode_u32 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) := decode_u32 (decIn a v k false 5#usize)
def diff_decode_u64 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) := decode_u64 (decIn a v k false 10#usize)
def diff_decode_s32 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) := decode_s32 (decIn a v k true 5#usize)
def diff_decode_s64 (a : Std.Array Std.U8 10#usize) (v : Std.U64) (k : Std.U8) := decode_s64 (decIn a v k true 10#usize)

end Benchmark.V2.Leb128fmt.Codec.Gold
