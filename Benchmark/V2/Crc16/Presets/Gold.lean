import Benchmark.V2.Prelude
import Crc16Presets.Extraction

/-! Hidden gold specification for target `crc16/presets`.

API: crate `crc16` 0.4 (blackbeam/rust-crc16): the generic `State<T: CrcType>`
(`new`, `update`, `get`, `calculate`, `Default::default`,
`core::hash::Hasher::{write, finish}`) and the `CrcType` implementations
(`init`, `update`, `get`) of the catalogue algorithms ARC, CRC-16/AUG-CCITT,
CRC-16/BUYPASS, CRC-16/CDMA2000, CRC-16/DECT-R, CRC-16/DNP, CRC-16/EN-13757,
CRC-16/MCRF4XX, CRC-16/T10-DIF, CRC-16/TELEDISK.

Contract. Each type `T` is the Rocksoft-model CRC-16 named by it, with the
parameters `(poly, init, refin, refout, xorout)` listed in the crate (and in
the CRC catalogue): `State::<T>::calculate(m)` is that CRC of `m`; its check
value on "123456789" is the documented `check`. A `State` accumulates the
message: after `new()` (= `default()`) and `update(m₁) … update(mₖ)`, `get()`
is the CRC of `m₁ ++ … ++ mₖ` and does not disturb the state (updating may
continue); `Hasher::write` = `update`, `Hasher::finish` = `get` zero-extended to
`u64`. The `CrcType` functions are the building blocks with
`calculate(m) = get(update(init(), m))` and `update` composes over
concatenation. The internal register value (`State::state`, `init()`, the value
threaded through `update`) is an implementation detail. Nothing panics. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM crc16 RSGB

namespace RSGBGold.Crc16.Presets

def toSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

structure Params where
  poly : Nat
  init : Nat
  refin : Bool
  refout : Bool
  xorout : Nat
  check : Nat

/-- The ten table-driven presets, in a fixed order. -/
def params : Nat → Params
  | 0 => ⟨0x8005, 0x0000, true, true, 0x0000, 0xbb3d⟩    -- ARC
  | 1 => ⟨0x1021, 0x1d0f, false, false, 0x0000, 0xe5cc⟩  -- AUG-CCITT
  | 2 => ⟨0x8005, 0x0000, false, false, 0x0000, 0xfee8⟩  -- BUYPASS
  | 3 => ⟨0xc867, 0xffff, false, false, 0x0000, 0x4c06⟩  -- CDMA2000
  | 4 => ⟨0x0589, 0x0000, false, false, 0x0001, 0x007e⟩  -- DECT-R
  | 5 => ⟨0x3d65, 0x0000, true, true, 0xffff, 0xea82⟩    -- DNP
  | 6 => ⟨0x3d65, 0x0000, false, false, 0xffff, 0xc2b7⟩  -- EN-13757
  | 7 => ⟨0x1021, 0xffff, true, true, 0x0000, 0x6f91⟩    -- MCRF4XX
  | 8 => ⟨0x8bb7, 0x0000, false, false, 0x0000, 0xd0db⟩  -- T10-DIF
  | _ => ⟨0xa097, 0x0000, false, false, 0x0000, 0x0fb3⟩  -- TELEDISK

def NP : Nat := 10

def withPreset {α : Type} (k : Nat) (f : {T : Type} → CrcType T → RustM α) : RustM α :=
  match k with
  | 0 => f ARC.Insts.Crc16CrcType
  | 1 => f AUG_CCITT.Insts.Crc16CrcType
  | 2 => f BUYPASS.Insts.Crc16CrcType
  | 3 => f CDMA2000.Insts.Crc16CrcType
  | 4 => f DECT_R.Insts.Crc16CrcType
  | 5 => f DNP.Insts.Crc16CrcType
  | 6 => f EN_13757.Insts.Crc16CrcType
  | 7 => f MCRF4XX.Insts.Crc16CrcType
  | 8 => f T10_DIF.Insts.Crc16CrcType
  | _ => f TELEDISK.Insts.Crc16CrcType

/-! Independent Rocksoft-model CRC-16 (bitwise, MSB-first register). -/

def rev (w x : Nat) : Nat := (List.range w).foldl (fun acc i => acc * 2 + (x / 2 ^ i) % 2) 0

def shift1 (poly r : Nat) : Nat :=
  if r / 0x8000 % 2 = 1 then ((r * 2) % 0x10000) ^^^ poly else (r * 2) % 0x10000

def feed (p : Params) (r : Nat) (b : Std.U8) : Nat :=
  let b' := if p.refin then rev 8 b.val else b.val
  Nat.iterate (shift1 p.poly) 8 (r ^^^ (b' * 256))

def crc (p : Params) (m : List Std.U8) : Nat :=
  let r := m.foldl (feed p) p.init
  (if p.refout then rev 16 r else r) ^^^ p.xorout

def check : List Std.U8 := [49, 50, 51, 52, 53, 54, 55, 56, 57].map (mkU .U8 ·)

/-! Operation scripts: `tag % 4` = 0 `update`, 1 record `get`, 2 `Hasher::write`,
3 record `Hasher::finish`; a final `get` is always recorded. -/

def modelOps (p : Params) : List Std.U8 → List (Std.U8 × List Std.U8) → List Nat
  | acc, [] => [crc p acc]
  | acc, (t, bs) :: rest =>
    match t.val % 4 with
    | 0 => modelOps p (acc ++ bs) rest
    | 2 => modelOps p (acc ++ bs) rest
    | _ => crc p acc :: modelOps p acc rest

def runOps {T : Type} (inst : CrcType T) (s : State T) : List (Std.U8 × List Std.U8) → RustM (List Nat)
  | [] => do let r ← State.get inst s; ok [r.val]
  | (t, bs) :: rest =>
    match t.val % 4 with
    | 0 => do let s ← State.update inst s (toSlice bs); runOps inst s rest
    | 2 => do let s ← State.Insts.CoreHashHasher.write inst s (toSlice bs); runOps inst s rest
    | 1 => do let r ← State.get inst s; let l ← runOps inst s rest; ok (r.val :: l)
    | _ => do let r ← State.Insts.CoreHashHasher.finish inst s; let l ← runOps inst s rest; ok (r.val :: l)

def calcP (k : Nat) (m : List Std.U8) : RustM Std.U16 :=
  withPreset k (fun inst => State.calculate inst (toSlice m))

/-- `get(update(init(), m))` through the `CrcType` functions. -/
def viaType (k : Nat) (m : List Std.U8) : RustM Std.U16 :=
  withPreset k (fun inst => do let i ← inst.init; let r ← inst.update i (toSlice m); inst.get r)

def viaTypeSplit (k : Nat) (a b : List Std.U8) : RustM Std.U16 :=
  withPreset k (fun inst => do
    let i ← inst.init; let r ← inst.update i (toSlice a); let r ← inst.update r (toSlice b); inst.get r)

def scripted (k : Nat) (ops : List (Std.U8 × List Std.U8)) : RustM (List Nat) :=
  withPreset k (fun inst => do let s ← State.new inst; runOps inst s ops)

def scriptedDefault (k : Nat) (ops : List (Std.U8 × List Std.U8)) : RustM (List Nat) :=
  withPreset k (fun inst => do let s ← State.Insts.CoreDefaultDefault.default inst; runOps inst s ops)

end RSGBGold.Crc16.Presets

namespace Benchmark.V2.Crc16.Presets.Gold
open RSGBGold.Crc16.Presets

/-- Every preset computes its catalogue CRC. -/
def gold_calculate (k : Std.U8) (m : List Std.U8) : Prop :=
  calcP (k.val % NP) m ⦃ r => r.val = crc (params (k.val % NP)) m ⦄

/-- Documented check values on "123456789". -/
def gold_check_values : Prop :=
  ∀ k < NP, calcP k check = ok (mkU .U16 (params k).check)

/-- Longer messages (beyond the default sampling lengths). -/
def gold_calculate_long (k : Std.U8) (a b c : List Std.U8) : Prop :=
  calcP (k.val % NP) (a ++ b ++ c ++ a ++ b ++ c) ⦃ r => r.val = crc (params (k.val % NP)) (a ++ b ++ c ++ a ++ b ++ c) ⦄

/-- `calculate` is assembled from the `CrcType` functions, and `update` composes. -/
def gold_type_functions (k : Std.U8) (a b : List Std.U8) : Prop :=
  viaType (k.val % NP) (a ++ b) = calcP (k.val % NP) (a ++ b) ∧
  viaTypeSplit (k.val % NP) a b = calcP (k.val % NP) (a ++ b)

/-- Stateful use: `new`, `update`/`Hasher::write` (incremental = one-shot),
`get`/`Hasher::finish` (non-destructive). -/
def gold_state (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) : Prop :=
  scripted (k.val % NP) ops ⦃ r => r = modelOps (params (k.val % NP)) [] ops ⦄

def gold_state_default (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) : Prop :=
  scriptedDefault (k.val % NP) ops ⦃ r => r = modelOps (params (k.val % NP)) [] ops ⦄

/-! Differential-testing probes. -/

def diff_calculate (k : Std.U8) (m : List Std.U8) := calcP (k.val % NP) m
def diff_all (m : List Std.U8) := (List.range NP).map (fun k => calcP k m)
def diff_state (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) := scripted (k.val % NP) ops
def diff_default (k : Std.U8) (ops : List (Std.U8 × List Std.U8)) := scriptedDefault (k.val % NP) ops
def diff_type (k : Std.U8) (a b : List Std.U8) := (viaType (k.val % NP) a, viaTypeSplit (k.val % NP) a b)

end Benchmark.V2.Crc16.Presets.Gold
