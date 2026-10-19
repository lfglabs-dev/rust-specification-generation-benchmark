import Benchmark.V2.Prelude
import Adler32Rolling.Extraction

/-! Hidden gold specification for target `adler32/rolling`.

API: `adler32::RollingAdler32` (crate `adler32` 1.2.0): `new`, `from_value`,
`from_buffer`, `hash`, `update`, `update_buffer`, `remove` (the `&mut self`
state is threaded functionally).

Contract. The hash is the Adler-32 checksum (RFC 1950): with `BASE = 65521`,
`A = 1 + Σ dᵢ`, `B = Σ_{i=1..n} (1 + d₁ + … + dᵢ)` (both mod `BASE`) and
`hash = B·2¹⁶ + A`. A context created by `from_value(h)` continues the checksum
`h` (its halves are the running `A`/`B`; `hash()` returns `h` back); feeding
bytes extends the checksummed stream (`update` = one byte, `update_buffer` =
many, incremental = one-shot, including buffers longer than the 5552-byte
deferred-reduction blocks). `remove(size, byte)` forgets the oldest byte `byte`
of a window of `size` bytes: afterwards the hash is that of the window without
its first byte. No operation panics.

Note (real upstream defect): `remove` computes `(BASE - size)·byte` with
wrapping `u32` arithmetic, so it is only correct while that product does not
wrap below zero, i.e. for windows up to about `BASE + 256` bytes (and `size` is
truncated to `u32`). The gold spec states the remove contract on
`size ≤ BASE + 256` and only totality/range beyond. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM adler32 RSGB

namespace RSGBGold.Adler32.Rolling

def M : Nat := 65521

def toSlice (l : List Std.U8) : Slice Std.U8 :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

/-- Unreduced running sums continuing from `(a, b)`. -/
def sums (a b : Nat) (l : List Std.U8) : Nat × Nat :=
  l.foldl (fun (p : Nat × Nat) x => (p.1 + x.val, p.2 + p.1 + x.val)) (a, b)

/-- Adler-32 continuing from the halves `(a, b)` of a previous checksum. -/
def adlerFrom (a b : Nat) (l : List Std.U8) : Nat :=
  let p := sums a b l
  (p.2 % M) * 65536 + p.1 % M

/-- Adler-32 of a whole stream. -/
def adler (l : List Std.U8) : Nat := adlerFrom 1 0 l

def lo (s : Std.U32) : Nat := s.val % 65536
def hi (s : Std.U32) : Nat := s.val / 65536

/-- Both halves of a hash are reduced residues. -/
abbrev reduced (h : Nat) : Prop := h % 65536 < M ∧ h / 65536 < M

/-- Model of `remove(size, byte)` on halves `(a, b)`. -/
def removeModel (a b size x : Nat) : Nat :=
  let a' := ((a : Int) - x) % (M : Int)
  let b' := ((b : Int) - 1 - (size : Int) * x) % (M : Int)
  b'.toNat * 65536 + a'.toNat

def fromBuf (l : List Std.U8) : RustM Std.U32 := do
  let h ← RollingAdler32.from_buffer (toSlice l); RollingAdler32.hash h

def updBuf (s : Std.U32) (l : List Std.U8) : RustM Std.U32 := do
  let h ← RollingAdler32.from_value s
  let h ← RollingAdler32.update_buffer h (toSlice l)
  RollingAdler32.hash h

def upd (s : Std.U32) (x : Std.U8) : RustM Std.U32 := do
  let h ← RollingAdler32.from_value s
  let h ← RollingAdler32.update h x
  RollingAdler32.hash h

def updEach (h : RollingAdler32) : List Std.U8 → RustM RollingAdler32
  | [] => ok h
  | x :: l => do let h ← RollingAdler32.update h x; updEach h l

def rem (s : Std.U32) (size : Std.Usize) (x : Std.U8) : RustM Std.U32 := do
  let h ← RollingAdler32.from_value s
  let h ← RollingAdler32.remove h size x
  RollingAdler32.hash h

/-- Slide a window of `w` bytes over `ins`: remove the oldest byte, add the new one. -/
def slide (h : RollingAdler32) (w : Nat) : List Std.U8 → List Std.U8 → RustM RollingAdler32
  | _, [] => ok h
  | win, y :: ins => do
    let h ← RollingAdler32.remove h (mkU .Usize w) (win.headD 0#u8)
    let h ← RollingAdler32.update h y
    slide h w (win.drop 1 ++ [y]) ins

def str (s : String) : List Std.U8 := s.toUTF8.toList.map (fun b => mkU .U8 b.toNat)

/-- A valid checksum state (both halves `< BASE`) derived from an arbitrary `u32`. -/
def valid (s : Std.U32) : Std.U32 := mkU .U32 ((hi s % M) * 65536 + lo s % M)

/-- A long buffer of `n` bytes obtained by cycling `pat` (or `0xFF` if empty). -/
def cyc (pat : List Std.U8) (n : Nat) : List Std.U8 :=
  let p := if pat = [] then [255#u8] else pat
  (List.range n).map (fun i => p.getD (i % p.length) 0#u8)

/-- Mostly-`0xFF` pattern (worst case for the deferred reduction). -/
def heavy (pat : List Std.U8) : List Std.U8 := pat.map (fun x => if x.val < 32 then x else 255#u8)

/-- Lengths around the multiples of the 5552-byte block (and of 16). -/
def longLen (k : Std.U8) : Nat :=
  let base := [5552, 5552, 5568, 5536, 11104][k.val % 5]!
  base + (k.val / 5) % 40 - 20

/-- Long inputs are expensive to evaluate: only about one sample in 40 uses one. -/
abbrev gate (g : Std.U8) : Prop := g.val % 40 = 13

def gateB (g : Std.U8) : Bool := g.val % 40 = 13

/-- Worst case for the deferred reduction: `A` close to its maximum. -/
def highA (s : Std.U32) : Std.U32 := mkU .U32 ((hi s) * 65536 + (65535 - lo s % 1024))

end RSGBGold.Adler32.Rolling

namespace Benchmark.V2.Adler32.Rolling.Gold
open RSGBGold.Adler32.Rolling

/-! ## Construction and readout -/

/-- A fresh context has hash 1 (the Adler-32 of the empty stream). -/
def gold_new_hash : Prop :=
  (do let h ← RollingAdler32.new; RollingAdler32.hash h) = ok 1#u32 ∧
  fromBuf [] = ok 1#u32

/-- `from_value(h).hash() = h` for every `u32`. -/
def gold_from_value_hash (s : Std.U32) : Prop :=
  (do let h ← RollingAdler32.from_value s; RollingAdler32.hash h) = ok s

/-- `new()` is `from_value(1)`: they behave identically on any input. -/
def gold_new_is_from_value_1 (l : List Std.U8) : Prop :=
  (do let h ← RollingAdler32.new; let h ← RollingAdler32.update_buffer h (toSlice l); RollingAdler32.hash h)
    = updBuf 1#u32 l

/-! ## Exact Adler-32 values -/

def gold_check_vectors : Prop :=
  fromBuf (str "a") = ok 0x00620062#u32 ∧
  fromBuf (str "abc") = ok 0x024d0127#u32 ∧
  fromBuf (str "message digest") = ok 0x29750586#u32 ∧
  fromBuf (str "Wikipedia") = ok 0x11E60398#u32 ∧
  fromBuf (str "abcdefghijklmnopqrstuvwxyz") = ok 0x90860b20#u32 ∧
  fromBuf (List.replicate 1024 0#u8) = ok 0x04000001#u32

/-- `from_buffer` returns the Adler-32 checksum of the buffer. -/
def gold_from_buffer (l : List Std.U8) : Prop :=
  fromBuf l ⦃ r => r.val = adler l ⦄

/-- Short buffers (all of the 0/1/<16 byte fast paths). -/
def gold_from_buffer_short (l : List Std.U8) (k : Std.U8) : Prop :=
  fromBuf (l.take (k.val % 17)) ⦃ r => r.val = adler (l.take (k.val % 17)) ⦄

/-- Long buffers, around multiples of the 5552-byte reduction block, worst-case bytes. -/
def gold_from_buffer_long (pat : List Std.U8) (k g : Std.U8) : Prop :=
  gate g → fromBuf (cyc (heavy pat) (longLen k)) ⦃ r => r.val = adler (cyc (heavy pat) (longLen k)) ⦄

/-- `update_buffer` continues any checksum given to `from_value` (non-empty buffers). -/
def gold_update_buffer_continues (s : Std.U32) (l : List Std.U8) : Prop :=
  l ≠ [] → updBuf s l ⦃ r => r.val = adlerFrom (lo s) (hi s) l ⦄

/-- … also for a valid checksum and any buffer, including the empty one (no-op). -/
def gold_update_buffer_valid (s : Std.U32) (l : List Std.U8) : Prop :=
  updBuf (valid s) l ⦃ r => r.val = adlerFrom (lo (valid s)) (hi (valid s)) l ⦄

def gold_update_buffer_empty (s : Std.U32) : Prop :=
  updBuf (valid s) [] = ok (valid s)

/-- Long all-`0xFF` buffers continuing from a state with a large `A` (any `B`): the
worst case for the 32-bit deferred reduction. -/
def gold_update_buffer_long (s : Std.U32) (k g : Std.U8) : Prop :=
  gate g → updBuf (highA s) (List.replicate (longLen k) 255#u8)
    ⦃ r => r.val = adlerFrom (lo (highA s)) (hi (highA s)) (List.replicate (longLen k) 255#u8) ⦄

/-- Short buffers whose running `A` sum lands exactly on / just past the modulus. -/
def gold_update_buffer_modulus_edge (l : List Std.U8) (d : Std.U8) (b : Std.U16) : Prop :=
  2 ≤ l.length → l.length < 16 →
    let a := M - (l.map (·.val)).sum + d.val % 8 - 4
    let s := mkU .U32 ((b.val % M) * 65536 + a)
    updBuf s l ⦃ r => r.val = adlerFrom a (b.val % M) l ∧ reduced r.val ⦄

/-- `update(byte)` appends one byte to the stream, from any state. -/
def gold_update (s : Std.U32) (x : Std.U8) : Prop :=
  upd s x ⦃ r => r.val = adlerFrom (lo s) (hi s) [x] ⦄

/-- The hash after any `update`/`update_buffer` has both halves reduced mod 65521. -/
def gold_reduced (s : Std.U32) (l : List Std.U8) (x : Std.U8) : Prop :=
  updBuf s (x :: l) ⦃ r => reduced r.val ⦄ ∧ upd s x ⦃ r => reduced r.val ⦄

/-! ## Incremental = one-shot -/

def gold_incremental (s : Std.U32) (a b : List Std.U8) : Prop :=
  (do let h ← RollingAdler32.from_value (valid s)
      let h ← RollingAdler32.update_buffer h (toSlice a)
      let h ← RollingAdler32.update_buffer h (toSlice b)
      RollingAdler32.hash h) = updBuf (valid s) (a ++ b)

/-- Byte-wise `update` agrees with `update_buffer`. -/
def gold_update_each (s : Std.U32) (l : List Std.U8) : Prop :=
  (do let h ← RollingAdler32.from_value (valid s); let h ← updEach h l; RollingAdler32.hash h)
    = updBuf (valid s) l

/-- Resuming from a published checksum (`from_value(hash)`) equals continuing the stream. -/
def gold_resume (a b : List Std.U8) : Prop :=
  (do let h ← fromBuf a; updBuf h b) = fromBuf (a ++ b)

/-- Resumption across a long first part (crosses the 5552-byte blocks). -/
def gold_resume_long (pat b : List Std.U8) (k g : Std.U8) : Prop :=
  gate g → (do let h ← fromBuf (cyc pat (longLen k)); updBuf h b) = fromBuf (cyc pat (longLen k) ++ b)

/-! ## Rolling `remove` -/

/-- Removing the first byte of a window gives the hash of the rest of the window. -/
def gold_remove_first (x : Std.U8) (w : List Std.U8) : Prop :=
  (do let h ← RollingAdler32.from_buffer (toSlice (x :: w))
      let h ← RollingAdler32.remove h (mkU .Usize (w.length + 1)) x
      RollingAdler32.hash h) = fromBuf w

/-- Sliding a fixed-size window: after every step the hash is that of the current window. -/
def gold_rolling_window (w ins : List Std.U8) : Prop :=
  w ≠ [] →
    (do let h ← RollingAdler32.from_buffer (toSlice w)
        let h ← slide h w.length w ins
        RollingAdler32.hash h) = fromBuf ((w ++ ins).drop ins.length)

/-- Exact effect of `remove` on any state, for windows up to `BASE + 256` bytes. -/
def gold_remove_model (s : Std.U32) (size : Std.U32) (x : Std.U8) : Prop :=
  let n := size.val % (M + 257)
  rem s (mkU .Usize n) x ⦃ r => r.val = removeModel (lo s) (hi s) n x.val ⦄

/-- Windows just above the modulus (e.g. 64 KiB) — where the unchecked formula overflowed. -/
def gold_remove_model_large (s : Std.U32) (d : Std.U8) (x : Std.U8) : Prop :=
  let n := M - 128 + d.val
  rem s (mkU .Usize n) x ⦃ r => r.val = removeModel (lo s) (hi s) n x.val ⦄

/-- `remove` never panics, for any size, and keeps both halves reduced. -/
def gold_remove_total (s : Std.U32) (size : Std.Usize) (x : Std.U8) : Prop :=
  rem s size x ⦃ r => reduced r.val ⦄

/-- `remove` undoes a prefix byte also after resuming from a checksum. -/
def gold_remove_after_resume (x : Std.U8) (w b : List Std.U8) : Prop :=
  (do let s ← fromBuf (x :: w)
      let h ← RollingAdler32.from_value s
      let h ← RollingAdler32.update_buffer h (toSlice b)
      let h ← RollingAdler32.remove h (mkU .Usize (w.length + b.length + 1)) x
      RollingAdler32.hash h) = fromBuf (w ++ b)

/-! Differential-testing probes. -/

def diff_from_value (s : Std.U32) := do let h ← RollingAdler32.from_value s; RollingAdler32.hash h
def diff_from_buffer (l : List Std.U8) := fromBuf l
def diff_update_buffer (s : Std.U32) (l : List Std.U8) := updBuf s l
def diff_update_buffer_long (s : Std.U32) (pat : List Std.U8) (k g : Std.U8) :=
  updBuf (highA s) (if gateB g then cyc (heavy pat) (longLen k) else heavy pat)
def diff_update_buffer_edge (l : List Std.U8) (d : Std.U8) :=
  updBuf (mkU .U32 (M - (l.map (·.val)).sum + d.val % 8 - 4)) (l.take 15)
def diff_update (s : Std.U32) (x : Std.U8) := upd s x
def diff_remove (s : Std.U32) (size : Std.Usize) (x : Std.U8) := rem s size x
def diff_remove_small (s : Std.U32) (size : Std.U32) (x : Std.U8) := rem s (mkU .Usize (size.val % (M + 300))) x

end Benchmark.V2.Adler32.Rolling.Gold
