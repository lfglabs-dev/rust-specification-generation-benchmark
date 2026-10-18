import Benchmark.V2.Prelude
import CobsState.Extraction

/-! Hidden gold specification for target `cobs/state`.

The streaming COBS state machines of `cobs` (no output buffer inside):
`EncoderState::{default, push, finalize}` driven by the documented `PushResult`
protocol (the output buffer starts with one placeholder byte; `AddSingle b` appends
`b`; `ModifyFromStartAndSkip (i, v)` sets byte `i` to `v` and appends a placeholder;
`ModifyFromStartAndPushAndSkip (i, v, b)` sets byte `i`, appends `b`, then appends a
placeholder only if the encoding is not done; `finalize` gives `(i, v)` to store if
`i` is inside the buffer), `DecoderState::{default, feed}`, and the
`max_encoding_overhead` / `max_encoding_length` bounds.

Independent reference: textbook COBS encoding / decoding on lists. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM cobs RSGB

namespace RSGBGold.Cobs.State

/-! ### Reference COBS on `List Nat` -/

/-- Take the longest zero-free prefix of length at most `k`. -/
def takeRun : Nat → List Nat → List Nat × List Nat
  | 0, l => ([], l)
  | _, [] => ([], [])
  | k + 1, x :: l =>
    if x == 0 then ([], x :: l) else
    let (r, t) := takeRun k l
    (x :: r, t)

/-- Standard COBS encoding (no trailing sentinel). After a full 254-byte block that
ends the message no further code byte is emitted. -/
def encModel (l : List Nat) (afterFull : Bool := false) : List Nat :=
  if _h : l = [] then (if afterFull then [] else [1]) else
  let (r, t) := takeRun 254 l
  if r.length = 254 then
    255 :: r ++ (if _h2 : t.length < l.length then encModel t true else [])
  else
    match t with
    | [] => (r.length + 1) :: r
    | _ :: t' => (r.length + 1) :: r ++ (if _h2 : t'.length < l.length then encModel t' false else [])
termination_by l.length

/-- Standard COBS decoding of a zero-free frame (`none` if a block overruns the frame
or the frame contains a zero / is empty). -/
def decModel (l : List Nat) : Option (List Nat) :=
  match l with
  | [] => none
  | c :: rest =>
    if c == 0 then none else
    let n := c - 1
    if rest.length < n then none else
    let blk := rest.take n
    let tl := rest.drop n
    if blk.any (· == 0) then none else
    if tl = [] then some blk else
    if _h2 : tl.length < l.length then
      match decModel tl with
      | none => none
      | some d => some (blk ++ (if c == 255 then [] else [0]) ++ d)
    else none
termination_by l.length

def vals (l : List Std.U8) : List Nat := l.map (·.val)
def u8s (l : List Nat) : List Std.U8 := l.map (fun n => mkU .U8 n)

/-! ### Protocol drivers -/

def encSteps : enc.EncoderState → List Std.U8 → Array Std.U8 → RustM (Array Std.U8 × enc.EncoderState)
  | st, [], buf => ok (buf, st)
  | st, x :: rest, buf => do
    let (r, st') ← enc.EncoderState.push st x
    let buf' := match r with
      | .AddSingle b => buf.push b
      | .ModifyFromStartAndSkip (i, v) => (buf.setIfInBounds i.val v).push 0#u8
      | .ModifyFromStartAndPushAndSkip (i, v, b) =>
        let b2 := (buf.setIfInBounds i.val v).push b
        if rest.isEmpty then b2 else b2.push 0#u8
    encSteps st' rest buf'

/-- Encode a whole message with the streaming encoder, following the documented protocol. -/
def encRun (xs : List Std.U8) : RustM (List Nat) := do
  let st0 ← enc.EncoderState.Insts.CoreDefaultDefault.default
  let (buf, st) ← encSteps st0 xs #[0#u8]
  let (i, v) ← enc.EncoderState.finalize st
  ok (vals (buf.setIfInBounds i.val v).toList)

/-- Decoder events: byte `b` (`DataContinue b`) as `b`, `DataStart` 256, `DataComplete` 257,
`NoData` 258, `Err (InvalidFrame _)` 259, any other error 260. -/
def evCode (r : core.result.Result dec.DecodeResult dec.DecodeError) : Nat :=
  match r with
  | .Ok (.DataContinue b) => b.val
  | .Ok .DataStart => 256
  | .Ok .DataComplete => 257
  | .Ok .NoData => 258
  | .Err (.InvalidFrame _) => 259
  | .Err _ => 260

def decSteps : dec.DecoderState → List Std.U8 → RustM (List Nat × dec.DecoderState)
  | st, [] => ok ([], st)
  | st, x :: rest => do
    let (r, st') ← dec.DecoderState.feed st x
    let (evs, st'') ← decSteps st' rest
    ok (evCode r :: evs, st'')

def decRun (xs : List Std.U8) : RustM (List Nat × dec.DecoderState) := do
  let st0 ← dec.DecoderState.Insts.CoreDefaultDefault.default
  decSteps st0 xs

def isIdle (s : dec.DecoderState) : Bool := match s with | .Idle => true | _ => false

/-- Frames delivered by the documented consumer: `DataStart` clears the buffer,
`DataContinue b` appends, `DataComplete` delivers, an error discards. Returns
(delivered frames, number of errors). -/
def framesAux : List Nat → List Nat → List (List Nat) × Nat
  | [], _ => ([], 0)
  | e :: es, cur =>
    if e == 256 then framesAux es []
    else if e == 257 then let (fs, n) := framesAux es []; (cur :: fs, n)
    else if e == 258 then framesAux es cur
    else if e ≥ 259 then let (fs, n) := framesAux es []; (fs, n + 1)
    else framesAux es (cur ++ [e])

def frames (evs : List Nat) : List (List Nat) × Nat := framesAux evs []

/-! ### Input generators -/

def hmix (a : Nat) : Nat :=
  let z := (a * 0x9E3779B1 + 0x7F4A7C15) % 2^32
  let z := ((z ^^^ (z >>> 15)) * 0x2C1B3C6D) % 2^32
  z ^^^ (z >>> 13)

/-- Long messages (up to ~1100 bytes, often exactly around multiples of 254) with a
selectable density of zero bytes. -/
def longIn (x : List Std.U8) (n : Std.U16) (z : Std.U8) : List Std.U8 :=
  let len := match z.val % 4 with
    | 0 => n.val % 1100
    | 1 => (254 * (n.val % 5) + (z.val / 4) % 3) - 1
    | 2 => n.val % 600
    | _ => x.length
  let zf := match (z.val / 16) % 4 with | 0 => 0 | 1 => 3 | 2 => 30 | _ => 400
  (List.range len).map fun i =>
    let h := hmix (i + 7919 * n.val + 104729 * z.val)
    match x[i]? with
    | some b => if z.val % 4 == 3 then b else if h % 1000 < zf then 0#u8 else mkU .U8 (h % 255 + 1)
    | none => if h % 1000 < zf then 0#u8 else mkU .U8 (h % 255 + 1)

def msg (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) : List Std.U8 :=
  if b then x else longIn x n z

/-- A zero-free candidate frame: either garbage, or a valid encoding with one byte changed. -/
def frameIn (x : List Std.U8) (n : Std.U16) (z : Std.U8) (k v : Std.U8) : List Std.U8 :=
  let base := match z.val % 3 with
    | 0 => (msg x n z (n.val % 2 == 0)).filter (·.val != 0)
    | _ => u8s (encModel (vals (msg x n z (n.val % 2 == 0))))
  if base.isEmpty then base else
  if z.val % 3 == 2 then base else
  base.set (k.val * 7 % base.length) (mkU .U8 (v.val % 255 + 1))

def ovModel (n : Nat) : Nat := if n = 0 then 1 else (n + 253) / 254

/-- Expected decoder outcome for one frame + sentinel. -/
def outcomeOk (m : Option (List Nat)) (evs : List Nat) : Bool :=
  match m with
  | some m => frames evs == ([m], 0)
  | none => frames evs == ([], 1) && evs.getLast? == some 259

def mkDState (t i : Std.U8) : dec.DecoderState :=
  match t.val % 3 with | 0 => .Idle | 1 => .Grab i | _ => .GrabChain i

end RSGBGold.Cobs.State

namespace Benchmark.V2.Cobs.State.Gold
open RSGBGold.Cobs.State

/-! ## Bounds -/

def gold_overhead (n : Std.Usize) : Prop :=
  max_encoding_overhead n ⦃ r => r.val = ovModel n.val ⦄

def gold_length (n : Std.Usize) : Prop :=
  (n.val + ovModel n.val < 2^64 → max_encoding_length n ⦃ r => r.val = n.val + ovModel n.val ⦄) ∧
  (2^64 ≤ n.val + ovModel n.val → max_encoding_length n = fail .panic)

/-- The bound covers the actual encoding produced by the streaming encoder. -/
def gold_length_covers (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) : Prop :=
  (do let e ← encRun (msg x n z b); let m ← max_encoding_length (mkU .Usize (msg x n z b).length); ok (e, m))
    ⦃ p => p.1.length ≤ p.2.val ⦄

/-! ## Encoder -/

def gold_encode_exact (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) : Prop :=
  encRun (msg x n z b) ⦃ e => e = encModel (vals (msg x n z b)) ⦄

def gold_encode_no_zero (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) : Prop :=
  encRun (msg x n z b) ⦃ e => e.all (· != 0) = true ∧ e ≠ [] ⦄

def gold_encode_roundtrip (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) : Prop :=
  encRun (msg x n z b) ⦃ e => decModel e = some (vals (msg x n z b)) ⦄

def gold_encode_empty : Prop := encRun [] = ok [1]

/-! ## Decoder -/

def gold_decoder_default_idle : Prop :=
  dec.DecoderState.Insts.CoreDefaultDefault.default ⦃ s => isIdle s = true ⦄

def gold_feed_total (t i d : Std.U8) : Prop :=
  dec.DecoderState.feed (mkDState t i) d ⦃ _ => True ⦄

def gold_feed_idle_zero : Prop :=
  dec.DecoderState.feed .Idle 0#u8 ⦃ p => evCode p.1 = 258 ∧ isIdle p.2 = true ⦄

/-- Decoding a well-formed frame plus sentinel: `DataStart`, the message bytes (with
`NoData` only for block headers), `DataComplete`, back to `Idle`. -/
def gold_decode_frame (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) : Prop :=
  decRun (u8s (encModel (vals (msg x n z b))) ++ [0#u8]) ⦃ p =>
    p.1.filter (· != 258) = 256 :: vals (msg x n z b) ++ [257] ∧ isIdle p.2 = true ⦄

/-- The streaming encoder and decoder agree. -/
def gold_encode_decode (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) : Prop :=
  (do let e ← encRun (msg x n z b); decRun (u8s e ++ [0#u8])) ⦃ p =>
    frames p.1 = ([vals (msg x n z b)], 0) ∧ isIdle p.2 = true ⦄

/-- Leading/extra sentinels are ignored and consecutive frames are decoded independently. -/
def gold_decode_stream (x y : List Std.U8) (k : Std.U8) : Prop :=
  decRun (List.replicate (k.val % 3) 0#u8 ++ u8s (encModel (vals x)) ++ [0#u8] ++
      List.replicate (k.val / 3 % 3) 0#u8 ++ u8s (encModel (vals y)) ++ [0#u8]) ⦃ p =>
    frames p.1 = ([vals x, vals y], 0) ∧ isIdle p.2 = true ⦄

/-- Arbitrary zero-free frame plus sentinel: delivered iff it is a valid COBS frame
(with the reference decoding), otherwise exactly one `InvalidFrame` error and the
decoder is back to `Idle`. -/
def gold_decode_any_frame (x : List Std.U8) (n : Std.U16) (z k v : Std.U8) : Prop :=
  frameIn x n z k v ≠ [] →
  decRun (frameIn x n z k v ++ [0#u8]) ⦃ p =>
    isIdle p.2 = true ∧ outcomeOk (decModel (vals (frameIn x n z k v))) p.1 = true ⦄

/-- After an early-terminated (invalid) frame the decoder resynchronises at that zero. -/
def gold_decode_resync (x y : List Std.U8) (n : Std.U16) (z k v : Std.U8) : Prop :=
  frameIn x n z k v ≠ [] → decModel (vals (frameIn x n z k v)) = none →
  decRun (frameIn x n z k v ++ [0#u8] ++ u8s (encModel (vals y)) ++ [0#u8]) ⦃ p =>
    frames p.1 = ([vals y], 1) ∧ isIdle p.2 = true ⦄

/-! ## Differential-testing probes -/

def diff_overhead (n : Std.Usize) := max_encoding_overhead n
def diff_length (n : Std.Usize) := max_encoding_length n
def diff_encode (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) := encRun (msg x n z b)
def diff_push (c : Std.U16) (s o d : Std.U8) :=
  enc.EncoderState.push { code_idx := mkU .Usize c.val, num_bt_sent := s, offset_idx := o } d
def diff_finalize (c : Std.U16) (s o : Std.U8) :=
  enc.EncoderState.finalize { code_idx := mkU .Usize c.val, num_bt_sent := s, offset_idx := o }
def diff_feed (t i d : Std.U8) := do
  let (r, s) ← dec.DecoderState.feed (mkDState t i) d
  ok (evCode r, match s with | .Idle => (0, 0) | .Grab j => (1, j.val) | .GrabChain j => (2, j.val))
def diff_decode (x : List Std.U8) (n : Std.U16) (z k v : Std.U8) := do
  let (evs, s) ← decRun (frameIn x n z k v ++ [0#u8]); ok (evs, isIdle s)
def diff_decode_valid (x : List Std.U8) (n : Std.U16) (z : Std.U8) (b : Bool) := do
  let (evs, s) ← decRun (u8s (encModel (vals (msg x n z b))) ++ [0#u8]); ok (evs, isIdle s)

end Benchmark.V2.Cobs.State.Gold
