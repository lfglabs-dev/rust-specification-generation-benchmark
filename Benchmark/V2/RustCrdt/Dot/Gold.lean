import Benchmark.V2.Prelude
import RustCrdtDot.Extraction

/-! Hidden gold specification for target `rust_crdt/dot` (actors instantiated at `u8`). -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM crdts RSGB


namespace Benchmark.V2.RustCrdt.Dot.Gold

/-! ## Reference model -/

def ordOf {α} [LT α] [DecidableRel (α := α) (· < ·)] [DecidableEq α] (a b : α) : core.cmp.Ordering :=
  if a < b then .Less else if a = b then .Equal else .Greater

/-- Lexicographic combination. -/
def lex : core.cmp.Ordering → core.cmp.Ordering → core.cmp.Ordering
  | .Equal, o => o
  | o, _ => o

/-- Second dot: same actor / same counter as the first when the flags say so. -/
def pick {α} (same : Bool) (x y : α) : α := if same then x else y

abbrev D := dot.Dot Std.U8
abbrev OD := dot.OrdDot Std.U8

def mkD (a : Std.U8) (c : Std.U64) : D := { actor := a, counter := c }
def mkOD (a : Std.U8) (c : Std.U64) : OD := { actor := a, counter := c }

def dotEq (x y : D) := dot.Dot.Insts.CoreCmpPartialEqDot.eq core.U8.Insts.CoreCmpPartialEqU8 x y
def dotPcmp (x y : D) := dot.Dot.Insts.CoreCmpPartialOrdDot.partial_cmp core.U8.Insts.CoreCmpPartialOrdU8 x y
def odEq (x y : OD) := dot.OrdDot.Insts.CoreCmpPartialEqOrdDot.eq core.U8.Insts.CoreCmpPartialEqU8 core.U8.Insts.CoreCmpOrd x y
def odPcmp (x y : OD) :=
  dot.OrdDot.Insts.CoreCmpPartialOrdOrdDot.partial_cmp core.U8.Insts.CoreCmpPartialOrdU8 core.U8.Insts.CoreCmpOrd x y
def odCmp (x y : OD) := dot.OrdDot.Insts.CoreCmpOrd.cmp core.U8.Insts.CoreCmpOrd core.U8.Insts.CoreCmpOrd x y

/-! ## Construction -/

def gold_new (a : Std.U8) (c : Std.U64) : Prop :=
  dot.Dot.new a c = ok (mkD a c) ∧
  dot.Dot.Insts.CoreConvertFromPairAU64.from (a, c) = ok (mkD a c)

def gold_clone (a : Std.U8) (c : Std.U64) : Prop :=
  dot.Dot.Insts.CoreCloneClone.clone core.U8.Insts.CoreCloneClone (mkD a c) = ok (mkD a c) ∧
  dot.OrdDot.Insts.CoreCloneClone.clone core.U8.Insts.CoreCloneClone core.U8.Insts.CoreCmpOrd (mkOD a c) =
    ok (mkOD a c)

/-! ## Increment: successor on the same actor; panics exactly on counter overflow -/

def gold_inc (a : Std.U8) (c : Std.U64) : Prop :=
  if c.val < 2^64 - 1 then
    dot.Dot.inc core.U8.Insts.CoreCloneClone (mkD a c) = ok (mkD a (mkU .U64 (c.val + 1)))
  else dot.Dot.inc core.U8.Insts.CoreCloneClone (mkD a c) = fail .panic

def gold_apply_inc (a : Std.U8) (c : Std.U64) : Prop :=
  if c.val < 2^64 - 1 then
    dot.Dot.apply_inc (mkD a c) = ok (mkD a (mkU .U64 (c.val + 1)))
  else dot.Dot.apply_inc (mkD a c) = fail .panic

/-- The successor is strictly greater than the original dot (and comparable). -/
def gold_inc_greater (a : Std.U8) (c : Std.U64) : Prop :=
  c.val < 2^64 - 1 →
    (do let d ← dot.Dot.inc core.U8.Insts.CoreCloneClone (mkD a c); dotPcmp (mkD a c) d) = ok (some .Less)

/-! ## `Dot`: equality and the per-actor partial order -/

def gold_dot_eq (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) : Prop :=
  let b' := pick sa a b
  let d' := pick sc c d
  dotEq (mkD a c) (mkD b' d') = ok (decide (a = b' ∧ c = d'))

def gold_dot_partial_cmp (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) : Prop :=
  let b' := pick sa a b
  let d' := pick sc c d
  dotPcmp (mkD a c) (mkD b' d') = ok (if a = b' then some (ordOf c.val d'.val) else none)

/-! ## `OrdDot`: total lexicographic order (actor first, then counter) -/

def gold_orddot_eq (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) : Prop :=
  let b' := pick sa a b
  let d' := pick sc c d
  odEq (mkOD a c) (mkOD b' d') = ok (decide (a = b' ∧ c = d'))

def gold_orddot_cmp (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) : Prop :=
  let b' := pick sa a b
  let d' := pick sc c d
  odCmp (mkOD a c) (mkOD b' d') = ok (lex (ordOf a.val b'.val) (ordOf c.val d'.val)) ∧
  odPcmp (mkOD a c) (mkOD b' d') = ok (some (lex (ordOf a.val b'.val) (ordOf c.val d'.val)))

/-! ## Conversions between `Dot` and `OrdDot` preserve both fields -/

def gold_conversions (a : Std.U8) (c : Std.U64) : Prop :=
  dot.OrdDot.Insts.CoreConvertFromDot.from core.U8.Insts.CoreCmpOrd (mkD a c) = ok (mkOD a c) ∧
  dot.Dot.Insts.CoreConvertFromOrdDot.from core.U8.Insts.CoreCmpOrd (mkOD a c) = ok (mkD a c)

/-- On dots of the same actor, `OrdDot::cmp` agrees with `Dot::partial_cmp`. -/
def gold_orddot_refines_dot (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) : Prop :=
  let b' := pick sa a b
  let d' := pick sc c d
  a = b' → (do let o ← odCmp (mkOD a c) (mkOD b' d'); ok (some o)) = dotPcmp (mkD a c) (mkD b' d')

/-! Differential-testing probes. -/

def diff_new (a : Std.U8) (c : Std.U64) := dot.Dot.new a c
def diff_from_pair (a : Std.U8) (c : Std.U64) := dot.Dot.Insts.CoreConvertFromPairAU64.from (a, c)
def diff_inc (a : Std.U8) (c : Std.U64) := dot.Dot.inc core.U8.Insts.CoreCloneClone (mkD a c)
def diff_apply_inc (a : Std.U8) (c : Std.U64) := dot.Dot.apply_inc (mkD a c)
def diff_clone (a : Std.U8) (c : Std.U64) :=
  (dot.Dot.Insts.CoreCloneClone.clone core.U8.Insts.CoreCloneClone (mkD a c),
   dot.OrdDot.Insts.CoreCloneClone.clone core.U8.Insts.CoreCloneClone core.U8.Insts.CoreCmpOrd (mkOD a c))
def diff_dot_eq (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) := dotEq (mkD a c) (mkD (pick sa a b) (pick sc c d))
def diff_dot_pcmp (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) := dotPcmp (mkD a c) (mkD (pick sa a b) (pick sc c d))
def diff_od_eq (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) := odEq (mkOD a c) (mkOD (pick sa a b) (pick sc c d))
def diff_od_pcmp (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) := odPcmp (mkOD a c) (mkOD (pick sa a b) (pick sc c d))
def diff_od_cmp (a b : Std.U8) (c d : Std.U64) (sa sc : Bool) := odCmp (mkOD a c) (mkOD (pick sa a b) (pick sc c d))
def diff_conv (a : Std.U8) (c : Std.U64) :=
  (dot.OrdDot.Insts.CoreConvertFromDot.from core.U8.Insts.CoreCmpOrd (mkD a c),
   dot.Dot.Insts.CoreConvertFromOrdDot.from core.U8.Insts.CoreCmpOrd (mkOD a c))

end Benchmark.V2.RustCrdt.Dot.Gold
