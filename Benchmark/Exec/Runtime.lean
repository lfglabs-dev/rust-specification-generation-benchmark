import Aeneas
import CoreModels
import Plausible

/-!
# Executable specification testing runtime

Used by the grader (and the agent's `test_spec` tool) to evaluate a candidate
specification `S : A₁ → … → Aₙ → Prop` on concrete inputs against the
*executable* build of the extracted Rust code.

* `Arbitrary` instances for Rust scalars, slices, vectors and arrays, biased
  towards boundary values (0, 1, MAX, MIN, powers of two ± 1) and log-uniform
  magnitudes so that typical preconditions (`x.val < 2^40`, `x ≠ 0`) are hit.
* `Decidable` instances for the Aeneas weakest-precondition notation
  `e ⦃ r => P r ⦄` and for `RustM` equality.
* `RSGB.Exec.check`, a deterministic test loop with a fixed seed so that the
  same inputs are used for the candidate and for every mutant.
-/

open Plausible Aeneas Aeneas.Std Aeneas.Std.WP

namespace RSGB.Exec

/-! ## Generators -/

/-- A natural number below `2^w`, biased towards boundary values. -/
def genBits (w : Nat) : Gen Nat := do
  let mode ← Gen.chooseNatLt 0 10 (by omega)
  if mode.val < 3 then
    let edges : List Nat :=
      [0, 1, 2, 3, 2^w - 1, 2^w - 2, 2^(w-1), 2^(w-1) - 1, 2^(w-1) + 1, 2^(w/2), 2^(w/2) - 1, 2^(w/2) + 1]
    let i ← Gen.chooseNatLt 0 edges.length (by simp [edges])
    pure (edges.getD i.val 0 % 2^w)
  else if mode.val < 7 then
    let k ← Gen.chooseNatLt 0 (w + 1) (by omega)
    let n ← Gen.chooseNatLt 0 (2^k.val) (Nat.two_pow_pos _)
    pure n.val
  else
    let n ← Gen.chooseNatLt 0 (2^w) (Nat.two_pow_pos _)
    pure n.val

instance (ty : UScalarTy) : Arbitrary (UScalar ty) where
  arbitrary := do
    let n ← genBits ty.numBits
    pure ⟨BitVec.ofNat _ n⟩

instance (ty : IScalarTy) : Arbitrary (IScalar ty) where
  arbitrary := do
    let n ← genBits ty.numBits
    pure ⟨BitVec.ofNat _ n⟩

/-- A list length: usually small, sometimes empty, occasionally longer. -/
def genLen : Gen Nat := do
  let mode ← Gen.chooseNatLt 0 10 (by omega)
  if mode.val < 1 then pure 0
  else if mode.val < 7 then pure (← Gen.chooseNatLt 1 9 (by omega)).val
  else pure (← Gen.chooseNatLt 9 65 (by omega)).val

def genList {α} [Arbitrary α] (n : Nat) : Gen (List α) := do
  let mut out := []
  for _ in [0:n] do
    out := (← Arbitrary.arbitrary) :: out
  pure out

instance (priority := high) instArbList {α} [Arbitrary α] : Arbitrary (List α) where
  arbitrary := do genList (← genLen)

instance {α} [Arbitrary α] : Arbitrary (Slice α) where
  arbitrary := do
    let l : List α ← Arbitrary.arbitrary
    if h : l.length ≤ Usize.max then pure ⟨l, h⟩ else pure ⟨[], by simp⟩

instance {α} [Arbitrary α] : Arbitrary (alloc.vec.Vec α) where
  arbitrary := do
    let l : List α ← Arbitrary.arbitrary
    if h : l.length ≤ Usize.max then pure ⟨l, h⟩ else pure ⟨[], by simp⟩

instance {α} [Arbitrary α] [Inhabited α] (n : Usize) : Arbitrary (Std.Array α n) where
  arbitrary := do
    let l : List α ← genList n.val
    if h : l.length = n.val then pure ⟨l, h⟩
    else pure ⟨List.replicate n.val default, by simp⟩

instance (priority := high) {α β} [Arbitrary α] [Arbitrary β] : Arbitrary (α × β) where
  arbitrary := do pure (← Arbitrary.arbitrary, ← Arbitrary.arbitrary)

instance (priority := high) : Arbitrary Bool where
  arbitrary := do pure ((← Gen.chooseNatLt 0 2 (by omega)).val == 1)

/-! ## `Repr` / `DecidableEq` for Aeneas containers (inputs and outputs) -/

instance {α} [Repr α] : Repr (Slice α) := ⟨fun s p => Repr.addAppParen ("slice " ++ repr s.val) p⟩
instance {α} [Repr α] : Repr (alloc.vec.Vec α) := ⟨fun s p => Repr.addAppParen ("vec " ++ repr s.val) p⟩
instance {α} [Repr α] (n : Usize) : Repr (Std.Array α n) := ⟨fun s p => Repr.addAppParen ("array " ++ repr s.val) p⟩
instance {α} [DecidableEq α] : DecidableEq (alloc.vec.Vec α) :=
  inferInstanceAs (DecidableEq { _l : List α // _ })
instance {α} [DecidableEq α] (n : Usize) : DecidableEq (Std.Array α n) :=
  inferInstanceAs (DecidableEq { _l : List α // _ })

/-! ## Decidability of Aeneas specification forms -/

instance decSpec {α} (x : RustM α) (p : Post α) [h : ∀ a, Decidable (p a)] :
    Decidable (WP.spec x p) :=
  match x with
  | .ok v => decidable_of_iff (p v) (by simp [WP.spec, WP.theta, WP.wp_return])
  | .fail _ => isFalse (by simp [WP.spec, WP.theta])
  | .div => isFalse (by simp [WP.spec, WP.theta])

instance decUncurry' {α β} (p : α → β → Prop) [h : ∀ a b, Decidable (p a b)] (x : α × β) :
    Decidable (WP.uncurry' p x) :=
  decidable_of_iff (p x.1 x.2) (by cases x; simp [WP.uncurry'])

instance decUncurry {α β} (p : α → β → Prop) [h : ∀ a b, Decidable (p a b)] (x : α × β) :
    Decidable (Aeneas.Std.uncurry p x) :=
  decidable_of_iff (p x.1 x.2) (by cases x; simp [Aeneas.Std.uncurry])

instance : DecidableEq Error := fun a b =>
  match a, b with
  | .panic, .panic => isTrue rfl
  | .undef, .undef => isTrue rfl
  | .panic, .undef => isFalse (by intro h; cases h)
  | .undef, .panic => isFalse (by intro h; cases h)

instance decEqRustM {α} [DecidableEq α] : DecidableEq (RustM α) := fun a b =>
  match a, b with
  | .ok x, .ok y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .fail x, .fail y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .div, .div => isTrue rfl
  | .ok _, .fail _ | .ok _, .div | .fail _, .ok _ | .fail _, .div | .div, .ok _ | .div, .fail _ =>
    isFalse (by intro e; cases e)

/-- `∃ r, e = ok r ∧ P r` (the explicit total-correctness form). -/
instance decExistsOk {α} (e : RustM α) (P : α → Prop) [∀ a, Decidable (P a)] :
    Decidable (∃ r, e = .ok r ∧ P r) :=
  match e with
  | .ok v => decidable_of_iff (P v) (by simp)
  | .fail _ => isFalse (by simp)
  | .div => isFalse (by simp)

/-! ## Test loop -/

/-- Outcome of testing one property. -/
structure Outcome where
  tested : Nat
  /-- inputs on which the property was false (at most `maxReport`) -/
  failures : List String
  /-- inputs whose evaluation crashed the generator (should be 0) -/
  genErrors : Nat
  deriving Repr

/-- Evaluate the decidable property `P` on `n` generated inputs (seeded). -/
def check {β} [Arbitrary β] [Repr β] (P : β → Prop) [DecidablePred P]
    (n : Nat) (seed : Nat := 0) (maxReport : Nat := 3) (size : Nat := 100) : IO Outcome := do
  let mut fails : List String := []
  let mut tested := 0
  let mut genErrors := 0
  for i in [0:n] do
    let g : Gen β := Arbitrary.arbitrary
    let r : Except GenError (β × ULift StdGen) :=
      ReaderT.run (StateT.run g (ULift.up (mkStdGen (seed * 1000003 + i)))) ⟨size⟩
    match r with
    | Except.error _ => genErrors := genErrors + 1
    | Except.ok (x, _) =>
      tested := tested + 1
      if !(decide (P x)) then
        if fails.length < maxReport then
          fails := fails ++ [toString (repr x)]
        else
          return { tested, failures := fails, genErrors }
  return { tested, failures := fails, genErrors }

end RSGB.Exec
