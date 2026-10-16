import Benchmark.Exec.Runtime
import Lean

/-!
# Generic test commands

* `#rsgb_test c n seed` — test a property constant `c` on `n` generated inputs.
  - If `c` is a definition `c : A₁ → … → Aₙ → Prop`, the property is `c x₁ … xₙ`.
  - If `c` is a theorem/axiom `c : ∀ (x₁ : A₁) … (h : H x) …, Q x`, the
    property is its statement; `Prop`-typed binders become preconditions.
  Prints one line `RSGB_RESULT {"name":…,"tested":…,"failures":[…],"gen_errors":…}`
  or `RSGB_ERROR {"name":…,"error":…}` when the property cannot be executed
  (no `Decidable` instance, unsupported binder type, …).
* `#rsgb_outputs f n seed` — evaluate the Rust function `f : A₁ → … → RustM R`
  on `n` generated inputs and print one hash per input (`RSGB_OUT i h`), used
  for differential testing of mutants.

`Decidable` instances are found after unfolding `Prop`-valued definitions from
the benchmark namespaces (the candidate's own helpers and `Defs.lean`).
-/

open Lean Meta Elab Command Term

namespace RSGB.Exec

/-- Is `n` a non-recursive benchmark/candidate definition whose type is `∀ …, Prop`?
Only those are unfolded when searching for a `Decidable` instance: data-valued
helpers stay folded (they are evaluated by compiled code), and recursive
definitions would unfold to `brecOn`/`WellFounded.fix` terms the code generator
cannot compile. -/
def unfoldableProp (n : Name) : MetaM Bool := do
  let s := n.toString
  unless s.startsWith "Benchmark." || s.startsWith "Candidate." do return false
  let some (.defnInfo info) := (← getEnv).find? n | return false
  let recursive := info.value.getUsedConstants.any fun c =>
    c == ``WellFounded.fix || (match c with | .str _ "brecOn" => true | _ => false) || c == n
  if recursive then return false
  forallTelescopeReducing info.type fun _ body => return body.isProp

/-- Repeatedly delta-expand `Prop`-valued benchmark definitions at the head and
inside logical connectives, then synthesize `Decidable`. -/
partial def synthDecidable (p : Expr) : MetaM (Option Expr) := do
  if let some inst ← (try? (synthInstance (mkApp (Expr.const ``Decidable []) p))) then
    return some inst
  let mut ok : NameSet := {}
  for c in p.getUsedConstants do
    if ← unfoldableProp c then ok := ok.insert c
  if ok.isEmpty then return none
  let p' ← deltaExpand p (ok.contains ·)
  let p' ← instantiateMVars (← whnfCore p')
  if p' == p then return none
  synthDecidable p'

/-- Build `(tupleType, P : tupleType → Prop)` from a property constant. -/
def propOf (c : Name) : MetaM (Expr × Expr × Nat) := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map fun _ => Level.zero
  let ty := info.type.instantiateLevelParams info.levelParams lvls
  let isDef := match info with | .defnInfo _ => true | _ => false
  forallTelescopeReducing ty fun xs body => do
    -- data binders are sampled; Prop binders become premises
    let mut data : Array Expr := #[]
    let mut hyps : Array Expr := #[]
    for x in xs do
      if ← isProp (← inferType x) then hyps := hyps.push x else data := data.push x
    let stmt ←
      if isDef then
        unless body.isProp do throwError "property {c} does not return Prop"
        pure (mkAppN (Expr.const c lvls) xs)
      else pure body
    let stmt ← mkForallFVars hyps stmt
    if data.isEmpty then throwError "property {c} has no inputs"
    let tys ← data.mapM inferType
    for t in tys do
      if t.hasAnyFVar (fun f => data.any (·.fvarId! == f)) then
        throwError "dependent binder types are not supported"
    let tupleTy ← tys.pop.foldrM (fun t acc => mkAppM ``Prod #[t, acc]) tys.back!
    let P ← withLocalDeclD `t tupleTy fun t => do
      -- projections t.1, t.2.1, …, t.2.….2
      let mut projs : Array Expr := #[]
      let mut cur := t
      for i in [0:data.size] do
        if i + 1 == data.size then projs := projs.push cur
        else
          projs := projs.push (← mkAppM ``Prod.fst #[cur])
          cur ← mkAppM ``Prod.snd #[cur]
      let s := (← mkLambdaFVars data stmt).beta projs
      mkLambdaFVars #[t] s
    return (tupleTy, P, data.size)

unsafe def evalOutcome (e : Expr) : TermElabM Outcome := do
  let act ← Lean.Meta.evalExpr (IO Outcome) (mkApp (Expr.const ``IO []) (Expr.const ``Outcome [])) e
  act

/-- Run the property constant `c` on `n` inputs (seeded); stop after `maxReport` failures. -/
def runProp (c : Name) (n seed maxReport : Nat) : TermElabM Outcome := do
  let (tupleTy, P, _) ← propOf c
  let instFn ← withLocalDeclD `t tupleTy fun t => do
    let body ← whnfCore (mkApp P t).headBeta
    match ← synthDecidable body with
    | some inst => mkLambdaFVars #[t] inst
    | none => throwError "no Decidable instance for the property (use Bool helpers or bounded quantifiers)"
  let e ← mkAppOptM ``RSGB.Exec.check
    #[tupleTy, none, none, P, instFn, mkNatLit n, mkNatLit seed, mkNatLit maxReport, mkNatLit 100]
  unsafe evalOutcome e

elab "#rsgb_test " id:ident n:num seed:num : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let nm := c.toString
  liftTermElabM do
    try
      let o ← runProp c n.getNat seed.getNat 3
      let j := Json.mkObj [("name", Json.str nm), ("tested", toJson o.tested),
        ("failures", toJson o.failures), ("gen_errors", toJson o.genErrors)]
      logInfo ("RSGB_RESULT " ++ j.compress)
    catch ex =>
      let j := Json.mkObj [("name", Json.str nm), ("error", Json.str (← ex.toMessageData.toString))]
      logInfo ("RSGB_ERROR " ++ j.compress)

/-- `#rsgb_kill n seed p₁ p₂ …`: run the properties in order and stop at the first
input on which one of them is false. Prints `RSGB_KILL {"killed_by": name | null}`. -/
elab "#rsgb_kill " n:num seed:num ids:ident* : command => do
  let cs ← ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM do
    let mut killer : Option String := none
    let mut errors : Array String := #[]
    for c in cs do
      try
        let o ← runProp c n.getNat seed.getNat 1
        if !o.failures.isEmpty then
          killer := some c.toString
          break
      catch _ => errors := errors.push c.toString
    let j := Json.mkObj [("killed_by", match killer with | some k => Json.str k | none => Json.null),
      ("errors", toJson errors)]
    logInfo ("RSGB_KILL " ++ j.compress)

/-- Hash of the `Repr` of each output. -/
def outputs {β γ} [Plausible.Arbitrary β] [Repr γ] (f : β → γ) (n seed : Nat) (size : Nat := 100) :
    IO (Array UInt64) := do
  let mut out := #[]
  for i in [0:n] do
    let g : Plausible.Gen β := Plausible.Arbitrary.arbitrary
    let r : Except Plausible.GenError (β × ULift StdGen) :=
      ReaderT.run (StateT.run g (ULift.up (mkStdGen (RSGB.Exec.mixSeed (seed * 1000003 + i))))) ⟨size⟩
    match r with
    | Except.error _ => out := out.push 0
    | Except.ok (x, _) => out := out.push (hash (toString (repr (f x))))
  return out

unsafe def evalOutputs (e : Expr) : TermElabM (Array UInt64) := do
  let act ← Lean.Meta.evalExpr (IO (Array UInt64))
    (mkApp (Expr.const ``IO []) (mkApp (Expr.const ``Array [Level.zero]) (Expr.const ``UInt64 []))) e
  act

elab "#rsgb_outputs " id:ident n:num seed:num : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM do
    try
      let info ← getConstInfo c
      let lvls := info.levelParams.map fun _ => Level.zero
      let f := Expr.const c lvls
      let ty ← inferType f
      let (tupleTy, F) ← forallTelescopeReducing ty fun xs _ => do
        let tys ← xs.mapM (fun x => (inferType x : MetaM Expr))
        let tupleTy ← tys.pop.foldrM (fun t acc => mkAppM ``Prod #[t, acc]) tys.back!
        let F ← withLocalDeclD `t tupleTy fun t => do
          let mut projs : Array Expr := #[]
          let mut cur := t
          for i in [0:xs.size] do
            if i + 1 == xs.size then projs := projs.push cur
            else
              projs := projs.push (← mkAppM ``Prod.fst #[cur])
              cur ← mkAppM ``Prod.snd #[cur]
          mkLambdaFVars #[t] (mkAppN f projs)
        return (tupleTy, F)
      let e ← mkAppOptM ``RSGB.Exec.outputs
        #[tupleTy, none, none, none, F, mkNatLit n.getNat, mkNatLit seed.getNat, mkNatLit 100]
      let hs ← unsafe evalOutputs e
      logInfo ("RSGB_OUTPUTS " ++ c.toString ++ " " ++ " ".intercalate (hs.toList.map toString))
    catch ex =>
      let j := Json.mkObj [("name", Json.str c.toString), ("error", Json.str (← ex.toMessageData.toString))]
      logInfo ("RSGB_ERROR " ++ j.compress)

end RSGB.Exec
