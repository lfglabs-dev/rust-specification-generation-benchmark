import Lean

open Lean Meta

def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def node (op : String) (args : Array Json := #[]) : Json :=
  Json.mkObj [("op", toJson op), ("args", Json.arr args)]

def ufNode (kind : String) (fn : String) (args : Array Json) (leaf : Nat := 0) (sort : String := "int") : Json :=
  Json.mkObj [("op", toJson kind), ("fn", toJson fn), ("leaf", toJson leaf), ("sort", toJson sort), ("args", Json.arr args)]

structure VarInfo where
  name : String
  sort : String
  deriving Inhabited

structure AuditState where
  vars : Array VarInfo := #[]
  varMap : FVarIdMap String := {}
  subst : FVarIdMap Json := {}
  resultMap : FVarIdMap (Json × Expr × Expr) := {}
  optionMap : FVarIdMap (Json × Expr) := {}
  nextSym : Nat := 0
  qDepth : Nat := 0
  lamDepth : Nat := 0

abbrev AuditM := StateRefT AuditState MetaM

partial def axiomClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (axioms : NameSet := {}) : NameSet :=
  match todo with
  | [] => axioms
  | name :: rest =>
    if seen.contains name then axiomClosure env rest seen axioms
    else
      let seen := seen.insert name
      match env.find? name with
      | none => axiomClosure env rest seen (axioms.insert name)
      | some ci =>
        let deps := ci.type.getUsedConstants.toList ++
          (match ci.value? true with | some v => v.getUsedConstants.toList | none => [])
        let axioms := if ci.isAxiom || ci.isUnsafe then axioms.insert name else axioms
        axiomClosure env (deps ++ rest) seen axioms

def auditDecl (env : Environment) (name : Name) (expectedType : Expr) : MetaM Unit := do
  let some ci := env.find? name | throwError "missing declaration {name}"
  unless ← isDefEq ci.type expectedType do
    throwError "wrong type for {name}: expected {← ppExpr expectedType}, got {← ppExpr ci.type}"
  for ax in (axiomClosure env [name]).toArray do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unauthorized axiom or unsafe dependency: {ax}"

def freshIndex : AuditM Nat := do
  modifyGet fun s => (s.nextSym, { s with nextSym := s.nextSym + 1 })

def registerVar (fv : FVarId) (name : String) (sort : String) : AuditM Json := do
  let j := Json.mkObj [("var", toJson name), ("sort", toJson sort)]
  modify fun s => {
    s with
    vars := s.vars.push { name := name, sort := sort },
    varMap := s.varMap.insert fv name,
    subst := s.subst.insert fv j
  }
  return j

def isCoreName (n? : Option Name) (suffix : String) : Bool :=
  match n? with
  | some n =>
    let s := n.toString
    s == suffix || s == "CoreModels." ++ suffix || s == "core." ++ suffix || s == "CoreModels.core." ++ suffix
  | none => false

def detectSort (ty : Expr) : MetaM String := do
  let ty ← withTransparency .all (whnf ty)
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if fn.constName? == some `Aeneas.Std.UScalar && args.size == 1 then
    match args[0]!.constName? with
    | some `Aeneas.Std.UScalarTy.U8 => return "u8"
    | some `Aeneas.Std.UScalarTy.U16 => return "u16"
    | some `Aeneas.Std.UScalarTy.U32 => return "u32"
    | some `Aeneas.Std.UScalarTy.U64 => return "u64"
    | some `Aeneas.Std.UScalarTy.U128 => return "u128"
    | some `Aeneas.Std.UScalarTy.Usize => return "usize"
    | _ => return "u64"
  if fn.constName? == some `Aeneas.Std.IScalar && args.size == 1 then
    match args[0]!.constName? with
    | some `Aeneas.Std.IScalarTy.I8 => return "i8"
    | some `Aeneas.Std.IScalarTy.I16 => return "i16"
    | some `Aeneas.Std.IScalarTy.I32 => return "i32"
    | some `Aeneas.Std.IScalarTy.I64 => return "i64"
    | some `Aeneas.Std.IScalarTy.I128 => return "i128"
    | some `Aeneas.Std.IScalarTy.Isize => return "isize"
    | _ => return "i64"
  if ty.isConstOf ``Nat then return "nat"
  if ty.isConstOf ``Int then return "int"
  if ty.isConstOf ``Bool then return "bool"
  if isCoreName fn.constName? "cmp.Ordering" then return "ordering"
  return "int"

partial def mkListExpr (elemTy : Expr) (u : Level) (elems : List Expr) : Expr :=
  match elems with
  | [] => mkApp (mkConst ``List.nil [u]) elemTy
  | x :: xs => mkApp3 (mkConst ``List.cons [u]) elemTy x (mkListExpr elemTy u xs)

def extractSmallArrayType? (ty : Expr) : MetaM (Option (Expr × Nat)) := do
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if (fn.constName? == some `Aeneas.Std.Array || fn.constName? == some `Std.Array) && args.size == 2 then
    let elemTy := args[0]!
    let lenUsize := args[1]!
    let valApp := mkApp2 (mkConst `Aeneas.Std.UScalar.val) (mkConst `Aeneas.Std.UScalarTy.Usize) lenUsize
    let reduced ← withTransparency .all (whnf valApp)
    if let .lit (.natVal n) := reduced then
      if n ≤ 16 then return some (elemTy, n)
  let tyWhnf ← withTransparency .all (whnf ty)
  if tyWhnf.isAppOfArity ``Subtype 2 then
    let listTy := tyWhnf.getArg! 0
    let pred := tyWhnf.getArg! 1
    if listTy.isAppOfArity ``List 1 then
      let elemTy := listTy.getArg! 0
      if let .lam _ _ body _ := pred then
        if body.isAppOfArity ``Eq 3 then
          let rhs ← withTransparency .all (whnf (body.getArg! 2))
          if let .lit (.natVal n) := rhs then
            if n ≤ 16 then return some (elemTy, n)
  return none

def isAtomicScalarType (ty : Expr) : MetaM Bool := do
  if (← extractSmallArrayType? ty).isSome then return false
  let ty ← withTransparency .all (whnf ty)
  let fn := ty.getAppFn
  if fn.constName? == some `Aeneas.Std.UScalar || fn.constName? == some `Aeneas.Std.IScalar then
    return true
  if ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isConstOf ``Bool || ty.isConstOf ``Unit || ty.isConstOf ``PUnit then
    return true
  if fn.constName? == some `BitVec || fn.constName? == some ``Subtype || fn.constName? == some ``List then
    return true
  if isCoreName fn.constName? "alloc.vec.Vec" || fn.constName? == some `Aeneas.Std.Slice || isCoreName fn.constName? "cmp.Ordering" then
    return true
  return false

partial def expandSymbolicValueAux (ty : Expr) (nextLeaf : AuditM Nat) (mkLeaf : Nat → String → AuditM Json)
    (k : Expr → AuditM Json) (depth : Nat := 0) : AuditM Json := do
  if depth > 5 then
    let sort ← detectSort ty
    let idx ← freshIndex
    let leafIdx ← nextLeaf
    let j ← mkLeaf leafIdx sort
    withLocalDeclD ((Name.mkSimple "_sym").appendIndexAfter idx) ty fun fv => do
      modify fun s => { s with subst := s.subst.insert fv.fvarId! j }
      k fv
  else if let some (elemTy, n) ← extractSmallArrayType? ty then
    let u ← getDecLevel elemTy
    let tyWhnf ← withTransparency .all (whnf ty)
    let listTy := tyWhnf.getArg! 0
    let pred := tyWhnf.getArg! 1
    let rec buildElems (rem : Nat) (acc : List Expr) : AuditM Json := do
      match rem with
      | 0 =>
        let listExpr := mkListExpr elemTy u acc.reverse
        let propTy := (mkApp pred listExpr).headBeta
        let idx ← freshIndex
        withLocalDeclD ((Name.mkSimple "_arr_prop").appendIndexAfter idx) propTy fun propFv => do
          let subExpr := mkApp4 (mkConst ``Subtype.mk [u]) listTy pred listExpr propFv
          k subExpr
      | m + 1 =>
        expandSymbolicValueAux elemTy nextLeaf mkLeaf (depth := depth + 1) fun elemExpr =>
          buildElems m (elemExpr :: acc)
    buildElems n []
  else
    let tyWhnf ← withTransparency .all (whnf ty)
    let fn := tyWhnf.getAppFn
    let args := tyWhnf.getAppArgs
    if fn.constName? == some ``Prod && args.size == 2 then
      let aTy := args[0]!
      let bTy := args[1]!
      let u ← getDecLevel aTy
      let v ← getDecLevel bTy
      expandSymbolicValueAux aTy nextLeaf mkLeaf (depth := depth + 1) fun aExpr =>
        expandSymbolicValueAux bTy nextLeaf mkLeaf (depth := depth + 1) fun bExpr => do
          let pair := mkApp4 (mkConst ``Prod.mk [u, v]) aTy bTy aExpr bExpr
          k pair
    else if isCoreName fn.constName? "result.Result" && args.size == 2 then
      let okTy := args[0]!
      let errTy := args[1]!
      let idx ← freshIndex
      let leafIdx ← nextLeaf
      let isOkJson ← mkLeaf leafIdx "bool"
      expandSymbolicValueAux okTy nextLeaf mkLeaf (depth := depth + 1) fun okExpr =>
        expandSymbolicValueAux errTy nextLeaf mkLeaf (depth := depth + 1) fun errExpr => do
          withLocalDeclD ((Name.mkSimple "_res").appendIndexAfter idx) ty fun fv => do
            modify fun s => { s with resultMap := s.resultMap.insert fv.fvarId! (isOkJson, okExpr, errExpr) }
            k fv
    else if (isCoreName fn.constName? "option.Option" || fn.constName? == some ``Option) && args.size == 1 then
      let valTy := args[0]!
      let idx ← freshIndex
      let leafIdx ← nextLeaf
      let isSomeJson ← mkLeaf leafIdx "bool"
      expandSymbolicValueAux valTy nextLeaf mkLeaf (depth := depth + 1) fun valExpr => do
        withLocalDeclD ((Name.mkSimple "_opt").appendIndexAfter idx) ty fun fv => do
          modify fun s => { s with optionMap := s.optionMap.insert fv.fvarId! (isSomeJson, valExpr) }
          k fv
    else
      let env ← getEnv
      let atomic ← isAtomicScalarType tyWhnf
      if !atomic && fn.isConst && isStructure env fn.constName! then
        let structName := fn.constName!
        let sStr := structName.toString
        let isRangeStruct := sStr.startsWith "core.ops.range." || sStr.startsWith "CoreModels.core.ops.range."
        if !isRangeStruct && (sStr.endsWith "MontyParameters" || hasSubstr sStr "Insts." || sStr.startsWith "core.ops." || sStr.startsWith "CoreModels.core.ops.") then
          let idx ← freshIndex
          let leafIdx ← nextLeaf
          let j ← mkLeaf leafIdx "int"
          withLocalDeclD ((Name.mkSimple "_inst").appendIndexAfter idx) ty fun fv => do
            modify fun s => { s with subst := s.subst.insert fv.fvarId! j }
            k fv
        else

          let ctor := getStructureCtor env structName
          let ctorConst := mkConst ctor.name fn.constLevels!
          let params := args.extract 0 ctor.numParams
          let ctorApp := mkAppN ctorConst params
          let ctorType ← inferType ctorApp
          let rec buildFields (remType : Expr) (accArgs : Array Expr) : AuditM Json := do
            let remWhnf ← withTransparency .all (whnf remType)
            if let .forallE _ dom body _ := remWhnf then
              expandSymbolicValueAux dom nextLeaf mkLeaf (depth := depth + 1) fun fieldExpr =>
                buildFields (body.instantiate1 fieldExpr) (accArgs.push fieldExpr)
            else
              k (mkAppN ctorApp accArgs)
          buildFields ctorType #[]
      else
        let sort ← detectSort ty
        let idx ← freshIndex
        let leafIdx ← nextLeaf
        let j ← mkLeaf leafIdx sort
        withLocalDeclD ((Name.mkSimple "_sym").appendIndexAfter idx) ty fun fv => do
          modify fun s => { s with subst := s.subst.insert fv.fvarId! j }
          k fv

def expandSymbolicValue (ty : Expr) (mkLeaf : Nat → String → AuditM Json)
    (k : Expr → AuditM Json) : AuditM Json := do
  let leafRef ← IO.mkRef (0 : Nat)
  let nextLeaf : AuditM Nat := do
    let i ← leafRef.get
    leafRef.set (i + 1)
    return i
  expandSymbolicValueAux ty nextLeaf mkLeaf k 0


def tryEvalClosedInt? (e : Expr) : MetaM (Option Int) := do
  if e.hasFVar || e.hasLooseBVars then return none
  let ty ← inferType e
  let sort ← detectSort ty
  if sort == "nat" then
    let r ← withTransparency .all (whnf e)
    if let .lit (.natVal n) := r then return some (Int.ofNat n)
  else if sort.startsWith "u" then
    let uTy ← withTransparency .all (whnf ty)
    if uTy.isAppOfArity `Aeneas.Std.UScalar 1 then
      let valApp := mkApp2 (mkConst `Aeneas.Std.UScalar.val) (uTy.getArg! 0) e
      let r ← withTransparency .all (whnf valApp)
      if let .lit (.natVal n) := r then return some (Int.ofNat n)
  else if sort == "int" || sort.startsWith "i" then
    let target ← if sort.startsWith "i" then do
      let iTy ← withTransparency .all (whnf ty)
      if iTy.isAppOfArity `Aeneas.Std.IScalar 1 then
        pure (mkApp2 (mkConst `Aeneas.Std.IScalar.val) (iTy.getArg! 0) e)
      else pure e
    else pure e
    let r ← withTransparency .all (whnf target)
    if r.isAppOfArity ``Int.ofNat 1 then
      let arg ← withTransparency .all (whnf (r.getArg! 0))
      if let .lit (.natVal n) := arg then return some (Int.ofNat n)
    if r.isAppOfArity ``Int.negSucc 1 then
      let arg ← withTransparency .all (whnf (r.getArg! 0))
      if let .lit (.natVal n) := arg then return some (Int.negSucc n)
  return none

def intJson (n : Int) : Json :=
  Json.mkObj [("int", toJson n)]

def scalarBounds (sort : String) : (Int × Int × Int) :=
  match sort with
  | "u8" => (0, 255, 8)
  | "u16" => (0, 65535, 16)
  | "u32" => (0, 4294967295, 32)
  | "u64" | "usize" => (0, 18446744073709551615, 64)
  | "u128" => (0, 340282366920938463463374607431768211455, 128)
  | "i8" => (-128, 127, 8)
  | "i16" => (-32768, 32767, 16)
  | "i32" => (-2147483648, 2147483647, 32)
  | "i64" | "isize" => (-9223372036854775808, 9223372036854775807, 64)
  | "i128" => (-170141183460469231731687303715884105728, 170141183460469231731687303715884105727, 128)
  | _ => (0, 18446744073709551615, 64)

def opaqueHelperNames : List String := [
  "partitionPointLt", "IsNaiveMaximalSuffix", "BytesLe", "byteVals",
  "allCards", "allRanks", "allSuits", "suffixProducts", "sortI32", "sortU32", "evens", "odds",
  "IsEvenPredicate", "CollectsTo", "btreeset_union_vec",
  "factorial_reference", "permutations_reference", "checkedMulU128",
  "GetBits", "countBits", "leBytes32", "KBParams", "BBParams"
]

def shouldUnfoldHelper (n : Name) : Bool :=
  let s := n.toString
  if opaqueHelperNames.any (fun h => s.endsWith ("." ++ h) || s == h) then false
  else if s.startsWith "Candidate." || s.startsWith "Benchmark.Cases." || s.startsWith "Benchmark.Generated." then true
  else if hasSubstr s ".match_" || hasSubstr s "._sparseCasesOn_" || s.endsWith ".uncurry'" || s.endsWith ".uncurry" then true
  else if s == "Aeneas.Std.Array.to_slice_mut" ||
          s == "CoreModels.core.cmp.PartialOrd.lt.default" ||
          s == "CoreModels.core.cmp.PartialOrd.le.default" ||
          s == "CoreModels.core.cmp.PartialOrd.gt.default" ||
          s == "CoreModels.core.cmp.PartialOrd.ge.default" ||
          s == "crdts.dot.OrdDot.Insts.CoreCmpOrd" ||
          s == "crdts.dot.OrdDot.Insts.CoreCmpPartialOrdOrdDot" then true
  else false

partial def extractListElems? (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← withTransparency .all (whnf e)
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.constName? == some ``List.nil then
    return some #[]
  if fn.constName? == some ``List.cons && args.size == 3 then
    if let some rest ← extractListElems? args[2]! then
      return some (#[args[1]!] ++ rest)
  return none

partial def extractListElemAt? (listExpr : Expr) (idx : Nat) : MetaM (Option Expr) := do
  let listExpr ← withTransparency .all (whnf listExpr)
  if listExpr.isAppOfArity ``List.cons 3 then
    if idx == 0 then return some (listExpr.getArg! 1)
    else return ← extractListElemAt? (listExpr.getArg! 2) (idx - 1)
  return none


partial def replaceListElemAt? (listExpr : Expr) (idx : Nat) (newElem : Expr) : MetaM (Option Expr) := do
  let listExpr ← withTransparency .all (whnf listExpr)
  if listExpr.isAppOfArity ``List.cons 3 then
    let cFn := listExpr.getAppFn
    let ty := listExpr.getArg! 0
    let hd := listExpr.getArg! 1
    let tl := listExpr.getArg! 2
    if idx == 0 then
      return some (mkApp3 cFn ty newElem tl)
    else if let some tl' ← replaceListElemAt? tl (idx - 1) newElem then
      return some (mkApp3 cFn ty hd tl')
  return none

mutual

partial def findExistWitness? (e : Expr) : AuditM (Option Expr) := do
  let st ← get
  let cur ← normalizeHead e
  let fn := cur.getAppFn
  let args := cur.getAppArgs
  if fn.constName? == some ``Eq && args.size == 3 then
    let lhs ← normalizeHead args[1]!
    let rhs ← normalizeHead args[2]!
    if lhs.isFVar && isCoreName rhs.getAppFn.constName? "result.Result.Ok" then
      if let some (_, okE, _) := st.resultMap.get? lhs.fvarId! then
        if rhs.getAppArgs.back!.consumeMData == Expr.bvar 0 then return some okE else return none
      else return none
    else if rhs.isFVar && isCoreName lhs.getAppFn.constName? "result.Result.Ok" then
      if let some (_, okE, _) := st.resultMap.get? rhs.fvarId! then
        if lhs.getAppArgs.back!.consumeMData == Expr.bvar 0 then return some okE else return none
      else return none
    else if lhs.isFVar && isCoreName rhs.getAppFn.constName? "result.Result.Err" then
      if let some (_, _, errE) := st.resultMap.get? lhs.fvarId! then
        if rhs.getAppArgs.back!.consumeMData == Expr.bvar 0 then return some errE else return none
      else return none
    else if rhs.isFVar && isCoreName lhs.getAppFn.constName? "result.Result.Err" then
      if let some (_, _, errE) := st.resultMap.get? rhs.fvarId! then
        if lhs.getAppArgs.back!.consumeMData == Expr.bvar 0 then return some errE else return none
      else return none
    else if lhs.isFVar && (isCoreName rhs.getAppFn.constName? "option.Option.Some" || rhs.getAppFn.constName? == some ``Option.some) then
      if let some (_, valE) := st.optionMap.get? lhs.fvarId! then
        if rhs.getAppArgs.back!.consumeMData == Expr.bvar 0 then return some valE else return none
      else return none
    else if rhs.isFVar && (isCoreName lhs.getAppFn.constName? "option.Option.Some" || lhs.getAppFn.constName? == some ``Option.some) then
      if let some (_, valE) := st.optionMap.get? rhs.fvarId! then
        if lhs.getAppArgs.back!.consumeMData == Expr.bvar 0 then return some valE else return none
      else return none
    else if lhs == Expr.bvar 0 && !rhs.hasLooseBVars then
      return some rhs
    else if rhs == Expr.bvar 0 && !lhs.hasLooseBVars then
      return some lhs
    else return none
  else if fn.constName? == some ``And && args.size == 2 then
    if let some w ← findExistWitness? args[0]! then return some w
    else return ← findExistWitness? args[1]!
  else return none

partial def findRustMExistWitness? (e : Expr) : AuditM (Option (Expr × Expr)) := do
  let cur ← normalizeHead e
  let fn := cur.getAppFn
  let args := cur.getAppArgs
  if fn.constName? == some ``Eq && args.size == 3 then
    let lhs ← normalizeHead args[1]!
    let rhs ← normalizeHead args[2]!
    if (rhs.getAppFn.constName? == some `Aeneas.Std.RustM.ok || rhs.getAppFn.constName? == some `Aeneas.Std.Result.ok) && rhs.getAppArgs.size == 2 then
      if rhs.getArg! 1 == Expr.bvar 0 && !lhs.hasLooseBVars then
        return some (lhs, mkConst ``True)
    if (lhs.getAppFn.constName? == some `Aeneas.Std.RustM.ok || lhs.getAppFn.constName? == some `Aeneas.Std.Result.ok) && lhs.getAppArgs.size == 2 then
      if lhs.getArg! 1 == Expr.bvar 0 && !rhs.hasLooseBVars then
        return some (rhs, mkConst ``True)
    return none
  else if fn.constName? == some ``And && args.size == 2 then
    if let some (prog, a') ← findRustMExistWitness? args[0]! then
      return some (prog, mkApp2 (mkConst ``And) a' args[1]!)
    if let some (prog, b') ← findRustMExistWitness? args[1]! then
      return some (prog, mkApp2 (mkConst ``And) args[0]! b')
    return none
  else return none

partial def reduceExprStep? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  if e.isHeadBetaTarget then return some e.headBeta
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  if let .proj typeName idx struct := e then
    if typeName != ``Bind && typeName != ``Pure && typeName != ``Monad && typeName != ``MonadLift && typeName != ``MonadLiftT then
      if let some r ← withTransparency .all (reduceProj? e) then return some r
      let struct' ← normalizeHead struct
      if struct' != struct then
        return some (.proj typeName idx struct')
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .proj typeName _ _ := fn then
    if typeName != ``Bind && typeName != ``Pure && typeName != ``Monad && typeName != ``MonadLift && typeName != ``MonadLiftT then
      if let some r ← withTransparency .all (reduceProj? fn) then return some (mkAppN r args)
  if fn.constName? == some ``List.casesOn && args.size >= 5 then
    let l ← normalizeHead args[2]!
    let rest := args.extract 5 args.size
    if l.getAppFn.constName? == some ``List.nil then
      return some (mkAppN args[3]! rest).headBeta
    if l.isAppOfArity ``List.cons 3 then
      let applied := mkApp2 args[4]! (l.getArg! 1) (l.getArg! 2)
      return some (mkAppN applied rest).headBeta
  if fn.constName? == some ``Prod.fst && args.size == 3 then
    let p ← normalizeHead args[2]!
    if p.isAppOfArity ``Prod.mk 4 then return some (p.getArg! 2)
  if fn.constName? == some ``Prod.snd && args.size == 3 then
    let p ← normalizeHead args[2]!
    if p.isAppOfArity ``Prod.mk 4 then return some (p.getArg! 3)
  if fn.constName? == some ``Subtype.val && args.size == 3 then
    let sub ← normalizeHead args[2]!
    if sub.isAppOfArity ``Subtype.mk 4 then return some (sub.getArg! 2)
  if (fn.constName? == some ``Prod.casesOn || fn.constName? == some ``Prod.rec) && args.size >= 5 then
    let isRec := fn.constName? == some ``Prod.rec
    let p ← normalizeHead (if isRec then args[4]! else args[3]!)
    let f := if isRec then args[3]! else args[4]!
    if p.isAppOfArity ``Prod.mk 4 then
      let applied := mkApp2 f (p.getArg! 2) (p.getArg! 3)
      return some (mkAppN applied (args.extract 5 args.size)).headBeta
  if (fn.constName? == some `Aeneas.Std.Array.index_usize ||
      fn.constName? == some ``GetElem?.getElem! ||
      fn.constName? == some ``GetElem.getElem) && args.size >= 4 then
    for i in [0 : args.size - 1] do
      let candArr ← normalizeHead args[i]!
      if candArr.isAppOfArity ``Subtype.mk 4 then
        for j in [i + 1 : args.size] do
          if let some idxVal ← tryEvalClosedInt? args[j]! then
            if idxVal >= 0 then
              if let some elem ← extractListElemAt? (candArr.getArg! 2) idxVal.toNat then
                return some elem
  if fn.constName? == some `Aeneas.Std.Array.set && args.size == 5 then
    let arr ← normalizeHead args[2]!
    if arr.isAppOfArity ``Subtype.mk 4 then
      if let some idxVal ← tryEvalClosedInt? args[3]! then
        if idxVal >= 0 then
          if let some list' ← replaceListElemAt? (arr.getArg! 2) idxVal.toNat args[4]! then
            return some (mkApp4 arr.getAppFn (arr.getArg! 0) (arr.getArg! 1) list' (arr.getArg! 3))
  if let .const n _ := fn then
    let env ← getEnv
    if shouldUnfoldHelper n then
      if let some u ← withTransparency .all (unfoldDefinition? e) then return some u
      if !args.isEmpty then
        let args' ← args.mapM normalizeHead
        if args' != args then
          let e' := mkAppN fn args'
          if let some u ← withTransparency .all (unfoldDefinition? e') then return some u
          return some e'
    else if env.isProjectionFn n && args.size >= 1 then
      let majorIdx := args.size - 1
      let major ← normalizeHead args[majorIdx]!
      if major.getAppFn.isConst && (env.find? major.getAppFn.constName! matches some (.ctorInfo _)) then
        let e' := mkAppN fn (args.set! majorIdx major)
        if let some u ← withTransparency .all (unfoldDefinition? e') then
          return some u.headBeta
  return none

partial def normalizeHead (e : Expr) (fuel : Nat := 128) : MetaM Expr := do
  if fuel == 0 then return e.consumeMData
  if let some e' ← reduceExprStep? e then
    normalizeHead e' (fuel - 1)
  else
    return e.consumeMData

partial def lowerArgs (args : Array Expr) (fuel : Nat) : AuditM (Array Json) := do
  let mut out : Array Json := #[]
  for a in args do
    let a ← normalizeHead a
    let rawTy ← inferType a
    if (← isProp rawTy) || rawTy.isSort || (← isClass? rawTy).isSome then continue
    let ty ← withTransparency .all (whnf rawTy)
    if (← isProp ty) || ty.isSort || (← isClass? ty).isSome then continue
    if ty.isForall && ty.getForallBody.isSort then continue
    let fnName := ty.getAppFn.constName?
    if fnName == some `Aeneas.Std.UScalarTy || fnName == some `Aeneas.Std.IScalarTy then continue
    let tStr := (← ppExpr ty).pretty
    let isDataStruct := tStr.startsWith "core.ops.range." || tStr.startsWith "CoreModels.core.ops.range." ||
                        tStr.startsWith "core.cmp.Ordering" || tStr.startsWith "CoreModels.core.cmp.Ordering"
    if !isDataStruct && (hasSubstr tStr "Insts." || tStr.startsWith "core.ops." || tStr.startsWith "core.cmp." ||
       tStr.startsWith "core.convert." || tStr.startsWith "core.slice.index." ||
       tStr.startsWith "CoreModels.core.ops." || tStr.startsWith "CoreModels.core.cmp." ||
       tStr.startsWith "CoreModels.core.convert." || tStr.startsWith "CoreModels.core.slice.index.") then
      continue
    out := out.push (← lowerTerm a (fuel - 1))
  return out

partial def resolveOptionScrut (scrut : Expr) (valTy : Expr) (fuel : Nat)
    (k : Json → Expr → AuditM Json) : AuditM Json := do
  let scrut ← normalizeHead scrut
  let st ← get
  if scrut.isFVar then
    if let some (isSomeJson, valExpr) := st.optionMap.get? scrut.fvarId! then
      return ← k isSomeJson valExpr
  let sFn := scrut.getAppFn
  let sArgs := scrut.getAppArgs
  if (isCoreName sFn.constName? "option.Option.Some" || sFn.constName? == some ``Option.some) && sArgs.size >= 2 then
    return ← k (node "true") sArgs.back!
  if isCoreName sFn.constName? "option.Option.None" || sFn.constName? == some ``Option.none then
    let idx ← freshIndex
    return ← withLocalDeclD ((Name.mkSimple "_none_val").appendIndexAfter idx) valTy fun dummyFv =>
      k (node "false") dummyFv
  let fnStr ← match sFn.constName? with | some n => pure n.toString | none => do pure (← ppExpr sFn).pretty
  let lArgs ← lowerArgs sArgs (fuel - 1)
  let isSomeJson := ufNode "call_ok" fnStr lArgs 0 "bool"
  expandSymbolicValue valTy
    (fun leafIdx sort => pure (ufNode "call_val" fnStr lArgs leafIdx sort))
    (fun valExpr => k isSomeJson valExpr)

partial def resolveResultScrut (scrut : Expr) (okTy errTy : Expr) (fuel : Nat)
    (k : Json → Expr → Expr → AuditM Json) : AuditM Json := do
  let scrut ← normalizeHead scrut
  let st ← get
  if scrut.isFVar then
    if let some (isOkJson, okExpr, errExpr) := st.resultMap.get? scrut.fvarId! then
      return ← k isOkJson okExpr errExpr
  let sFn := scrut.getAppFn
  let sArgs := scrut.getAppArgs
  if isCoreName sFn.constName? "result.Result.Ok" && sArgs.size >= 3 then
    let idx ← freshIndex
    return ← withLocalDeclD ((Name.mkSimple "_dummy_err").appendIndexAfter idx) errTy fun dummyErr =>
      k (node "true") sArgs.back! dummyErr
  if isCoreName sFn.constName? "result.Result.Err" && sArgs.size >= 3 then
    let idx ← freshIndex
    return ← withLocalDeclD ((Name.mkSimple "_dummy_ok").appendIndexAfter idx) okTy fun dummyOk =>
      k (node "false") dummyOk sArgs.back!
  let fnStr ← match sFn.constName? with | some n => pure n.toString | none => do pure (← ppExpr sFn).pretty
  let lArgs ← lowerArgs sArgs (fuel - 1)
  let isOkJson := ufNode "call_ok" fnStr lArgs 0 "bool"
  expandSymbolicValue okTy
    (fun leafIdx sort => pure (ufNode "call_val" fnStr lArgs (leafIdx + 1) sort))
    (fun okExpr =>
      expandSymbolicValue errTy
        (fun leafIdx sort => pure (ufNode "call_err" fnStr lArgs (leafIdx + 1) sort))
        (fun errExpr => k isOkJson okExpr errExpr))

partial def evalRustM (prog : Expr) (k : Expr → AuditM Json) (fuel : Nat) : AuditM Json := do
  if fuel == 0 then throwError "unsupported: evalRustM fuel exhausted"
  let prog ← normalizeHead prog
  if let .letE _ _ val body _ := prog then
    return ← evalRustM (body.instantiate1 val) k (fuel - 1)
  let fn := prog.getAppFn
  let args := prog.getAppArgs
  let name := fn.constName?
  let isBindProj := match fn with | .proj ``Bind _ _ => true | _ => false
  let isPureProj := match fn with | .proj ``Pure _ _ => true | _ => false
  if (name == some `Aeneas.Std.RustM.ok || name == some `Aeneas.Std.Result.ok || name == some ``Pure.pure || isPureProj) && args.size >= 2 then
    return ← k args.back!
  if name == some `Aeneas.Std.RustM.fail || name == some `Aeneas.Std.Result.fail || name == some `Aeneas.Std.Result.div then
    return node "false"
  if (name == some `Aeneas.Std.WP.lift || name == some `Aeneas.Std.lift || name == some ``MonadLift.monadLift || name == some ``MonadLiftT.monadLift) && args.size >= 2 then
    return ← k args.back!
  if (name == some ``Bind.bind || name == some `Aeneas.Std.bind || isBindProj) && args.size >= 2 then
    let ma := args[args.size - 2]!
    let cont := args[args.size - 1]!
    return ← evalRustM ma (fun v => evalRustM (mkApp cont v).headBeta k (fuel - 1)) (fuel - 1)
  if name == some ``ite && args.size == 5 then
    return node "if" #[← lowerProp args[1]! (fuel - 1), ← evalRustM args[3]! k (fuel - 1), ← evalRustM args[4]! k (fuel - 1)]
  if name == some ``dite && args.size == 5 then
    let c := args[1]!
    let tBr ← withLocalDeclD `_h c fun h => evalRustM (mkApp args[3]! h).headBeta k (fuel - 1)
    let fBr ← withLocalDeclD `_nh (mkNot c) fun h => evalRustM (mkApp args[4]! h).headBeta k (fuel - 1)
    return node "if" #[← lowerProp c (fuel - 1), tBr, fBr]
  if (isCoreName name "cmp.Ordering.casesOn" || isCoreName name "cmp.Ordering.rec") && args.size >= 5 then
    let isRec := isCoreName name "cmp.Ordering.rec"
    let scrutExpr := if isRec then args[4]! else args[1]!
    let lessBr := if isRec then args[1]! else args[2]!
    let eqBr := if isRec then args[2]! else args[3]!
    let gtBr := if isRec then args[3]! else args[4]!
    let scrut ← lowerTerm scrutExpr (fuel - 1)
    let rest := args.extract 5 args.size
    let bLess ← evalRustM (mkAppN lessBr rest).headBeta k (fuel - 1)
    let bEq ← evalRustM (mkAppN eqBr rest).headBeta k (fuel - 1)
    let bGt ← evalRustM (mkAppN gtBr rest).headBeta k (fuel - 1)
    return node "if" #[
      node "eq" #[scrut, intJson (-1)],
      bLess,
      node "if" #[node "eq" #[scrut, intJson 0], bEq, bGt]
    ]
  if (isCoreName name "option.Option.casesOn" || name == some ``Option.casesOn ||
      isCoreName name "option.Option.rec" || name == some ``Option.rec) && args.size >= 5 then
    let isRec := isCoreName name "option.Option.rec" || name == some ``Option.rec
    let valTy := args[0]!
    let scrut := if isRec then args[4]! else args[2]!
    let noneBr := if isRec then args[2]! else args[3]!
    let someBr := if isRec then args[3]! else args[4]!
    let rest := args.extract 5 args.size
    return ← resolveOptionScrut scrut valTy (fuel - 1) fun isSomeJson valExpr => do
      let bNone ← evalRustM (mkAppN noneBr rest).headBeta k (fuel - 1)
      let bSome ← evalRustM (mkAppN (mkApp someBr valExpr) rest).headBeta k (fuel - 1)
      return node "if" #[isSomeJson, bSome, bNone]
  if (isCoreName name "result.Result.casesOn" || isCoreName name "result.Result.rec") && args.size >= 6 then
    let isRec := isCoreName name "result.Result.rec"
    let okTy := args[0]!
    let errTy := args[1]!
    let scrut := if isRec then args[5]! else args[3]!
    let okBr := if isRec then args[3]! else args[4]!
    let errBr := if isRec then args[4]! else args[5]!
    let rest := args.extract 6 args.size
    return ← resolveResultScrut scrut okTy errTy (fuel - 1) fun isOkJson okExpr errExpr => do
      let bOk ← evalRustM (mkAppN (mkApp okBr okExpr) rest).headBeta k (fuel - 1)
      let bErr ← evalRustM (mkAppN (mkApp errBr errExpr) rest).headBeta k (fuel - 1)
      return node "if" #[isOkJson, bOk, bErr]
  if !prog.hasFVar && !prog.hasLooseBVars then
    let r ← withTransparency .all (whnf prog)
    if r.getAppFn.constName? == some `Aeneas.Std.RustM.ok && r.getAppArgs.size == 2 then
      return ← k (r.getArg! 1)
    if r.getAppFn.constName? == some `Aeneas.Std.RustM.fail then
      return node "false"
  if isCoreName name "cmp.Ordering.reverse" && args.size == 1 then
    if let some u ← withTransparency .all (unfoldDefinition? prog) then
      return ← evalRustM u k (fuel - 1)
  if isCoreName name "option.Option.unwrap" && args.size >= 2 then
    let valTy := args[0]!
    let opt := args.back!
    return ← resolveOptionScrut opt valTy (fuel - 1) fun isSomeJson valExpr => do
      return node "and" #[isSomeJson, ← k valExpr]
  if (isCoreName name "option.Option.is_some" || isCoreName name "option.Option.is_none") && args.size >= 2 then
    let valTy := args[0]!
    let opt := args.back!
    return ← resolveOptionScrut opt valTy (fuel - 1) fun isSomeJson _ => do
      let bJson := if isCoreName name "option.Option.is_some" then isSomeJson else node "not" #[isSomeJson]
      let idx ← freshIndex
      withLocalDeclD ((Name.mkSimple "_isopt").appendIndexAfter idx) (mkConst ``Bool) fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! bJson }
        k fv
  if isCoreName name "result.Result.unwrap" && args.size >= 3 then
    return ← resolveResultScrut args.back! args[0]! args[1]! (fuel - 1) fun isOkJson okExpr _ => do
      return node "and" #[isOkJson, ← k okExpr]
  if isCoreName name "result.Result.unwrap_err" && args.size >= 3 then
    return ← resolveResultScrut args.back! args[0]! args[1]! (fuel - 1) fun isOkJson _ errExpr => do
      return node "and" #[node "not" #[isOkJson], ← k errExpr]
  if (isCoreName name "result.Result.is_ok" || isCoreName name "result.Result.is_err") && args.size >= 3 then
    return ← resolveResultScrut args.back! args[0]! args[1]! (fuel - 1) fun isOkJson _ _ => do
      let bJson := if isCoreName name "result.Result.is_ok" then isOkJson else node "not" #[isOkJson]
      let idx ← freshIndex
      withLocalDeclD ((Name.mkSimple "_isok").appendIndexAfter idx) (mkConst ``Bool) fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! bJson }
        k fv
  -- Monadic scalar arithmetic & CoreModels scalar traits
  let progTy ← withTransparency .all (whnf (← inferType prog))
  let retTy := if progTy.getAppArgs.size >= 1 then progTy.getAppArgs.back! else mkConst ``Nat
  if (name == some ``HAdd.hAdd || name == some ``HSub.hSub || name == some ``HMul.hMul) && args.size >= 2 then
    if ← isAtomicScalarType retTy then
      let sort ← detectSort retTy
      let (minVal, maxVal, _) := scalarBounds sort
      let op := if name == some ``HAdd.hAdd then "add" else if name == some ``HSub.hSub then "sub" else "mul"
      let lhs ← lowerTerm args[args.size - 2]! (fuel - 1)
      let rhs ← lowerTerm args[args.size - 1]! (fuel - 1)
      let valJson := node op #[lhs, rhs]
      let okCond := node "and" #[node "le" #[intJson minVal, valJson], node "le" #[valJson, intJson maxVal]]
      let idx ← freshIndex
      let contJson ← withLocalDeclD ((Name.mkSimple "_arith").appendIndexAfter idx) retTy fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! valJson }
        k fv
      return node "and" #[okCond, contJson]
  if (name == some ``HDiv.hDiv || name == some ``HMod.hMod) && args.size >= 2 then
    if ← isAtomicScalarType retTy then
      let sort ← detectSort retTy
      let (minVal, _, _) := scalarBounds sort
      let op := if name == some ``HDiv.hDiv then "div" else "mod"
      let lhs ← lowerTerm args[args.size - 2]! (fuel - 1)
      let rhs ← lowerTerm args[args.size - 1]! (fuel - 1)
      let valJson := node op #[lhs, rhs]
      let nzCond := node "not" #[node "eq" #[rhs, intJson 0]]
      let okCond := if sort.startsWith "i" then
        node "and" #[nzCond, node "not" #[node "and" #[node "eq" #[lhs, intJson minVal], node "eq" #[rhs, intJson (-1)]]]]
      else nzCond
      let idx ← freshIndex
      let contJson ← withLocalDeclD ((Name.mkSimple "_divmod").appendIndexAfter idx) retTy fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! valJson }
        k fv
      return node "and" #[okCond, contJson]
  if (name == some ``HShiftLeft.hShiftLeft || name == some ``HShiftRight.hShiftRight) && args.size >= 2 then
    if ← isAtomicScalarType retTy then
      let sort ← detectSort retTy
      let (_, _, nBits) := scalarBounds sort
      let op := if name == some ``HShiftLeft.hShiftLeft then "shl" else "shr"
      let lhs ← lowerTerm args[args.size - 2]! (fuel - 1)
      let rhs ← lowerTerm args[args.size - 1]! (fuel - 1)
      let rawJson := node op #[lhs, rhs]
      let valJson := if op == "shl" && sort.startsWith "u" then
        node "mod" #[rawJson, intJson ((2 : Int) ^ nBits.toNat)]
      else rawJson
      let okCond := node "and" #[node "le" #[intJson 0, rhs], node "lt" #[rhs, intJson nBits]]
      let idx ← freshIndex
      let contJson ← withLocalDeclD ((Name.mkSimple "_shift").appendIndexAfter idx) retTy fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! valJson }
        k fv
      return node "and" #[okCond, contJson]
  if (name == some ``HAnd.hAnd || name == some ``HOr.hOr || name == some ``HXor.hXor) && args.size >= 2 then
    if ← isAtomicScalarType retTy then
      let op := if name == some ``HAnd.hAnd then "bitand" else if name == some ``HOr.hOr then "bitor" else "bitxor"
      let lhs ← lowerTerm args[args.size - 2]! (fuel - 1)
      let rhs ← lowerTerm args[args.size - 1]! (fuel - 1)
      let valJson := node op #[lhs, rhs]
      let idx ← freshIndex
      return ← withLocalDeclD ((Name.mkSimple "_bitop").appendIndexAfter idx) retTy fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! valJson }
        k fv
  let fnStr ← match name with | some n => pure n.toString | none => do pure (← ppExpr fn).pretty
  if (fnStr.endsWith ".CoreOpsDerefDerefSlice.deref" || fnStr.endsWith ".CoreOpsDerefMutDerefMutSlice.deref_mut" ||
      fnStr == "Aeneas.Std.Array.to_slice" || fnStr == "Aeneas.Std.Vec.deref") && args.size >= 1 then
    return ← k args.back!
  if hasSubstr fnStr ".Insts.CoreConvertFrom" && fnStr.endsWith ".from" && args.size >= 1 then
    if (← isAtomicScalarType retTy) && (← isAtomicScalarType (← inferType args.back!)) then
      let vJson ← lowerTerm args.back! (fuel - 1)
      let idx ← freshIndex
      return ← withLocalDeclD ((Name.mkSimple "_from").appendIndexAfter idx) retTy fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! vJson }
        k fv
  if (fnStr.startsWith "CoreModels.core.num." || fnStr.startsWith "core.num.") && fnStr.endsWith ".pow" && args.size == 2 then
    if ← isAtomicScalarType retTy then
      let sort ← detectSort retTy
      let (minVal, maxVal, _) := scalarBounds sort
      let lhs ← lowerTerm args[0]! (fuel - 1)
      let rhs ← lowerTerm args[1]! (fuel - 1)
      let valJson := node "pow" #[lhs, rhs]
      let okCond := node "and" #[node "le" #[intJson minVal, valJson], node "le" #[valJson, intJson maxVal]]
      let idx ← freshIndex
      let contJson ← withLocalDeclD ((Name.mkSimple "_pow").appendIndexAfter idx) retTy fun fv => do
        modify fun s => { s with subst := s.subst.insert fv.fvarId! valJson }
        k fv
      return node "and" #[okCond, contJson]
  if (fnStr.startsWith "CoreModels.core." || fnStr.startsWith "core.") && args.size == 2 then
    if (← isAtomicScalarType (← inferType args[0]!)) && (← isAtomicScalarType (← inferType args[1]!)) then
      if fnStr.endsWith ".eq" || fnStr.endsWith ".ne" || fnStr.endsWith ".lt" || fnStr.endsWith ".le" || fnStr.endsWith ".gt" || fnStr.endsWith ".ge" then
        let a ← lowerTerm args[0]! (fuel - 1)
        let b ← lowerTerm args[1]! (fuel - 1)
        let bJson :=
          if fnStr.endsWith ".eq" then node "eq" #[a, b]
          else if fnStr.endsWith ".ne" then node "not" #[node "eq" #[a, b]]
          else if fnStr.endsWith ".lt" then node "lt" #[a, b]
          else if fnStr.endsWith ".le" then node "le" #[a, b]
          else if fnStr.endsWith ".gt" then node "lt" #[b, a]
          else node "le" #[b, a]
        let idx ← freshIndex
        return ← withLocalDeclD ((Name.mkSimple "_cmpb").appendIndexAfter idx) (mkConst ``Bool) fun fv => do
          modify fun s => { s with subst := s.subst.insert fv.fvarId! bJson }
          k fv
      if fnStr.endsWith ".cmp" then
        let a ← lowerTerm args[0]! (fuel - 1)
        let b ← lowerTerm args[1]! (fuel - 1)
        let ordJson := node "if" #[node "lt" #[a, b], intJson (-1), node "if" #[node "eq" #[a, b], intJson 0, intJson 1]]
        let idx ← freshIndex
        return ← withLocalDeclD ((Name.mkSimple "_cmp").appendIndexAfter idx) retTy fun fv => do
          modify fun s => { s with subst := s.subst.insert fv.fvarId! ordJson }
          k fv
  -- Generic monadic call: `fn args : RustM retTy`
  let lArgs ← lowerArgs args (fuel - 1)
  let okCond := ufNode "call_ok" fnStr lArgs 0 "bool"
  let contJson ← expandSymbolicValue retTy
    (fun leafIdx sort => pure (ufNode "call_val" fnStr lArgs leafIdx sort))
    k
  return node "and" #[okCond, contJson]

partial def lowerEq (lhs rhs : Expr) (fuel : Nat) : AuditM Json := do
  if fuel == 0 then throwError "unsupported: lowerEq fuel exhausted"
  let lhs ← normalizeHead lhs
  let rhs ← normalizeHead rhs
  let st ← get
  -- Result equality with Result.Ok / Result.Err
  if lhs.isFVar then
    if let some (isOkJson, okExpr, errExpr) := st.resultMap.get? lhs.fvarId! then
      if isCoreName rhs.getAppFn.constName? "result.Result.Ok" then
        return node "and" #[isOkJson, ← lowerEq okExpr rhs.getAppArgs.back! (fuel - 1)]
      if isCoreName rhs.getAppFn.constName? "result.Result.Err" then
        return node "and" #[node "not" #[isOkJson], ← lowerEq errExpr rhs.getAppArgs.back! (fuel - 1)]
      if rhs.isFVar then
        if let some (isOk2, ok2, err2) := st.resultMap.get? rhs.fvarId! then
          return node "and" #[
            node "iff" #[isOkJson, isOk2],
            node "if" #[isOkJson, ← lowerEq okExpr ok2 (fuel - 1), ← lowerEq errExpr err2 (fuel - 1)]
          ]
    if let some (isSomeJson, valExpr) := st.optionMap.get? lhs.fvarId! then
      if isCoreName rhs.getAppFn.constName? "option.Option.Some" || rhs.getAppFn.constName? == some ``Option.some then
        return node "and" #[isSomeJson, ← lowerEq valExpr rhs.getAppArgs.back! (fuel - 1)]
      if isCoreName rhs.getAppFn.constName? "option.Option.None" || rhs.getAppFn.constName? == some ``Option.none then
        return node "not" #[isSomeJson]
      if rhs.isFVar then
        if let some (isSome2, val2) := st.optionMap.get? rhs.fvarId! then
          return node "and" #[
            node "iff" #[isSomeJson, isSome2],
            node "implies" #[isSomeJson, ← lowerEq valExpr val2 (fuel - 1)]
          ]
  if rhs.isFVar && (st.resultMap.contains rhs.fvarId! || st.optionMap.contains rhs.fvarId!) then
    return ← lowerEq rhs lhs (fuel - 1)
  -- Result equality when lhs or rhs is Result.Ok / Result.Err and the other is a Result term
  if isCoreName rhs.getAppFn.constName? "result.Result.Ok" && rhs.getAppArgs.size >= 3 then
    let rArgs := rhs.getAppArgs
    return ← resolveResultScrut lhs rArgs[0]! rArgs[1]! (fuel - 1) fun isOkJson okExpr _ => do
      return node "and" #[isOkJson, ← lowerEq okExpr rArgs.back! (fuel - 1)]
  if isCoreName rhs.getAppFn.constName? "result.Result.Err" && rhs.getAppArgs.size >= 3 then
    let rArgs := rhs.getAppArgs
    return ← resolveResultScrut lhs rArgs[0]! rArgs[1]! (fuel - 1) fun isOkJson _ errExpr => do
      return node "and" #[node "not" #[isOkJson], ← lowerEq errExpr rArgs.back! (fuel - 1)]
  if isCoreName lhs.getAppFn.constName? "result.Result.Ok" || isCoreName lhs.getAppFn.constName? "result.Result.Err" then
    return ← lowerEq rhs lhs (fuel - 1)
  -- Option equality when lhs or rhs is Option.some / Option.none and the other is an Option term
  if isCoreName rhs.getAppFn.constName? "option.Option.Some" || rhs.getAppFn.constName? == some ``Option.some then
    let valTy ← inferType rhs.getAppArgs.back!
    return ← resolveOptionScrut lhs valTy (fuel - 1) fun isSomeJson valExpr => do
      return node "and" #[isSomeJson, ← lowerEq valExpr rhs.getAppArgs.back! (fuel - 1)]
  if isCoreName rhs.getAppFn.constName? "option.Option.None" || rhs.getAppFn.constName? == some ``Option.none then
    let valTy := if rhs.getAppArgs.size >= 1 then rhs.getAppArgs[0]! else mkConst ``Nat
    return ← resolveOptionScrut lhs valTy (fuel - 1) fun isSomeJson _ => do
      return node "not" #[isSomeJson]
  if isCoreName lhs.getAppFn.constName? "option.Option.Some" || lhs.getAppFn.constName? == some ``Option.some ||
     isCoreName lhs.getAppFn.constName? "option.Option.None" || lhs.getAppFn.constName? == some ``Option.none then
    return ← lowerEq rhs lhs (fuel - 1)
  -- Prod equality
  if lhs.isAppOfArity ``Prod.mk 4 && rhs.isAppOfArity ``Prod.mk 4 then
    return node "and" #[← lowerEq (lhs.getArg! 2) (rhs.getArg! 2) (fuel - 1), ← lowerEq (lhs.getArg! 3) (rhs.getArg! 3) (fuel - 1)]
  -- Subtype equality (e.g. Array)
  if lhs.isAppOfArity ``Subtype.mk 4 && rhs.isAppOfArity ``Subtype.mk 4 then
    return ← lowerEq (lhs.getArg! 2) (rhs.getArg! 2) (fuel - 1)
  -- Direct RustM ok/fail check: `run = ok val` or `run = fail .panic`
  if (rhs.getAppFn.constName? == some `Aeneas.Std.RustM.ok || rhs.getAppFn.constName? == some `Aeneas.Std.Result.ok) && rhs.getAppArgs.size == 2 then
    return ← evalRustM lhs (fun r => lowerEq r (rhs.getArg! 1) (fuel - 1)) (fuel - 1)
  if (lhs.getAppFn.constName? == some `Aeneas.Std.RustM.ok || lhs.getAppFn.constName? == some `Aeneas.Std.Result.ok) && lhs.getAppArgs.size == 2 then
    return ← evalRustM rhs (fun r => lowerEq (lhs.getArg! 1) r (fuel - 1)) (fuel - 1)
  if rhs.getAppFn.constName? == some `Aeneas.Std.RustM.fail || rhs.getAppFn.constName? == some `Aeneas.Std.Result.fail then
    let okRun ← evalRustM lhs (fun _ => pure (node "true")) (fuel - 1)
    return node "not" #[okRun]
  if lhs.getAppFn.constName? == some `Aeneas.Std.RustM.fail || lhs.getAppFn.constName? == some `Aeneas.Std.Result.fail then
    let okRun ← evalRustM rhs (fun _ => pure (node "true")) (fuel - 1)
    return node "not" #[okRun]
  -- Same constructor equality (e.g. structs, List.cons, Error enums)
  let fnL := lhs.getAppFn
  let fnR := rhs.getAppFn
  let env ← getEnv
  if fnL.isConst && fnR.isConst then
    let nL := fnL.constName!
    let nR := fnR.constName!
    let ciL := env.find? nL
    let ciR := env.find? nR
    if ciL matches some (.ctorInfo _) && ciR matches some (.ctorInfo _) then
      if nL != nR then return node "false"
      let some (.ctorInfo ci) := ciL | unreachable!
      let argsL := lhs.getAppArgs
      let argsR := rhs.getAppArgs
      if argsL.size == argsR.size && argsL.size >= ci.numParams then
        let mut conjs : Array Json := #[]
        for i in [ci.numParams : argsL.size] do
          conjs := conjs.push (← lowerEq argsL[i]! argsR[i]! (fuel - 1))
        if conjs.isEmpty then return node "true"
        let mut res := conjs[0]!
        for i in [1 : conjs.size] do
          res := node "and" #[res, conjs[i]!]
        return res
  -- Propositional or Bool equality with true/false
  if (← isProp lhs) || (← isProp rhs) then
    return node "iff" #[← lowerProp lhs (fuel - 1), ← lowerProp rhs (fuel - 1)]
  let lJson ← lowerTerm lhs (fuel - 1)
  let rJson ← lowerTerm rhs (fuel - 1)
  return node "eq" #[lJson, rJson]

partial def lowerProp (e : Expr) (fuel : Nat := 1024) : AuditM Json := do
  if fuel == 0 then throwError "unsupported: lowerProp fuel exhausted"
  let e ← normalizeHead e
  if let .letE _ _ val body _ := e then
    return ← lowerProp (body.instantiate1 val) (fuel - 1)
  let fn := e.getAppFn
  let args := e.getAppArgs
  let name := fn.constName?
  if name == some ``True then return node "true"
  if name == some ``False then return node "false"
  if name == some ``And && args.size == 2 then
    return node "and" #[← lowerProp args[0]! (fuel - 1), ← lowerProp args[1]! (fuel - 1)]
  if name == some ``Or && args.size == 2 then
    return node "or" #[← lowerProp args[0]! (fuel - 1), ← lowerProp args[1]! (fuel - 1)]
  if name == some ``Iff && args.size == 2 then
    return node "iff" #[← lowerProp args[0]! (fuel - 1), ← lowerProp args[1]! (fuel - 1)]
  if name == some ``Not && args.size == 1 then
    return node "not" #[← lowerProp args[0]! (fuel - 1)]
  if name == some ``ite && args.size == 5 then
    return node "if" #[← lowerProp args[1]! (fuel - 1), ← lowerProp args[3]! (fuel - 1), ← lowerProp args[4]! (fuel - 1)]
  if name == some ``dite && args.size == 5 then
    let c := args[1]!
    let tBr ← withLocalDeclD `_h c fun h => lowerProp (mkApp args[3]! h).headBeta (fuel - 1)
    let fBr ← withLocalDeclD `_nh (mkNot c) fun h => lowerProp (mkApp args[4]! h).headBeta (fuel - 1)
    return node "if" #[← lowerProp c (fuel - 1), tBr, fBr]
  if (isCoreName name "option.Option.casesOn" || name == some ``Option.casesOn ||
      isCoreName name "option.Option.rec" || name == some ``Option.rec) && args.size >= 5 then
    let isRec := isCoreName name "option.Option.rec" || name == some ``Option.rec
    let valTy := args[0]!
    let scrut := if isRec then args[4]! else args[2]!
    let noneBr := if isRec then args[2]! else args[3]!
    let someBr := if isRec then args[3]! else args[4]!
    let rest := args.extract 5 args.size
    return ← resolveOptionScrut scrut valTy (fuel - 1) fun isSomeJson valExpr => do
      let bNone ← lowerProp (mkAppN noneBr rest).headBeta (fuel - 1)
      let bSome ← lowerProp (mkAppN (mkApp someBr valExpr) rest).headBeta (fuel - 1)
      return node "if" #[isSomeJson, bSome, bNone]
  if (isCoreName name "result.Result.casesOn" || isCoreName name "result.Result.rec") && args.size >= 6 then
    let isRec := isCoreName name "result.Result.rec"
    let okTy := args[0]!
    let errTy := args[1]!
    let scrut := if isRec then args[5]! else args[3]!
    let okBr := if isRec then args[3]! else args[4]!
    let errBr := if isRec then args[4]! else args[5]!
    let rest := args.extract 6 args.size
    return ← resolveResultScrut scrut okTy errTy (fuel - 1) fun isOkJson okExpr errExpr => do
      let bOk ← lowerProp (mkAppN (mkApp okBr okExpr) rest).headBeta (fuel - 1)
      let bErr ← lowerProp (mkAppN (mkApp errBr errExpr) rest).headBeta (fuel - 1)
      return node "if" #[isOkJson, bOk, bErr]
  if (name == some `Aeneas.Std.Result.casesOn || name == some `Aeneas.Std.Result.rec) && args.size >= 6 then
    let isRec := name == some `Aeneas.Std.Result.rec
    let scrut := if isRec then args[5]! else args[2]!
    let okBr := if isRec then args[2]! else args[3]!
    let failBr := if isRec then args[3]! else args[4]!
    let rest := args.extract 6 args.size
    let okRun ← evalRustM scrut (fun _ => pure (node "true")) (fuel - 1)
    let bOk ← evalRustM scrut (fun v => lowerProp (mkAppN (mkApp okBr v) rest).headBeta (fuel - 1)) (fuel - 1)
    let bFail ← withLocalDeclD `_err (mkConst `Aeneas.Std.Error) fun errFv =>
      lowerProp (mkAppN (mkApp failBr errFv) rest).headBeta (fuel - 1)
    return node "if" #[okRun, bOk, bFail]
  if (isCoreName name "cmp.Ordering.casesOn" || isCoreName name "cmp.Ordering.rec") && args.size >= 5 then
    let isRec := isCoreName name "cmp.Ordering.rec"
    let scrutExpr := if isRec then args[4]! else args[1]!
    let lessBr := if isRec then args[1]! else args[2]!
    let eqBr := if isRec then args[2]! else args[3]!
    let gtBr := if isRec then args[3]! else args[4]!
    let scrut ← lowerTerm scrutExpr (fuel - 1)
    let rest := args.extract 5 args.size
    let bLess ← lowerProp (mkAppN lessBr rest).headBeta (fuel - 1)
    let bEq ← lowerProp (mkAppN eqBr rest).headBeta (fuel - 1)
    let bGt ← lowerProp (mkAppN gtBr rest).headBeta (fuel - 1)
    return node "if" #[
      node "eq" #[scrut, intJson (-1)],
      bLess,
      node "if" #[node "eq" #[scrut, intJson 0], bEq, bGt]
    ]
  if name == some `Aeneas.Std.WP.spec && args.size == 3 then
    let prog := args[1]!
    let post := args[2]!
    return ← evalRustM prog (fun v => lowerProp (mkApp post v).headBeta (fuel - 1)) (fuel - 1)
  if name == some ``Eq && args.size == 3 then
    if (← isProp args[1]!) || (← isProp args[2]!) then
      return node "iff" #[← lowerProp args[1]! (fuel - 1), ← lowerProp args[2]! (fuel - 1)]
    return ← lowerEq args[1]! args[2]! (fuel - 1)
  if name == some ``Ne && args.size == 3 then
    return node "not" #[← lowerEq args[1]! args[2]! (fuel - 1)]
  if (name == some ``LE.le || name == some ``Nat.le || name == some ``Int.le) && args.size >= 2 then
    return node "le" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``LT.lt || name == some ``Nat.lt || name == some ``Int.lt) && args.size >= 2 then
    return node "lt" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if name == some ``GE.ge && args.size >= 2 then
    return node "le" #[← lowerTerm args[args.size - 1]! (fuel - 1), ← lowerTerm args[args.size - 2]! (fuel - 1)]
  if name == some ``GT.gt && args.size >= 2 then
    return node "lt" #[← lowerTerm args[args.size - 1]! (fuel - 1), ← lowerTerm args[args.size - 2]! (fuel - 1)]
  if (name == some ``Membership.mem || name == some ``List.Mem) && args.size >= 2 then
    let a1 := args[args.size - 2]!
    let a2 := args[args.size - 1]!
    if let some elems ← extractListElems? a1 then
      if elems.isEmpty then return node "false"
      let mut res ← lowerEq a2 elems[0]! (fuel - 1)
      for i in [1 : elems.size] do
        res := node "or" #[res, ← lowerEq a2 elems[i]! (fuel - 1)]
      return res
    if let some elems ← extractListElems? a2 then
      if elems.isEmpty then return node "false"
      let mut res ← lowerEq a1 elems[0]! (fuel - 1)
      for i in [1 : elems.size] do
        res := node "or" #[res, ← lowerEq a1 elems[i]! (fuel - 1)]
      return res
  if name == some ``Exists && args.size == 2 then
    let dom := args[0]!
    let lam := args[1]!
    if let .lam _ _ body _ := lam then
      if let some w ← findExistWitness? body then
        return ← lowerProp (body.instantiate1 w) (fuel - 1)
      if let some (prog, restBody) ← findRustMExistWitness? body then
        return ← evalRustM prog (fun v => lowerProp (restBody.instantiate1 v) (fuel - 1)) (fuel - 1)
    let d ← modifyGet fun s => (s.qDepth, { s with qDepth := s.qDepth + 1 })
    let qVarsRef ← IO.mkRef (#[] : Array Json)
    let res ← expandSymbolicValue dom
      (fun idx sort => do
        let vname := s!"_ex_{d}_{idx}"
        qVarsRef.modify fun a => a.push (Json.mkObj [("name", toJson vname), ("sort", toJson sort)])
        return Json.mkObj [("var", toJson vname), ("sort", toJson sort)])
      (fun w => lowerProp (mkApp lam w).headBeta (fuel - 1))
    modify fun s => { s with qDepth := d }
    let qVars ← qVarsRef.get
    return Json.mkObj [("op", toJson "exists"), ("vars", Json.arr qVars), ("body", res)]
  if e.isForall then
    let .forallE bName dom body _ := e | unreachable!
    if ← isProp dom then
      let lhs ← lowerProp dom (fuel - 1)
      let rhs ← withLocalDeclD bName dom fun h => lowerProp (body.instantiate1 h) (fuel - 1)
      return node "implies" #[lhs, rhs]
    else
      let d ← modifyGet fun s => (s.qDepth, { s with qDepth := s.qDepth + 1 })
      let qVarsRef ← IO.mkRef (#[] : Array Json)
      let res ← expandSymbolicValue dom
        (fun idx sort => do
          let qname := s!"_q_{d}_{idx}"
          qVarsRef.modify fun a => a.push (Json.mkObj [("name", toJson qname), ("sort", toJson sort)])
          return Json.mkObj [("var", toJson qname), ("sort", toJson sort)])
        (fun qv => lowerProp (body.instantiate1 qv) (fuel - 1))
      modify fun s => { s with qDepth := d }
      let qVars ← qVarsRef.get
      return Json.mkObj [("op", toJson "forall"), ("vars", Json.arr qVars), ("body", res)]
  if e.isFVar then
    let st ← get
    if let some j := st.subst.get? e.fvarId! then return j
  -- Fallback: uninterpreted predicate / unfolded definition
  if let .const n _ := fn then
    if !(opaqueHelperNames.any (fun h => n.toString.endsWith ("." ++ h) || n.toString == h)) then
      if let some u ← withTransparency .all (unfoldDefinition? e) then
        return ← lowerProp u (fuel - 1)
  let lArgs ← lowerArgs args (fuel - 1)
  if fn.isFVar then
    let fnJson ← lowerTerm fn (fuel - 1)
    return ufNode "uf_prop" "app" (#[fnJson] ++ lArgs) 0 "bool"
  let fnStr ← match name with | some n => pure n.toString | none => do pure (← ppExpr fn).pretty
  return ufNode "uf_prop" fnStr lArgs 0 "bool"

partial def lowerTerm (e : Expr) (fuel : Nat := 1024) : AuditM Json := do
  if fuel == 0 then throwError "unsupported: lowerTerm fuel exhausted"
  let e ← normalizeHead e
  if ← isProp e then
    return ← lowerProp e (fuel - 1)
  if let .letE _ _ val body _ := e then
    return ← lowerTerm (body.instantiate1 val) (fuel - 1)
  if let .lam bName bTy body bi := e then
    let rawBTy := bTy
    if (← isProp rawBTy) || rawBTy.isSort || (← isClass? rawBTy).isSome then
      return ← withLocalDecl bName bi bTy fun fv => lowerTerm (body.instantiate1 fv) (fuel - 1)
    let d ← modifyGet fun s => (s.lamDepth, { s with lamDepth := s.lamDepth + 1 })
    let bodyJson ← expandSymbolicValue bTy
      (fun idx sort => do
        let lname := s!"_lam_{d}_{idx}"
        return Json.mkObj [("var", toJson lname), ("sort", toJson sort)])
      (fun lv => do
        let inst := (body.instantiate1 lv).headBeta
        let bty ← inferType inst
        if ← isProp bty then
          lowerProp inst (fuel - 1)
        else
          let btyWhnf ← withTransparency .all (whnf bty)
          let bfn := btyWhnf.getAppFn.constName?
          if bfn == some `Aeneas.Std.Result || bfn == some `Aeneas.Std.RustM || bty.getAppFn.constName? == some `Aeneas.Std.RustM then
            evalRustM inst (fun r => do
              let rTy ← inferType r
              if ← isProp rTy then lowerProp r (fuel - 1) else lowerTerm r (fuel - 1)) (fuel - 1)
          else
            lowerTerm inst (fuel - 1))
    modify fun s => { s with lamDepth := d }
    return Json.mkObj [("op", toJson "lam"), ("body", bodyJson)]
  if let .lit (.natVal n) := e then
    return intJson (Int.ofNat n)
  if e.isFVar then
    let st ← get
    if let some j := st.subst.get? e.fvarId! then return j
    if let some (isOkJson, okExpr, errExpr) := st.resultMap.get? e.fvarId! then
      return ufNode "uf_term" "Result" #[isOkJson, ← lowerTerm okExpr (fuel - 1), ← lowerTerm errExpr (fuel - 1)] 0 "int"
    if let some (isSomeJson, valExpr) := st.optionMap.get? e.fvarId! then
      return ufNode "uf_term" "Option" #[isSomeJson, ← lowerTerm valExpr (fuel - 1)] 0 "int"
    if let some vname := st.varMap.get? e.fvarId! then
      let sort ← detectSort (← inferType e)
      return Json.mkObj [("var", toJson vname), ("sort", toJson sort)]
    let sort ← detectSort (← inferType e)
    return ← registerVar e.fvarId! (s!"_fv_{e.fvarId!.name}") sort
  if let some n ← tryEvalClosedInt? e then
    return intJson n
  let fn := e.getAppFn
  let args := e.getAppArgs
  let name := fn.constName?
  if name == some ``Bool.true then return node "true"
  if name == some ``Bool.false then return node "false"
  if name == some `System.Platform.numBits then return intJson 64
  if name == some `Aeneas.Std.Usize.max then return intJson 18446744073709551615
  if name == some `Aeneas.Std.Usize.min then return intJson 0
  if name == some `Aeneas.Std.Isize.max then return intJson 9223372036854775807
  if name == some `Aeneas.Std.Isize.min then return intJson (-9223372036854775808)
  if isCoreName name "cmp.Ordering.Less" then return intJson (-1)
  if isCoreName name "cmp.Ordering.Equal" then return intJson 0
  if isCoreName name "cmp.Ordering.Greater" then return intJson 1
  if name == some ``decide && args.size >= 1 then
    return ← lowerProp args[0]! (fuel - 1)
  if name == some ``BEq.beq && args.size >= 2 then
    return ← lowerEq args[args.size - 2]! args[args.size - 1]! (fuel - 1)
  if name == some ``bne && args.size >= 2 then
    return node "not" #[← lowerEq args[args.size - 2]! args[args.size - 1]! (fuel - 1)]
  if (name == some ``Bool.and || name == some ``and) && args.size == 2 then
    return node "and" #[← lowerTerm args[0]! (fuel - 1), ← lowerTerm args[1]! (fuel - 1)]
  if (name == some ``Bool.or || name == some ``or) && args.size == 2 then
    return node "or" #[← lowerTerm args[0]! (fuel - 1), ← lowerTerm args[1]! (fuel - 1)]
  if (name == some ``Bool.not || name == some ``not) && args.size == 1 then
    return node "not" #[← lowerTerm args[0]! (fuel - 1)]
  if (name == some `Aeneas.Std.UScalar.val || name == some `Aeneas.Std.IScalar.val ||
      name == some `Aeneas.Std.UScalar.mk || name == some `Aeneas.Std.IScalar.mk ||
      name == some ``Subtype.val ||
      name == some ``BitVec.ofNat || name == some ``BitVec.ofInt ||
      name == some ``Nat.cast || name == some ``Int.ofNat ||
      name == some `Aeneas.Std.UScalar.cast || name == some `Aeneas.Std.IScalar.cast) && args.size >= 1 then
    return ← lowerTerm args.back! (fuel - 1)
  if (name == some `Aeneas.Std.UScalar.ofNat || name == some `Aeneas.Std.UScalar.ofNatCore ||
      name == some `Aeneas.Std.IScalar.ofInt || name == some `Aeneas.Std.IScalar.ofIntCore) && args.size >= 2 then
    return ← lowerTerm args[1]! (fuel - 1)
  if name == some ``Subtype.mk && args.size == 4 then
    return ← lowerTerm args[2]! (fuel - 1)
  if (name == some `abs || name == some ``Int.natAbs) && args.size >= 1 then
    let v ← lowerTerm args.back! (fuel - 1)
    return node "if" #[node "le" #[intJson 0, v], v, node "neg" #[v]]
  if (name == some ``HAdd.hAdd || name == some ``Add.add || name == some ``Nat.add || name == some ``Int.add) && args.size >= 2 then
    return node "add" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HSub.hSub || name == some ``Sub.sub || name == some ``Nat.sub || name == some ``Int.sub) && args.size >= 2 then
    let ty ← inferType e
    let s ← detectSort ty
    let op := if s == "nat" then "natsub" else "sub"
    return node op #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HMul.hMul || name == some ``Mul.mul || name == some ``Nat.mul || name == some ``Int.mul) && args.size >= 2 then
    return node "mul" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HDiv.hDiv || name == some ``Div.div || name == some ``Nat.div || name == some ``Int.ediv || name == some ``Int.tdiv) && args.size >= 2 then
    return node "div" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HMod.hMod || name == some ``Mod.mod || name == some ``Nat.mod || name == some ``Int.emod || name == some ``Int.tmod) && args.size >= 2 then
    return node "mod" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HPow.hPow || name == some ``Pow.pow || name == some ``Nat.pow) && args.size >= 2 then
    return node "pow" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HAnd.hAnd || name == some ``Nat.land || name == some `Aeneas.Std.UScalar.and || name == some `Aeneas.Std.IScalar.and) && args.size >= 2 then
    return node "bitand" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HOr.hOr || name == some ``Nat.lor || name == some `Aeneas.Std.UScalar.or || name == some `Aeneas.Std.IScalar.or) && args.size >= 2 then
    return node "bitor" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HXor.hXor || name == some ``Nat.xor || name == some `Aeneas.Std.UScalar.xor || name == some `Aeneas.Std.IScalar.xor) && args.size >= 2 then
    return node "bitxor" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HShiftLeft.hShiftLeft || name == some ``Nat.shiftLeft) && args.size >= 2 then
    return node "shl" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``HShiftRight.hShiftRight || name == some ``Nat.shiftRight) && args.size >= 2 then
    return node "shr" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``Neg.neg || name == some ``Int.neg) && args.size >= 1 then
    return node "neg" #[← lowerTerm args.back! (fuel - 1)]
  if (name == some ``Min.min || name == some ``min) && args.size >= 2 then
    return node "min" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if (name == some ``Max.max || name == some ``max) && args.size >= 2 then
    return node "max" #[← lowerTerm args[args.size - 2]! (fuel - 1), ← lowerTerm args[args.size - 1]! (fuel - 1)]
  if name == some ``ite && args.size == 5 then
    return node "if" #[← lowerProp args[1]! (fuel - 1), ← lowerTerm args[3]! (fuel - 1), ← lowerTerm args[4]! (fuel - 1)]
  if name == some ``dite && args.size == 5 then
    let c := args[1]!
    let tBr ← withLocalDeclD `_h c fun h => lowerTerm (mkApp args[3]! h).headBeta (fuel - 1)
    let fBr ← withLocalDeclD `_nh (mkNot c) fun h => lowerTerm (mkApp args[4]! h).headBeta (fuel - 1)
    return node "if" #[← lowerProp c (fuel - 1), tBr, fBr]
  if let .const n _ := fn then
    if !(opaqueHelperNames.any (fun h => n.toString.endsWith ("." ++ h) || n.toString == h)) then
      let env ← getEnv
      let ci? := env.find? n
      if ci? matches some (.defnInfo _) then
        if shouldUnfoldHelper n then
          if let some u ← withTransparency .all (unfoldDefinition? e) then
            return ← lowerTerm u (fuel - 1)
  let lArgs ← lowerArgs args (fuel - 1)
  if fn.isFVar then
    let fnJson ← lowerTerm fn (fuel - 1)
    return ufNode "uf_term" "app" (#[fnJson] ++ lArgs) 0 "int"
  let fnStr ← match name with | some n => pure n.toString | none => do pure (← ppExpr fn).pretty
  return ufNode "uf_term" fnStr lArgs 0 "int"

end


partial def peelTheoremBinders (remType : Expr) (candSpecName? : Option Name) (preAcc : Array Json) : AuditM Json := do
  if let .forallE bName dom body bi := remType then
    let domWhnf ← withTransparency .all (whnf dom)
    if domWhnf.isSort then
      withLocalDecl bName bi dom fun fv =>
        peelTheoremBinders (body.instantiate1 fv) candSpecName? preAcc
    else if ← isProp dom then
      let preJson ← lowerProp dom
      withLocalDecl bName bi dom fun hFv =>
        peelTheoremBinders (body.instantiate1 hFv) candSpecName? (preAcc.push preJson)
    else
      let baseName := bName.eraseMacroScopes.toString
      let isAtomic ← isAtomicScalarType dom
      expandSymbolicValue dom
        (fun idx sort => do
          let vname := if isAtomic then baseName else s!"{baseName}_{idx}"
          modify fun s => { s with vars := s.vars.push { name := vname, sort := sort } }
          return Json.mkObj [("var", toJson vname), ("sort", toJson sort)])
        (fun valExpr => peelTheoremBinders (body.instantiate1 valExpr) candSpecName? preAcc)
  else
    let env ← getEnv
    let oracleFn := remType.getAppFn
    let oracleArgs := remType.getAppArgs
    let some oracleSpecName := oracleFn.constName? | throwError "expected spec application in conclusion, got {← ppExpr remType}"
    let some oracleSpecCi := env.find? oracleSpecName | throwError "missing oracle spec {oracleSpecName}"
    let candSpecName := candSpecName?.getD oracleSpecName
    auditDecl env candSpecName oracleSpecCi.type
    let oracleJson ← lowerProp remType
    let candExpr := mkAppN (mkConst candSpecName oracleFn.constLevels!) oracleArgs
    let candJson ← lowerProp candExpr
    let st ← get
    let varsJson := st.vars.map fun v => Json.mkObj [("name", toJson v.name), ("sort", toJson v.sort)]
    return Json.mkObj [
      ("vars", Json.arr varsJson),
      ("preconditions", Json.arr preAcc),
      ("oracle", oracleJson),
      ("candidate", candJson)
    ]

def auditTask (thmName : Name) (candSpecName? : Option Name := none) : MetaM Json := do
  let env ← getEnv
  let some thmCi := env.find? thmName | throwError "missing theorem {thmName}"
  let (res, _) ← (peelTheoremBinders thmCi.type candSpecName? #[]).run {}
  return res

def strToName (s : String) : Name :=
  (s.splitOn ".").foldl Name.str Name.anonymous

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | "--batch" :: pairs =>
    for p in pairs do
      let parts := p.splitOn ":"
      if parts.length >= 3 then
        let tid := parts[0]!
        let modName := strToName parts[1]!
        let thmName := strToName parts[2]!
        withImportModules #[{module := modName}] {} fun env => do
          let (result, _) ← (do
            try
              let j ← auditTask thmName none
              pure <| Json.mkObj [("id", toJson tid), ("ok", toJson true), ("data", j)]
            catch err =>
              pure <| Json.mkObj [("id", toJson tid), ("ok", toJson false), ("error", toJson (← err.toMessageData.toString))]
          : MetaM Json).toIO {fileName := "spec-audit", fileMap := default, maxHeartbeats := 0} {env := env}
          IO.println result.compress
    return 0

  | [modStr, thmStr] =>
    let modName := strToName modStr
    let thmName := strToName thmStr
    withImportModules #[{module := modName}] {} fun env => do
      let (result, _) ← (do
        try auditTask thmName none
        catch err => pure <| Json.mkObj [("error", toJson (← err.toMessageData.toString))]
      : MetaM Json).toIO {fileName := "spec-audit", fileMap := default, maxHeartbeats := 0} {env := env}
      IO.println result.compress
      return 0
  | [mod1Str, mod2Str, thmStr, candStr] =>
    let mod1 := strToName mod1Str
    let mod2 := strToName mod2Str
    let thmName := strToName thmStr
    let candName := strToName candStr
    withImportModules #[{module := mod1}, {module := mod2}] {} fun env => do
      let (result, _) ← (do
        try auditTask thmName (some candName)
        catch err => pure <| Json.mkObj [("error", toJson (← err.toMessageData.toString))]
      : MetaM Json).toIO {fileName := "spec-audit", fileMap := default, maxHeartbeats := 0} {env := env}
      IO.println result.compress
      return 0
  | _ =>
    IO.eprintln "Usage: SpecAudit <refModule> <thmName> OR SpecAudit <refModule> <candModule> <thmName> <candSpecName>"
    return 1



