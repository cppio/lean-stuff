import Common.Meta

open Lean Parser Meta Elab

elab tk:"@[structural]" fns:Command.mutual : command => withRef tk do
  let fns ← fns.raw[1].getArgs.mapM fun fn => do Command.mkDefView (← elabModifiers fn[0]) fn[1]
  if fns.isEmpty then
    return
  Command.liftTermElabM do
  let fns ← _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.elabHeaders fns
  _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.withFunLocalDecls fns fun fnExprs => do

  let fns ← fns.mapM fun header =>
    forallBoundedTelescope header.type header.numParams fun defParams type => do

    let .forallE name major body _ ← whnf type
      | throwErrorAt header.ref "expected function type"
    let major ← whnf major
    let some induct := major.getAppFn.constName?
      | throwErrorAt header.ref "expected inductive type"

    let induct ← getConstInfoInduct induct
    let args := major.getAppArgs
    let params := args[:induct.numParams]
    let indices := args[induct.numParams:]

    let skip := params.foldl collectFVars {} |>.fvarSet

    let (fixedParams, fixedParamsIdx) := defParams.zipWithIndex.filter (skip.contains ·.fst.fvarId!) |>.unzip

    let (skip, indicesIdx) ← indices.foldlM (init := (skip, @Array.mkEmpty Nat indices.size)) fun (skip, indicesIdx) index => do
      if !index.isFVar then
        throwErrorAt header.ref "index is not a variable"
      if skip.contains index.fvarId! then
        throwErrorAt header.ref "duplicate index variable"
      return (skip.insert index.fvarId!, indicesIdx.push (defParams.indexOf? index |>.map (↑·)).get!)

    let (genParams, genParamsIdx) := defParams.zipWithIndex.filter (!skip.contains ·.fst.fvarId!) |>.unzip

    let motive ← mkForallFVars genParams <| body.instantiate1 (.bvar genParams.size)
    let level := (← inferType motive).sortLevel!
    let motive ← mkForallFVars fixedParams <| ← mkLambdaFVars indices <| .lam name major motive .default
    return (header, induct, major.getAppFn.constLevels!, motive, level, fixedParamsIdx, indicesIdx, genParamsIdx)

  let (header, induct, levels, motive, level, fixedParamsIdx, _) := fns[0]!
  forallBoundedTelescope motive fixedParamsIdx.size fun fixedParams _ => do
  let paramsTy ← mkForallFVars fixedParams <| .const ``Unit []

  let recLevels ← do
    if (← getConstInfoRec (mkRecName induct.name)).levelParams.length > induct.levelParams.length then
      pure <| level :: levels
    else
      if level != .zero then
        throwErrorAt header.ref m!"cannot eliminate into non-prop sort"
      pure levels

  for (header', _, levels', motive', level', fixedParamsIdx', _) in fns[1:] do
    if header'.levelNames != header.levelNames then
      throwErrorAt header'.ref m!"different level parameters"
    if levels' != levels then
      throwErrorAt header'.ref m!"levels mismatch"
    if level' != level then
      throwErrorAt header'.ref m!"output sort mismatch"
    forallBoundedTelescope motive' fixedParamsIdx'.size fun fixedParams' _ => do
      let paramsTy' ← mkForallFVars fixedParams' <| .const ``Unit []
      if !(← isDefEq paramsTy paramsTy') then
        throwErrorAt header'.ref m!"fixed params differ"

  let fns ← fns.mapM fun (header, induct, _, motive, _, fixedParamsIdx, indicesIdx, genParamsIdx) =>
    Elab.Term.withDeclName header.declName do

    let `(Command.declValEqns| $alts:matchAlt*) := header.valueStx
      | throwErrorAt header.valueStx "expected match arms"
    let alts ← liftMacroM <| alts.concatMapM Term.expandMatchAlt
    let alts ← alts.mapM fun alt => do
      match alt with
      | `(Term.matchAltExpr| | $pattern => $rhs) =>
        return {
          ref := alt
          patterns := #[pattern]
          rhs
        }
      | _ => throwErrorAt alt "expected match arm with single pattern"
    let alts ← liftMacroM <| Term.expandMacrosInPatterns alts

    let motive' ← instantiateForall motive fixedParams

    let motives ← fns.foldlM (init := mkHashMap) fun motives (_, induct, _, motive, _) =>
      return motives.insert induct.name <| ← instantiateForall motive fixedParams

    let alts ← alts.mapM fun alt => do
      let (pVars, alt) ← Term.collectPatternVars alt
      _private.Lean.Elab.Match.0.Lean.Elab.Term.withPatternVars pVars fun pVarDecls => do
      let (_, _, .lam _ major motive _) ← lambdaMetaTelescope motive' induct.numIndices
        | unreachable!

      let lhs ← Term.elabTermEnsuringType alt.patterns[0]! major
      let lhs ← instantiateMVars lhs

      let mvars := lhs.collectMVars {} |>.result
      _ ← setMVarUserNamesAt lhs <| mvars.map .mvar
      let extraFields ← mvars.mapM fun mvar => do
        let decl ← mvar.getDecl
        return (decl.userName, fun _ => return decl.type)
      withLocalDeclsD extraFields fun extraFields => do
      modifyMCtx fun mctx => { mctx with eAssignment := mvars.zip extraFields |>.foldl (init := mctx.eAssignment) fun eAssignment (mvar, fvar) => eAssignment.insert mvar fvar }

      let lhs ← instantiateMVars lhs
      let lhs ← whnf lhs

      let some ctor := lhs.getAppFn.constName?
        | throwErrorAt alt.patterns[0]! "not a constructor"
      let cv ← getConstInfoCtor ctor
      let fields := lhs.getAppArgs[cv.numParams:].toArray
      for field in fields do
        if !field.isFVar || (!pVarDecls.any (·.fvarId == field.fvarId!) && !extraFields.any (· == field)) then
          throwErrorAt alt.patterns[0]! "field is not a variable"

      let (ihFields, ihs) := Array.unzip <| ← fields.filterMapM fun field => do
        forallTelescopeReducing (← instantiateMVars <| ← field.fvarId!.getType) fun xs t => do
          t.getAppFn.constName?.bindM fun fn => do
          motives.find? fn |>.mapM fun motive => do
          let ih ← mkForallFVars xs <| ← instantiateLambda motive <| t.getAppArgs[induct.numParams:].toArray.push (mkAppN field xs)
          return (field, (← field.fvarId!.getUserName).appendAfter "_ih", (fun _ => return ih : Array _ → TermElabM _))
      withLocalDeclsD ihs fun ihs =>

      forallBoundedTelescope (motive.instantiate1 lhs) genParamsIdx.size fun genParams body => do
      let rhs ← Term.elabTermEnsuringType alt.rhs body
      Term.synthesizeSyntheticMVars
      let rhs ← instantiateMVars rhs

      let minor ← transform rhs (post := fun e => do
        let some stx := getRecAppSyntax? e
          | return .done e
        let args := e.mdataExpr!.getAppArgs
        if args.size <= header.numParams then
          throwErrorAt stx "not enough arguments"
        if fixedParamsIdx.map args.get! != fixedParams then
          throwErrorAt stx "fixed params difer"
        let major := args[header.numParams]!
        let some idx := ihFields.indexOf? major.getAppFn
          | throwErrorAt stx "invalid recursive call"
        return .done <| mkAppN (mkAppN (mkAppN ihs[idx]! major.getAppArgs) (genParamsIdx.map args.get!)) args[header.numParams + 1:]
      )

      let rhs ← transform rhs (post := fun e => do
        if !e.isMData then
          return .done e
        let some idx := fnExprs.indexOf? e.mdataExpr!.getAppFn
          | return .done e
        return .done <| mkAppN (.const fns[idx]!.fst.declName (header.levelNames.map .param)) e.mdataExpr!.getAppArgs
      )

      return (alt.patterns[0]!, cv.name, ← mkLambdaFVars (fixedParams ++ fields ++ genParams) rhs, ← mkLambdaFVars (fixedParams ++ fields ++ ihs ++ genParams) minor)

    let alts ← alts.foldlM (init := mkHashMap) fun alts (ref, ctor, alt) =>
      if alts.contains ctor then
        throwErrorAt ref "duplicate constructor"
      else
        return alts.insert ctor alt

    let alts ← induct.ctors.mapM fun ctor =>
      if let some alt := alts.find? ctor then
        return alt
      else
        throwErrorAt header.ref m!"missing constructor: {ctor}"

    return (header, induct, motive, alts, fixedParamsIdx, indicesIdx, genParamsIdx)

  let fns ← fns.foldlM (init := mkHashMap) fun fns (header, induct, fn) =>
    if fns.contains induct.name then
      throwErrorAt header.ref "duplicate inductive"
    else
      return fns.insert induct.name (header, induct, fn)

  let fns ← induct.all.toArray.mapM fun induct =>
    if let some fn := fns.find? induct then
      return fn
    else
      throwError "missing inductive: {induct}"

  for (header, _, _, _, fixedParamsIdx, indicesIdx, genParamsIdx) in fns do
    forallBoundedTelescope header.type (some (header.numParams + 1)) fun defParams _ => do
    let fixedParams := fixedParamsIdx.map defParams.get!
    let indices := indicesIdx.map defParams.get!
    let genParams := genParamsIdx.map defParams.get!

    let major := defParams.back
    let majorTy ← major.fvarId!.getType
    let majorTy ← whnf majorTy
    let induct := majorTy.getAppFn
    let args := majorTy.getAppArgs

    let mut e := .const (mkRecName induct.constName!) recLevels
    e := mkAppN e args[:args.size - indices.size]
    e := mkAppN e <| ← fns.mapM fun (_, _, motive, _) => instantiateForall motive fixedParams
    e := mkAppN e <| ← fns.concatMapM fun (_, _, _, alts, _) => alts.toArray.mapM fun (_, minor) => instantiateLambda minor fixedParams
    e := mkAppN e indices
    e := .app e major
    e := mkAppN e genParams

    addDecl <| .defnDecl {
      name := header.declName
      levelParams := header.levelNames
      type := header.type
      value := ← mkLambdaFVars defParams e
      hints := .opaque
      safety := if header.modifiers.isUnsafe then .unsafe else .safe
    }

  for (header, induct, motive, alts, fixedParamsIdx, indicesIdx, genParamsIdx) in fns do
    forallBoundedTelescope header.type (some (header.numParams + 1)) fun defParams _ => do
    let fixedParams := fixedParamsIdx.map defParams.get!
    let indices := indicesIdx.map defParams.get!
    let genParams := genParamsIdx.map defParams.get!

    let major := defParams.back
    let majorTy ← major.fvarId!.getType
    let majorTy ← whnf majorTy
    let args := majorTy.getAppArgs

    let casesOn := mkCasesOnName induct.name

    let mut e := .const casesOn recLevels
    e := mkAppN e args[:args.size - indices.size]
    e := .app e <| ← instantiateForall motive fixedParams
    e := mkAppN e indices
    e := .app e major
    e := mkAppN e <| ← alts.toArray.mapM fun (rhs, _) => instantiateLambda rhs fixedParams
    e := mkAppN e genParams

    addDecl <| .defnDecl {
      name := Compiler.mkUnsafeRecName header.declName
      levelParams := header.levelNames
      type := header.type
      value := ← mkLambdaFVars defParams e
      hints := .opaque
      safety := if header.modifiers.isUnsafe then .unsafe else .safe
    }

    let matcherName ← mkAuxName (header.declName.str "match") 1
    let casesOnInfo ← getConstInfo casesOn

    addDecl <| .defnDecl {
      name := matcherName
      levelParams := casesOnInfo.levelParams
      type := casesOnInfo.type
      value := .const casesOn (casesOnInfo.levelParams.map .param)
      hints := .abbrev
      safety := .safe
    }

    Match.addMatcherInfo matcherName {
        numParams := induct.numParams
        numDiscrs := induct.numIndices + 1
        altNumParams := ← induct.ctors.toArray.mapM fun ctor => return (← getConstInfoCtor ctor).numFields
        uElimPos? := if casesOnInfo.levelParams.length == levels.length then none else some 0
        discrInfos := #[]
    }

    e := .const matcherName recLevels
    e := mkAppN e args[:args.size - indices.size]
    e := .app e <| ← instantiateForall motive fixedParams
    e := mkAppN e indices
    e := .app e major
    e := mkAppN e <| ← alts.toArray.mapM fun (rhs, _) => do
      let rhs ← instantiateLambda rhs fixedParams
      lambdaTelescope rhs fun xs rhs => do
        mkLambdaFVars xs[:xs.size - genParams.size] <| markSmartUnfoldingMatchAlt <| ← mkLambdaFVars xs[xs.size - genParams.size:] rhs
    e := markSmartUnfoldingMatch e
    e := mkAppN e genParams

    addDecl <| .defnDecl {
      name := mkSmartUnfoldingNameFor header.declName
      levelParams := header.levelNames
      type := header.type
      value := ← mkLambdaFVars defParams e
      hints := .opaque
      safety := if header.modifiers.isUnsafe then .unsafe else .safe
    }

  compileDecls <| Array.toList <| fns.map fun (header, _) => Compiler.mkUnsafeRecName header.declName

  -- TODO equations
  -- TODO eq_def

  for (header, _) in fns do
    Term.applyAttributes header.declName header.modifiers.attrs

/-
mutual

inductive Even
  | zero
  | succ (o : Odd)

inductive Odd
  | succ (e : Even)

end

@[structural]
mutual

def Odd.toNat : (o : Odd) → Nat
  | .succ e => .succ e.toNat

def Even.toNat : (e : Even) → Nat
  | .succ o => .succ o.toNat
  | .zero   => .zero

end

@[structural]
mutual

def List.id {α : Type u} : List α → List α
  | [] => []
  | x :: xs => x :: xs.id

end

@[structural]
mutual

def List.mem {α : Type u} : (l : List α) → List { x // x ∈ l }
  | [] => []
  | x :: xs => ⟨x, .head xs⟩ :: xs.mem.map fun ⟨_, h⟩ => ⟨_, .tail x h⟩

end

inductive Fin2 : Nat → Type
  | zero : Fin2 (.succ n)
  | succ : Fin2 n → Fin2 n.succ

@[structural]
mutual

def Fin2.toNat : Fin2 n → Nat
  | .zero   => .zero
  | .succ i => .succ i.toNat

end

inductive Ordinal
  | zero
  | succ (o : Ordinal)
  | limit (os : Nat → Ordinal)

@[structural]
mutual

def Ordinal.add (x : Ordinal) : (y : Ordinal) → Ordinal
  | .zero => x
  | .succ y => .succ (x.add y)
  | .limit ys => .limit (x.add <| ys ·)

end

@[structural]
mutual

def List_id {α : Sort u} : List (PLift α) → List (PLift α)
  | [] => []
  | x :: xs => x :: xs

end

mutual

inductive EvenList (α : Type u)
  | nil
  | cons (x : α) (xs : OddList α)

inductive OddList (α : Type u)
  | cons (x : α) (xs : EvenList α)

end

@[structural]
mutual

def EvenList.toList {α : Type u} : EvenList α → List α
  | .nil       => .nil
  | .cons x xs => .cons x xs.toList

def OddList.toList {α : Type u} : OddList α → List α
  | .cons x xs => .cons x xs.toList

end
-/
