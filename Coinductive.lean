import Lean

open Lean Meta

@[elab_as_elim]
private theorem Nat.le.ndrec {motive : (n m : Nat) → Prop} (zero_le : ∀ m, motive .zero m) (succ_le_succ : ∀ {n m}, n.le m → motive n m → motive n.succ m.succ) : ∀ {n m}, n.le m → motive n m
  | .zero, m, _ => zero_le m
  | .succ _, .succ _, h => succ_le_succ (Nat.le_of_succ_le_succ h) (ndrec @zero_le @succ_le_succ (Nat.le_of_succ_le_succ h))

private theorem Subtype.eq' : {lhs rhs : Subtype p} → lhs.val = rhs.val → lhs = rhs
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

structure CoinductiveType.Field where
  name : Name
  type : Expr

structure CoinductiveType where
  name : Name
  levelParams : List Name
  type : Expr
  numParams : Nat
  ctorName : Name
  fields : Array CoinductiveType.Field

private partial def getUnusedLevelParam (levelParams : List Name) : Name :=
  if levelParams.contains `u then
    let rec loop (i : Nat) :=
      let u := (`u).appendIndexAfter i
      if levelParams.contains u then loop (i + 1) else u
    loop 1
  else
    `u

-- TODO: optimize ctor equality fields
-- TODO: switch from subtype to structure
-- TODO: dependent fields
-- TODO: computable
-- TODO: nested/mutual

def CoinductiveType.elab (view : CoinductiveType) : MetaM Unit :=
  forallBoundedTelescope view.type view.numParams fun params type => do
  if params.size < view.numParams then
    throwError "invalid number of parameters"
  forallTelescopeReducing type (whnfType := true) fun indices typeInner => do
  let .sort resultLevel := typeInner
    | throwError "invalid type"
  let levels := view.levelParams.map .param
  let viewFields ← view.fields.mapM fun field => do
    let mut fieldType := field.type
    for param in params do
      let .forallE _ d b _ := fieldType
        | throwError "invalid field {field.name}: missing parameter"
      unless d == (← param.fvarId!.getType) do
        throwError "invalid field {field.name}: mismatched parameter"
      fieldType := b.instantiate #[param, .bvar 0]
    let rec isRec idx
      | e@(.forallE _ d b _) => do
        if d.hasLooseBVar idx then
          throwError "invalid field {field.name}: invalid recursive occurrence"
        let (b, isRec) ← isRec (idx + 1) b
        return (e.updateForallE! d b, isRec)
      | ty =>
        ty.withApp fun fn args => do
        if fn == .bvar idx then
          if params != args[:view.numParams] then
            throwError "invalid field {field.name}: mismatched parameter"
          if args[view.numParams:].any (·.hasLooseBVar idx) then
            throwError "invalid field {field.name}: invalid recursive occurrence"
          return (mkAppN fn args[view.numParams:], true)
        if ty.hasLooseBVar idx then
          throwError "invalid field {field.name}: invalid recursive occurrence"
        return (ty, false)
    let rec findMajorIdx idx
      | e@(.forallE _ d b _) =>
        d.withApp fun fn args => do
        if fn == .bvar idx then
          if params != args[:view.numParams] then
            throwError "invalid field {field.name}: mismatched parameter"
          if args[view.numParams:].any (·.hasLooseBVar idx) then
            throwError "invalid field {field.name}: invalid recursive occurrence"
          let (b, isRec) ← isRec (idx + 1) b
          return (e.updateForallE! (mkAppN fn args[view.numParams:]) b, idx, isRec, field.type)
        if d.hasLooseBVar idx then
          throwError "invalid field {field.name}: invalid recursive occurrence"
        let (b, rest) ← findMajorIdx (idx + 1) b
        return (e.updateForallE! d b, rest)
      | _ => do
        unless indices.isEmpty do
          throwError "invalid field {field.name}: missing self argument for indexed coinductive"
        let (b, isRec) ← isRec 0 fieldType
        forallBoundedTelescope field.type view.numParams fun params' fieldType' =>
        return (.forallE `self (.bvar 0) (b.instantiate1 (.bvar 1)) .default, 0, isRec, ← mkForallFVars params' (.forallE `self (mkAppN (.bvar view.numParams) params') (fieldType'.instantiate1 (.bvar (view.numParams + 1))) .default))
    findMajorIdx 0 fieldType
  withLocalDeclD `Approx type fun approxArg => do
  let approxName := view.name.str "Approx"
  let patternName := approxName.str "Pattern"
  let patternCtorName := patternName.str "mk"
  let pattern := mkAppN (.const patternName levels) params
  let fieldDecls ← (view.fields.zip viewFields).mapM fun (field, fieldType, majorIdx, _) =>
    forallBoundedTelescope (fieldType.instantiate1 approxArg) majorIdx fun preArgs fieldType => do
    let eqs ← (indices.zip fieldType.bindingDomain!.getAppArgs).mapM fun (index, indexVal) => return (`h, ← mkEq index indexVal)
    withLocalDeclsDND eqs fun eqs =>
    return (field.name.componentsRev.head!, ← mkForallFVars (preArgs ++ eqs) fieldType.bindingBody!)
  withLocalDeclsDND fieldDecls fun fields => do
    addDecl <| .inductDecl view.levelParams (view.numParams + 1 + indices.size) [{
      name := patternName
      type := ← mkForallFVars (params.push approxArg ++ indices) typeInner
      ctors := [{
        name := patternCtorName
        type := ← mkForallFVars (params.push approxArg ++ indices ++ fields) (mkAppN (.app pattern approxArg) indices)
      }]
    }] false
  let patternCtor := mkAppN (.const patternCtorName levels) params
  addDecl <| .defnDecl {
    name := approxName
    levelParams := view.levelParams
    type := ← mkForallFVars params (.forallE `ℓ (.const ``Nat []) type .default)
    value := ← mkLambdaFVars params (.app (.app (.app (.const ``Nat.rec [(← inferType type).sortLevel!]) (.lam `ℓ (.const ``Nat []) type .default)) (← mkLambdaFVars indices (.const ``PUnit [resultLevel]))) (.lam `ℓ (.const ``Nat []) pattern .default))
    hints := .opaque -- TODO
    safety := .safe
  }
  let approx := mkAppN (.const approxName levels) params
  let agreeName := approxName.str "Agree"
  let agreePatternName := agreeName.str "Pattern"
  let agreePatternCtorName := agreePatternName.str "intro"
  let agreePattern := mkAppN (.const agreePatternName levels) params
  withLocalDecl `Approx .implicit type fun approx₁ =>
    withLocalDecl `Approx' .implicit type fun approx₂ => do
    withLocalDeclD `Agree (← mkForallFVars indices (.forallE `a (mkAppN approx₁ indices) (.forallE `a' (mkAppN approx₂ indices) (.sort .zero) .default) .default)) fun agree =>
    withLocalDeclD `a (mkAppN (.app pattern approx₁) indices) fun a =>
    withLocalDeclD `a' (mkAppN (.app pattern approx₂) indices) fun a' => do
    let ihs ← (fieldDecls.zip viewFields).mapIdxM fun fieldIdx (⟨_, type⟩, _, _, isRec, _) =>
      let fieldℓ := .proj patternName fieldIdx a
      let fieldℓ' := .proj patternName fieldIdx a'
      if isRec then
        forallTelescope type fun typeArgs typeRes =>
        return ⟨`h, ← mkForallFVars typeArgs (mkAppN agree (typeRes.getAppArgs.push (mkAppN fieldℓ typeArgs) |>.push (mkAppN fieldℓ' typeArgs)))⟩
      else
        return ⟨`h, ← mkEq fieldℓ fieldℓ'⟩
    withLocalDeclsDND ihs fun ihs => do
    addDecl <| .inductDecl view.levelParams (view.numParams + 3 + indices.size + 2) [{
      name := agreePatternName
      type := ← mkForallFVars ((params.push approx₁ |>.push approx₂ |>.push agree) ++ indices |>.push a |>.push a') (.sort .zero)
      ctors := [{
        name := agreePatternCtorName
        type := ← mkForallFVars (((params.push approx₁ |>.push approx₂ |>.push agree) ++ indices |>.push a |>.push a') ++ ihs) (mkAppN (.app (.app (.app agreePattern approx₁) approx₂) agree) (indices.push a |>.push a'))
      }]
    }] false
  let agreePatternCtor := mkAppN (.const agreePatternCtorName levels) params
  withLocalDecl `ℓ .implicit (.const ``Nat []) fun ℓ =>
  withLocalDecl `ℓ' .implicit (.const ``Nat []) fun ℓ' =>
  withLocalDeclD `h (.app (.app (.const ``Nat.le []) ℓ) ℓ') fun h => do
  let recLevel := (← inferType (← mkForallFVars indices (mkAppN (.app approx ℓ) indices))).sortLevel!
  addDecl <| .defnDecl {
    name := agreeName
    levelParams := view.levelParams
    type := ← mkForallFVars ((params.push ℓ |>.push ℓ') ++ indices) (.forallE `a (mkAppN (.app approx ℓ) indices) (.forallE `a' (mkAppN (.app approx ℓ') indices) (.sort .zero) .default) .default)
    value := ← mkLambdaFVars params (.app (.app (.app (.const ``Nat.rec [recLevel]) (← mkLambdaFVars #[ℓ] (← mkForallFVars (#[ℓ'] ++ indices) (.forallE `a (mkAppN (.app approx ℓ) indices) (.forallE `a' (mkAppN (.app approx ℓ') indices) (.sort .zero) .default) .default)))) (← mkLambdaFVars (#[ℓ'] ++ indices) (.lam `a (mkAppN (.app approx (.const ``Nat.zero [])) indices) (.lam `a' (mkAppN (.app approx ℓ') indices) (.const ``True []) .default) .default))) (← mkLambdaFVars #[ℓ] (.lam `Agree (← mkForallFVars (#[ℓ'] ++ indices) (.forallE `a (mkAppN (.app approx ℓ) indices) (.forallE `a' (mkAppN (.app approx ℓ') indices) (.sort .zero) .default) .default)) (.app (.app (.app (.const ``Nat.rec [recLevel]) (← mkLambdaFVars #[ℓ'] (← mkForallFVars indices (.forallE `a (mkAppN (.app approx (.app (.const ``Nat.succ []) ℓ)) indices) (.forallE `a' (mkAppN (.app approx ℓ') indices) (.sort .zero) .default) .default)))) (← mkLambdaFVars indices (.lam `a (mkAppN (.app approx (.app (.const ``Nat.succ []) ℓ)) indices) (.lam `a' (mkAppN (.app approx (.const ``Nat.zero [])) indices) (.const ``False []) .default) .default))) (← mkLambdaFVars #[ℓ'] (.lam `Agree (← mkForallFVars indices (.forallE `a (mkAppN (.app approx (.app (.const ``Nat.succ []) ℓ)) indices) (.forallE `a' (mkAppN (.app approx ℓ') indices) (.sort .zero) .default) .default)) (.app (.app (.app agreePattern (.app approx ℓ)) (.app approx ℓ')) (.app (.bvar 2) ℓ')) .default))) .default)))
    hints := .opaque -- TODO
    safety := .safe
  }
  let agree := mkAppN (.const agreeName levels) params
  let α := .forallE `ℓ (.const ``Nat []) (mkAppN (.app approx (.bvar 0)) indices) .default
  let β := .lam `f α (.forallE `ℓ (.const ``Nat []) (.forallE `ℓ' (.const ``Nat []) (.forallE `h (.app (.app (.const ``Nat.le []) (.bvar 1)) (.bvar 0)) (mkAppN (.app (.app agree (.bvar 2)) (.bvar 1)) (indices.push (.app (.bvar 3) (.bvar 2)) |>.push (.app (.bvar 3) (.bvar 1)))) .default) .implicit) .implicit) .default
  addDecl <| .defnDecl {
    name := view.name
    levelParams := view.levelParams
    type := view.type
    value := ← mkLambdaFVars (params ++ indices) (.app (.app (.const ``Subtype [resultLevel]) α) β)
    hints := .opaque -- TODO
    safety := .safe
  }
  let coind := mkAppN (.const view.name levels) params
  for (field, (fieldType, majorIdx, isRec, fieldType'), fieldIdx) in view.fields.zip viewFields.zipIdx do
    addDecl <| .defnDecl {
      name := field.name
      levelParams := view.levelParams
      type := fieldType'.instantiate1 (.const view.name levels)
      value := ← mkLambdaFVars params <| ← forallTelescope (fieldType.instantiate1 coind) fun args body => do
        let major := args[majorIdx]!
        let commonArgs := args[:majorIdx].toArray ++ (← (← major.fvarId!.getType).getAppArgs[view.numParams:].toArray.mapM mkEqRefl)
        if isRec then
          let indexValues := body.getAppArgs[view.numParams:]
          mkLambdaFVars args (.app (.app (.app (.app (.const ``Subtype.mk [resultLevel]) (α.replaceFVars indices indexValues)) (β.replaceFVars indices indexValues)) (.lam `ℓ (.const ``Nat []) (mkAppN (.proj patternName fieldIdx (.app (.proj ``Subtype 0 args[majorIdx]!) (.app (.const ``Nat.succ []) (.bvar 0)))) (commonArgs ++ args[majorIdx + 1:].toArray)) .default)) (.lam `ℓ (.const ``Nat []) (.lam `ℓ' (.const ``Nat []) (.lam `h (.app (.app (.const ``Nat.le []) (.bvar 1)) (.bvar 0)) (mkAppN (.proj agreePatternName fieldIdx (.app (.app (.app (.proj ``Subtype 1 args[majorIdx]!) (.app (.const ``Nat.succ []) (.bvar 2))) (.app (.const ``Nat.succ []) (.bvar 1))) (.app (.app (.app (.const ``Nat.succ_le_succ []) (.bvar 2)) (.bvar 1)) (.bvar 0)))) (commonArgs ++ args[majorIdx + 1:].toArray)) .default) .implicit) .implicit))
        else
          mkLambdaFVars args[:majorIdx + 1] (mkAppN (.proj patternName fieldIdx (.app (.proj ``Subtype 0 major) (.app (.const ``Nat.succ []) (.const ``Nat.zero [])))) commonArgs)
      hints := .opaque -- TODO
      safety := .safe
    }
  let paramBinderInfos ← params.mapM fun param => do
    let param := param.fvarId!
    let bi ← param.getBinderInfo
    return (param, if bi.isExplicit then .implicit else bi)
  let indicesBinderInfos ← indices.mapM fun index => do
    let index := index.fvarId!
    let bi ← index.getBinderInfo
    return (index, if bi.isExplicit then .implicit else bi)
  withNewBinderInfos paramBinderInfos do
  let u := getUnusedLevelParam view.levelParams
  withLocalDeclD `σ (← mkForallFVars indices (.sort (.param u))) fun σ =>
    let minors := view.fields.zipWith (bs := viewFields) fun field (fieldType, _) => (field.name.componentsRev.head!, fieldType.instantiate1 σ)
    withLocalDeclsDND minors fun minors => do
    withLocalDeclD `corec (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app approx ℓ) indices) .default)) fun corec => do
    withLocalDeclD `ih (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app (.app agree ℓ) ℓ') (indices.push (.app (mkAppN (.app (.bvar (indices.size + 7)) ℓ) indices) (.bvar 0)) |>.push (.app (mkAppN (.app (.bvar (indices.size + 7)) ℓ') indices) (.bvar 0)))) .default)) fun ih =>
    withLocalDeclD `s (mkAppN σ indices) fun s => do
    let fieldsVal ← (viewFields.zip <| minors.zip fieldDecls).mapM fun ⟨(_, majorIdx, isRec, _), minor, _, type⟩ =>
      forallTelescope type fun typeArgs typeRes => do
      let mut s := s
      let mut indexVals := indices
      for i in [:indices.size] do
        let pf := typeArgs[majorIdx + i]!
        let (idxTy, idxLhs, idxRhs) := (← pf.fvarId!.getType).eq?.get!
        s := .app (.app (.app (.app (.app (.app (.const ``Eq.ndrec [.param u, ← getLevel idxTy]) idxTy) idxLhs) (← mkLambdaFVars indices[i:i + 1] (mkAppN σ indexVals))) s) idxRhs) pf
        indexVals := indexVals.set! i idxRhs
      if isRec then
        mkLambdaFVars typeArgs (.app (mkAppN corec typeRes.getAppArgs) (mkAppN minor (typeArgs[:majorIdx].toArray.push s ++ typeArgs[majorIdx + indices.size:])))
      else
        mkLambdaFVars typeArgs[:majorIdx + indices.size] (mkAppN minor (typeArgs[:majorIdx].toArray.push s))
    let fieldsProperty ← fieldsVal.mapM fun type =>
      let type' := type.replaceFVar corec ih
      if type'.equal type then
        mkEqRefl type
      else
        return type'
    let corecName := view.name.str "corec"
    addDecl <| .defnDecl {
      name := corecName
      levelParams := u :: view.levelParams
      type := ← withNewBinderInfos indicesBinderInfos <| mkForallFVars (params.push σ ++ minors ++ indices) (.forallE `s (mkAppN σ indices) (mkAppN coind indices) .default)
      value := ← mkLambdaFVars (params.push σ ++ minors ++ indices) (.lam `s (mkAppN σ indices) (.letE `val (← mkForallFVars (#[ℓ] ++ indices) (.forallE `s (mkAppN σ indices) (mkAppN (.app approx ℓ) indices) .default)) (.app (.app (.app (.const ``Nat.rec [.max recLevel (.param u)]) (← mkLambdaFVars #[ℓ] (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app approx ℓ) indices) .default)))) (← mkLambdaFVars indices (.lam `s (mkAppN σ indices) (.const ``PUnit.unit [resultLevel]) .default))) (← mkLambdaFVars (#[ℓ, corec] ++ indices |>.push s) (mkAppN (.app patternCtor (.app approx ℓ)) (indices ++ fieldsVal)))) (.app (.app (.app (.app (.const ``Subtype.mk [resultLevel]) α) β) (.lam `ℓ (.const ``Nat []) (.app (mkAppN (.app (.bvar 1) (.bvar 0)) indices) (.bvar 2)) .default)) (.lam `ℓ (.const ``Nat []) (.lam `ℓ' (.const ``Nat []) (.lam `h (.app (.app (.const ``Nat.le []) (.bvar 1)) (.bvar 0)) (.app (mkAppN (.app (.app (.app (.app (.app (.app (.const ``Nat.le.ndrec []) (← mkLambdaFVars #[ℓ, ℓ'] (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app (.app agree ℓ) ℓ') (indices.push (.app (mkAppN (.app (.bvar (indices.size + 6)) ℓ) indices) (.bvar 0)) |>.push (.app (mkAppN (.app (.bvar (indices.size + 6)) ℓ') indices) (.bvar 0)))) .default)))) (.lam `ℓ' (.const ``Nat []) (← mkLambdaFVars indices (.lam `s (mkAppN σ indices) (.const ``True.intro []) .default)) .default)) (← mkLambdaFVars (#[ℓ, ℓ', h, ih] ++ indices |>.push s) (mkAppN (.app (.app (.app agreePatternCtor (.app approx ℓ)) (.app approx ℓ')) (.app (.app agree ℓ) ℓ')) ((indices.push (mkAppN (.app (.bvar (indices.size + 8)) (.app (.const ``Nat.succ []) ℓ)) (indices |>.push (.bvar 0))) |>.push (mkAppN (.app (.bvar (indices.size + 8)) (.app (.const ``Nat.succ []) ℓ')) (indices |>.push (.bvar 0)))) ++ fieldsProperty)))) (.bvar 2)) (.bvar 1)) (.bvar 0)) indices) (.bvar 4)) .default) .implicit) .implicit)) false) .default)
      hints := .opaque -- TODO
      safety := .safe
    }
    let corec := mkAppN (.const corecName (.param u :: levels)) (params.push σ ++ minors)
    for (field, minor, fieldType, majorIdx, isRec, _) in view.fields.zip <| minors.zip viewFields do
      forallTelescope (fieldType.instantiate1 coind) fun args body => do
      let indexVals := (← args[majorIdx]!.fvarId!.getType).getAppArgs[view.numParams:].toArray
      withLocalDeclD `s (mkAppN σ indexVals) fun s => do
      let corecApp := mkAppN corec (indexVals.push s)
      let mut eqArgs := params.push σ ++ minors ++ args[:majorIdx] |>.push s
      let mut lhs := .app (mkAppN (.const field.name levels) (params ++ args[:majorIdx])) corecApp
      let mut rhs := .app (mkAppN minor args[:majorIdx]) s
      if isRec then
        eqArgs := eqArgs ++ args[majorIdx + 1:]
        lhs := mkAppN lhs args[majorIdx + 1:]
        rhs := mkAppN corec (body.getAppArgs[view.numParams:].toArray.push (mkAppN rhs args[majorIdx + 1:]))
      let ty ← inferType rhs
      let tyLvl ← getLevel ty
      let fieldCorecName := field.name.str "corec"
      addDecl <| .thmDecl {
        name := fieldCorecName
        levelParams := u :: view.levelParams
        type := ← mkForallFVars eqArgs (.app (.app (.app (.const ``Eq [tyLvl]) ty) lhs) rhs)
        value := ← mkLambdaFVars eqArgs (.app (.app (.const ``Eq.refl [tyLvl]) ty) rhs)
      }
      validateDefEqAttr fieldCorecName
      defeqAttr.setTag fieldCorecName
      addSimpTheorem simpExtension fieldCorecName true false .global (eval_prio default)
      let fieldCorecHintName := fieldCorecName.str "hint"
      addDecl <| .defnDecl {
        name := fieldCorecHintName
        levelParams := u :: view.levelParams
        type := ← mkForallFVars eqArgs (.forallE `rhs ty (.sort .zero) .default)
        value := ← mkLambdaFVars eqArgs (.lam `rhs ty (.forallE `h (.app (.app (.app (.const ``Eq [tyLvl]) ty) rhs) (.bvar 0)) (.app (.app (.app (.const ``Eq [tyLvl]) ty) lhs) (.bvar 1)) .default) .default)
        hints := .abbrev -- TODO
        safety := .safe
      }
      --addUnificationHint fieldCorecHintName .global
    setIrreducibleAttribute corecName
  withLocalDeclsDND (fieldDecls.map fun (n, e) => (n, e.replaceFVar approxArg coind)) fun fields => do
    let fieldsVal ← (fields.zip <| viewFields.zip fieldDecls).mapM fun (field, (_, _, isRec, _), _, type) =>
      if isRec then
        forallTelescope type fun typeArgs _ =>
        mkLambdaFVars typeArgs (.app (.proj ``Subtype 0 (mkAppN field typeArgs)) ℓ)
      else
        return field
    let fieldsProperty ← (fields.zip <| viewFields.zip fieldDecls).mapM fun (field, (_, _, isRec, _), _, type) =>
      if isRec then
        forallTelescope type fun typeArgs _ =>
        mkLambdaFVars typeArgs (.app (.app (.app (.proj ``Subtype 1 (mkAppN field typeArgs)) ℓ) ℓ') h)
      else
        mkEqRefl field
    withNewBinderInfos indicesBinderInfos do
    addDecl <| .defnDecl {
      name := view.ctorName
      levelParams := view.levelParams
      type := ← mkForallFVars (params ++ indices ++ fields) (mkAppN coind indices)
      --value := ← mkLambdaFVars (params ++ indices ++ fields) (.letE `val (.forallE `ℓ (.const ``Nat []) (mkAppN (.app approx (.bvar 0)) indices) .default) (.app (.app (.app (.const ``Nat.rec [resultLevel]) (.lam `ℓ (.const ``Nat []) (mkAppN (.app approx (.bvar 0)) indices) .default)) (.const ``PUnit.unit [resultLevel])) (← mkLambdaFVars #[ℓ] (.lam `mk (mkAppN (.app approx ℓ) indices) (mkAppN (.app patternCtor (.app approx ℓ)) (indices ++ fieldsVal)) .default))) (.app (.app (.app (.app (.const ``Subtype.mk [resultLevel]) α) β) (.bvar 0)) (.app (.app (.app (.const ``Nat.le.ndrec []) (.lam `ℓ (.const ``Nat []) (.lam `ℓ' (.const ``Nat []) (mkAppN (.app (.app agree (.bvar 1)) (.bvar 0)) (indices.push (.app (.bvar 2) (.bvar 1)) |>.push (.app (.bvar 2) (.bvar 0)))) .default) .default)) (.lam `ℓ' (.const ``Nat []) (.const ``True.intro []) .default)) (← mkLambdaFVars #[ℓ, ℓ', h] (.lam `ih (mkAppN (.app (.app agree (.bvar 2)) (.bvar 1)) (indices.push (.app (.bvar 3) (.bvar 2)) |>.push (.app (.bvar 3) (.bvar 1)))) (mkAppN (.app (.app (.app agreePatternCtor (.app approx ℓ)) (.app approx ℓ')) (.app (.app agree ℓ) ℓ')) ((indices.push (.app (.bvar 4) (.app (.const ``Nat.succ []) ℓ)) |>.push (.app (.bvar 4) (.app (.const ``Nat.succ []) ℓ'))) ++ fieldsProperty)) .default)))) false)
      value := ← mkLambdaFVars (params ++ indices ++ fields) (.letE `val (.forallE `ℓ (.const ``Nat []) (mkAppN (.app approx (.bvar 0)) indices) .default) (.lam `ℓ (.const ``Nat []) (.app (.app (.app (.app (.const ``Nat.rec [resultLevel]) (.lam `ℓ (.const ``Nat []) (mkAppN (.app approx (.bvar 0)) indices) .default)) (.const ``PUnit.unit [resultLevel])) (← mkLambdaFVars #[ℓ] (.lam `mk (mkAppN (.app approx ℓ) indices) (mkAppN (.app patternCtor (.app approx ℓ)) (indices ++ fieldsVal)) .default))) (.bvar 0)) .default) (.app (.app (.app (.app (.const ``Subtype.mk [resultLevel]) α) β) (.bvar 0)) (.app (.app (.app (.const ``Nat.le.ndrec []) (.lam `ℓ (.const ``Nat []) (.lam `ℓ' (.const ``Nat []) (mkAppN (.app (.app agree (.bvar 1)) (.bvar 0)) (indices.push (.app (.bvar 2) (.bvar 1)) |>.push (.app (.bvar 2) (.bvar 0)))) .default) .default)) (.lam `ℓ' (.const ``Nat []) (.const ``True.intro []) .default)) (← mkLambdaFVars #[ℓ, ℓ', h] (.lam `ih (mkAppN (.app (.app agree (.bvar 2)) (.bvar 1)) (indices.push (.app (.bvar 3) (.bvar 2)) |>.push (.app (.bvar 3) (.bvar 1)))) (mkAppN (.app (.app (.app agreePatternCtor (.app approx ℓ)) (.app approx ℓ')) (.app (.app agree ℓ) ℓ')) ((indices.push (.app (.bvar 4) (.app (.const ``Nat.succ []) ℓ)) |>.push (.app (.bvar 4) (.app (.const ``Nat.succ []) ℓ'))) ++ fieldsProperty)) .default)))) false)
      hints := .abbrev -- .opaque -- TODO
      safety := .safe
    }
    let ctor := mkAppN (.const view.ctorName levels) params
    for (field, (fieldType, majorIdx, _), fieldIdx) in view.fields.zip viewFields.zipIdx do
      forallBoundedTelescope (fieldType.instantiate1 coind) majorIdx fun args body =>
      let indexVals := body.bindingDomain!.getAppArgs[view.numParams:].toArray
      withLocalDeclsDND (fieldDecls.map fun (n, e) => (n, e.replaceFVars (indices.push approxArg) (indexVals.push coind))) fun fields => do
      let eqArgs := params ++ args ++ fields
      let lhs := .app (mkAppN (.const field.name levels) (params ++ args)) (mkAppN ctor (indexVals ++ fields))
      let rhs := mkAppN fields[fieldIdx]! (args ++ (← indexVals.mapM mkEqRefl))
      let ty ← inferType rhs
      let tyLvl ← getLevel ty
      let fieldCtorName := field.name.str view.ctorName.getString!
      addDecl <| .thmDecl {
        name := fieldCtorName
        levelParams := view.levelParams
        type := ← mkForallFVars eqArgs (.app (.app (.app (.const ``Eq [tyLvl]) ty) lhs) rhs)
        value := ← mkLambdaFVars eqArgs (.app (.app (.const ``Eq.refl [tyLvl]) ty) rhs)
      }
      validateDefEqAttr fieldCtorName
      defeqAttr.setTag fieldCtorName
      addSimpTheorem simpExtension fieldCtorName true false .global (eval_prio default)
      let fieldCtorHintName := fieldCtorName.str "hint"
      addDecl <| .defnDecl {
        name := fieldCtorHintName
        levelParams := view.levelParams
        type := ← mkForallFVars eqArgs (.forallE `rhs ty (.sort .zero) .default)
        value := ← mkLambdaFVars eqArgs (.lam `rhs ty (.forallE `h (.app (.app (.app (.const ``Eq [tyLvl]) ty) rhs) (.bvar 0)) (.app (.app (.app (.const ``Eq [tyLvl]) ty) lhs) (.bvar 1)) .default) .default)
        hints := .opaque -- TODO
        safety := .safe
      }
      --addUnificationHint fieldCtorHintName .global
      setIrreducibleAttribute field.name
    setIrreducibleAttribute view.ctorName
  setIrreducibleAttribute view.name
  withLocalDeclD `r (← mkForallFVars indices (.forallE `lhs (mkAppN coind indices) (.forallE `rhs (mkAppN coind indices) (.sort .zero) .default) .default)) fun r => do
  let extMinors ← (view.fields.zip viewFields).mapM fun (field, fieldType, majorIdx, isRec, _) =>
    forallBoundedTelescope (fieldType.instantiate1 approxArg) majorIdx fun fieldArgs fieldBody =>
    let indexVals := fieldBody.bindingDomain!.getAppArgs
    withLocalDeclD `lhs (mkAppN coind indexVals) fun lhs =>
    withLocalDeclD `rhs (mkAppN coind indexVals) fun rhs =>
    withLocalDeclD `h (mkAppN r (indexVals.push lhs |>.push rhs)) fun h =>
    let body := fieldBody.bindingBody!
    if isRec then
      forallTelescope body fun bodyArgs bodyType =>
      return (field.name.componentsRev.head!, ← mkForallFVars ((fieldArgs.push lhs |>.push rhs |>.push h) ++ bodyArgs) (mkAppN r (bodyType.getAppArgs.push (mkAppN (.const field.name levels) ((params ++ fieldArgs |>.push lhs) ++ bodyArgs)) |>.push (mkAppN (.const field.name levels) ((params ++ fieldArgs |>.push rhs) ++ bodyArgs)))))
    else
      return (field.name.componentsRev.head!, ← mkForallFVars (fieldArgs.push lhs |>.push rhs |>.push h) (.app (.app (.app (.const ``Eq [← getLevel body]) body) (mkAppN (.const field.name levels) (params ++ fieldArgs |>.push lhs))) (mkAppN (.const field.name levels) (params ++ fieldArgs |>.push rhs))))
  withLocalDeclsDND extMinors fun extMinors => do
  withLocalDeclD `ih (← mkForallFVars indices (.forallE `lhs (mkAppN coind indices) (.forallE `rhs (mkAppN coind indices) (.forallE `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.const ``Eq [resultLevel]) (mkAppN (.app approx ℓ) indices)) (.app (.proj ``Subtype 0 (.bvar 2)) ℓ)) (.app (.proj ``Subtype 0 (.bvar 1)) ℓ)) .default) .default) .default)) fun ih =>
  withLocalDeclD `lhs (mkAppN coind indices) fun lhs =>
  withLocalDeclD `rhs (mkAppN coind indices) fun rhs =>
  withLocalDeclD `h (mkAppN r (indices.push lhs |>.push rhs)) fun h => do
  let lhs' := .app (.proj ``Subtype 0 lhs) (.app (.const ``Nat.succ []) ℓ)
  let rhs' := .app (.proj ``Subtype 0 rhs) (.app (.const ``Nat.succ []) ℓ)
  let mut lhsCtor := mkAppN (.app patternCtor (.app approx ℓ)) indices
  let mut rhsCtor := lhsCtor
  let mut ctorType ← withLocalDeclsDND (fieldDecls.map fun (n, e) => (n, e.replaceFVar approxArg (.app approx ℓ))) fun fields => mkForallFVars fields (mkAppN (.app pattern (.app approx ℓ)) indices)
  let mut pf : Expr := .app (.app (.const ``Eq.refl [resultLevel]) ctorType) lhsCtor
  for ((_, fieldType), field, (_, majorIdx, isRec, _), fieldIdx) in fieldDecls.zip <| view.fields.zip viewFields.zipIdx do
    let fieldType := fieldType.replaceFVar approxArg (.app approx ℓ)
    let fieldTypeLevel ← getLevel fieldType
    let lhsField := .proj patternName fieldIdx lhs'
    let rhsField := .proj patternName fieldIdx rhs'
    let eq ← forallBoundedTelescope fieldType (majorIdx + indices.size) fun args body => do
      let bodyLevel ← getLevel body
      let mut indexVals ← args[majorIdx:].toArray.mapM fun arg => return (← arg.fvarId!.getType).eq?.get!.snd.snd
      let mut argVals := args
      for i in [majorIdx:majorIdx + indices.size] do
        let (idxTy, _, idxRhs) := (← argVals[i]!.fvarId!.getType).eq?.get!
        argVals := argVals.set! i (.app (.app (.const ``Eq.refl [← getLevel idxTy]) idxTy) idxRhs)
      let mut eq ←
        withLocalDeclD `lhs (mkAppN coind indexVals) fun lhs =>
        withLocalDeclD `rhs (mkAppN coind indexVals) fun rhs =>
        withLocalDeclD `h (mkAppN r ((indexVals.push lhs |>.push rhs))) fun h =>
        if isRec then
          forallTelescope body fun bodyArgs bodyType => do
          let bodyIndexVals := bodyType.getAppArgs[view.numParams + 1:]
          let mut lhsBody := mkAppN (.proj patternName fieldIdx (.app (.proj ``Subtype 0 lhs) (.app (.const ``Nat.succ []) ℓ))) (argVals ++ bodyArgs)
          let mut rhsBody := mkAppN (.proj patternName fieldIdx (.app (.proj ``Subtype 0 rhs) (.app (.const ``Nat.succ []) ℓ))) (argVals ++ bodyArgs)
          let mut eq := .app (.app (.app (mkAppN ih bodyIndexVals) (mkAppN (.const field.name levels) ((params ++ args[:majorIdx] |>.push lhs) ++ bodyArgs))) (mkAppN (.const field.name levels) ((params ++ args[:majorIdx] |>.push rhs) ++ bodyArgs))) (mkAppN extMinors[fieldIdx]! ((args[:majorIdx].toArray.push lhs |>.push rhs |>.push h) ++ bodyArgs))
          let mut bodyType := bodyType
          for arg in bodyArgs.reverse do
            let argTy ← arg.fvarId!.getType
            lhsBody ← mkLambdaFVars #[arg] lhsBody
            rhsBody ← mkLambdaFVars #[arg] rhsBody
            eq := .app (.app (.app (.app (.app (.const ``funext [← getLevel argTy, ← getLevel bodyType]) argTy) (← mkLambdaFVars #[arg] bodyType)) lhsBody) rhsBody) (← mkLambdaFVars #[arg] eq)
            bodyType ← mkForallFVars #[arg] bodyType
          mkLambdaFVars #[lhs, rhs, h] eq
        else
          let eqLhs₀ := .proj patternName fieldIdx (.app (.proj ``Subtype 0 lhs) (.app (.const ``Nat.succ []) ℓ))
          let eqLhs := mkAppN eqLhs₀ argVals
          let eqRhs₀ := .proj patternName fieldIdx (.app (.proj ``Subtype 0 rhs) (.app (.const ``Nat.succ []) ℓ))
          let eqRhs := mkAppN eqRhs₀ argVals
          let eqLhs₀' := .proj patternName fieldIdx (.app (.proj ``Subtype 0 lhs) (.app (.const ``Nat.succ []) (.const ``Nat.zero [])))
          let eqLhs' := mkAppN eqLhs₀' argVals
          let eqRhs₀' := .proj patternName fieldIdx (.app (.proj ``Subtype 0 rhs) (.app (.const ``Nat.succ []) (.const ``Nat.zero [])))
          let eqRhs' := mkAppN eqRhs₀' argVals
          let fieldType := fieldType.replaceFVars indices indexVals
          let eq₁ := .proj agreePatternName fieldIdx (.app (.app (.app (.proj ``Subtype 1 lhs) (.app (.const ``Nat.succ []) (.const ``Nat.zero []))) (.app (.const ``Nat.succ []) ℓ)) (.app (.app (.const ``Nat.le_add_left []) (.app (.const ``Nat.succ []) (.const ``Nat.zero []))) ℓ))
          let eq₁ := .app (.app (.app (.app (.app (.app (.const ``congrArg [fieldTypeLevel, bodyLevel]) fieldType) body) eqLhs₀') eqLhs₀) (.lam `f fieldType (mkAppN (.bvar 0) argVals) .default)) eq₁
          let eq₂ := mkAppN extMinors[fieldIdx]! (args[:majorIdx].toArray.push lhs |>.push rhs |>.push h)
          let eq₃ := .proj agreePatternName fieldIdx (.app (.app (.app (.proj ``Subtype 1 rhs) (.app (.const ``Nat.succ []) (.const ``Nat.zero []))) (.app (.const ``Nat.succ []) ℓ)) (.app (.app (.const ``Nat.le_add_left []) (.app (.const ``Nat.succ []) (.const ``Nat.zero []))) ℓ))
          let eq₃ := .app (.app (.app (.app (.app (.app (.const ``congrArg [fieldTypeLevel, bodyLevel]) fieldType) body) eqRhs₀') eqRhs₀) (.lam `f fieldType (mkAppN (.bvar 0) argVals) .default)) eq₃
          mkLambdaFVars #[lhs, rhs, h] (.app (.app (.app (.app (.app (.app (.const ``Eq.trans [bodyLevel]) body) eqLhs) eqLhs') eqRhs) (.app (.app (.app (.app (.const ``Eq.symm [bodyLevel]) body) eqLhs') eqLhs) eq₁)) (.app (.app (.app (.app (.app (.app (.const ``Eq.trans [bodyLevel]) body) eqLhs') eqRhs') eqRhs) eq₂) eq₃))
      let mut lhsBody := mkAppN lhsField args
      let mut rhsBody := mkAppN rhsField args
      for (index, idx) in indices.zipIdx.reverse do
        let indexTy ← index.fvarId!.getType
        let indexLvl ← getLevel indexTy
        let indexVal := indexVals[idx]!
        let eqArg := args[majorIdx + idx]!
        indexVals := indexVals.set! idx index
        argVals := argVals.set! (majorIdx + idx) (.app (.app (.app (.app (.const ``Eq.symm [indexLvl]) indexTy) indexVal) index) (.bvar 3))
        eq := .app (.app (.app (.app (.app (.app (.const ``Eq.rec [.zero, indexLvl]) indexTy) indexVal) (← mkLambdaFVars #[index] (.lam `h (.app (.app (.app (.const ``Eq [indexLvl]) indexTy) indexVal) index) (.forallE `lhs (mkAppN coind indexVals) (.forallE `rhs (mkAppN coind indexVals) (.forallE `h (mkAppN r (indexVals.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.const ``Eq [bodyLevel]) body) (mkAppN (.proj patternName fieldIdx (.app (.proj ``Subtype 0 (.bvar 2)) (.app (.const ``Nat.succ []) ℓ))) argVals)) (mkAppN (.proj patternName fieldIdx (.app (.proj ``Subtype 0 (.bvar 1)) (.app (.const ``Nat.succ []) ℓ))) argVals)) .default) .default) .default) .default))) eq) index) (.app (.app (.app (.app (.const ``Eq.symm [indexLvl]) indexTy) index) indexVal) eqArg)
        argVals := argVals.set! (majorIdx + idx) eqArg
      let mut body := body
      eq := .app (.app (.app eq lhs) rhs) h
      for arg in args.reverse do
        let argTy ← arg.fvarId!.getType
        lhsBody ← mkLambdaFVars #[arg] lhsBody
        rhsBody ← mkLambdaFVars #[arg] rhsBody
        eq := .app (.app (.app (.app (.app (.const ``funext [← getLevel argTy, ← getLevel body]) argTy) (← mkLambdaFVars #[arg] body)) lhsBody) rhsBody) (← mkLambdaFVars #[arg] eq)
        body ← mkForallFVars #[arg] body
      return eq
    ctorType := ctorType.bindingBody!
    pf := .app (.app (.app (.app (.app (.app (.app (.app (.const ``congr [fieldTypeLevel, ← getLevel ctorType]) fieldType) ctorType) lhsCtor) rhsCtor) lhsField) rhsField) pf) eq
    lhsCtor := .app lhsCtor lhsField
    rhsCtor := .app rhsCtor rhsField
  addDecl <| .thmDecl {
    name := view.name.str "ext"
    levelParams := view.levelParams
    type := ← withNewBinderInfos indicesBinderInfos <| mkForallFVars (params.push r ++ extMinors ++ indices) (.forallE `lhs (mkAppN coind indices) (.forallE `rhs (mkAppN coind indices) (.forallE `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.const ``Eq [resultLevel]) (mkAppN coind indices)) (.bvar 2)) (.bvar 1)) .default) .implicit) .implicit)
    value := ← mkLambdaFVars (params.push r ++ extMinors ++ indices) (.lam `lhs (mkAppN coind indices) (.lam `rhs (mkAppN coind indices) (.lam `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.app (.app (.const ``Subtype.eq' [resultLevel]) α) β) (.bvar 2)) (.bvar 1)) (.app (.app (.app (.app (.app (.const ``funext [1, resultLevel]) (.const ``Nat [])) (.lam `ℓ (.const ``Nat []) (mkAppN (.app approx (.bvar 0)) indices) .default)) (.proj ``Subtype 0 (.bvar 2))) (.proj ``Subtype 0 (.bvar 1))) (.lam `ℓ (.const ``Nat []) (mkAppN (.app (.app (.app (.app (.const ``Nat.rec [.zero]) (← mkLambdaFVars #[ℓ] (← mkForallFVars indices (.forallE `lhs (mkAppN coind indices) (.forallE `rhs (mkAppN coind indices) (.forallE `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.const ``Eq [resultLevel]) (mkAppN (.app approx ℓ) indices)) (.app (.proj ``Subtype 0 (.bvar 2)) ℓ)) (.app (.proj ``Subtype 0 (.bvar 1)) ℓ)) .default) .default) .default)))) (← mkLambdaFVars indices (.lam `lhs (mkAppN coind indices) (.lam `rhs (mkAppN coind indices) (.lam `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.const ``Eq.refl [resultLevel]) (.const ``PUnit [resultLevel])) (.const ``PUnit.unit [resultLevel])) .default) .default) .default))) (← mkLambdaFVars (#[ℓ, ih] ++ indices |>.push lhs |>.push rhs |>.push h) pf)) (.bvar 0)) (indices.push (.bvar 3) |>.push (.bvar 2) |>.push (.bvar 1))) .default))) .default) .default) .default)
  }

open Elab Parser

def coinductiveFields := leading_parser
  manyIndent <| ppLine >> checkColGe >> ppGroup (atomic (Command.declModifiers true >> ident) >> Command.declSig)

-- TODO: redo this
elab modifiers:declModifiers "coinductive " id:declId sig:declSig " where " ctor:(Command.structCtor)? fields:coinductiveFields : command => do
  let modifiers ← elabModifiers modifiers
  let ⟨name, declName, levelNames⟩ ← Command.liftTermElabM <| Term.expandDeclId (← getCurrNamespace) (← Command.getLevelNames) id modifiers
  let (binders, typeStx) := expandDeclSig sig
  let view ← Command.liftTermElabM <| Term.withLevelNames levelNames <| Term.withAutoBoundImplicit <| Term.elabBinders binders.getArgs fun params => do
    let levelNames ← Term.getLevelNames
    let type ← Term.elabType typeStx
    let ctorName ←
      if let some ctor := ctor then
        let `(Command.structCtor| $_ctorModifiers:declModifiers $ctorId ::) := ctor
          | unreachable!
        pure (declName ++ ctorId.getId)
      else
        pure (declName.str "mk")
    let `(coinductiveFields| $[$fieldModifiers:declModifiers $fieldIds $fieldSigs]*) := fields
      | unreachable!
    let type ← mkForallFVars params type
    let fields ← withAuxDecl name type declName fun aux => (fieldIds.zip fieldSigs).mapM fun (fieldId, fieldSig) =>
      let (binders, typeStx) := expandDeclSig fieldSig
      Term.elabBinders binders.getArgs fun args => do
      let type ← Term.elabType typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let paramBinderInfos ← params.mapM fun param => do
        let param := param.fvarId!
        let bi ← param.getBinderInfo
        return (param, if bi.isExplicit then .implicit else bi)
      withNewBinderInfos paramBinderInfos do
      return {
        name := declName ++ fieldId.getId
        type := ← instantiateMVars <| ← eraseRecAppSyntaxExpr <| ((← mkForallFVars (params ++ args) type).abstract #[aux])
      }
    return {
      name := declName
      levelParams := levelNames
      type := ← instantiateMVars type
      numParams := params.size
      ctorName
      fields
      : CoinductiveType
    }
  if view.type.hasFVar || view.type.hasMVar then
    throwError "bad type"
  if view.fields.any fun field => field.type.hasFVar || field.type.hasMVar then
    throwError "bad fields"
  Command.liftTermElabM view.elab

/-
coinductive Colist.{u} (α : Type u) : Type u where
  head : Option α
  tail : head.isSome → Colist α
-/

coinductive InfStream (α : Type u) : Type u where
  hd : α
  tl : InfStream α

noncomputable
def InfStream.ofFn (f : Nat → α) : InfStream α :=
  .corec Nat f (· + 1) 0

noncomputable
def InfStream.get (s : InfStream α) : Nat → α
  | 0 => s.hd
  | n + 1 => s.tl.get n

theorem InfStream.get_ofFn : get (ofFn f) = f := by
  funext n
  suffices ∀ k, get (.corec Nat f (· + 1) k) n = f (n + k) from this 0
  intro k
  induction n generalizing k with simp! [*]
  | succ => grind

theorem InfStream.ext' : (∀ n, get s n = get s' n) → s = s' :=
  ext (fun lhs rhs => ∀ n, get lhs n = get rhs n) (fun _ _ h => h 0) (fun _ _ h n => h (n + 1))

theorem InfStream.ofFn_get : ofFn (get s) = s := by
  apply ext'
  intro n
  rw [get_ofFn]

set_option linter.unusedVariables false

coinductive Vec (α : Type u) : (n : Nat) → Type u where
  hd {n} (xs : Vec α (n + 1)) : α
  tl {n} (xs : Vec α (n + 1)) : Vec α n

noncomputable
def Vec.nil {α : Type u} : Vec α .zero :=
  .mk nofun nofun

noncomputable
def Vec.cons {α : Type u} {n} (hd : α) (tl : Vec α n) : Vec α n.succ :=
  .mk (fun _ => hd) fun h => Nat.succ.inj h ▸ tl

coinductive Collection.{u} (α : Type u) : (n : Nat) → Type u where
  push {n} (self : Collection α n) (x : α) : Collection α (n + 1)
  peek {n} (self : Collection α (n + 1)) : α
  pop {n} (self : Collection α (n + 1)) : Collection α n

noncomputable
def specQueue : Vector α n → Collection α n :=
  .corec (Vector α) (·.insertIdx 0) Vector.back .pop

structure BatchedQueue (α : Type u) (n : Nat) where
  n₁ : Nat
  n₂ : Nat
  hn : n = n₁ + n₂
  inlist : Vector α n₁
  outlist : Vector α n₂

noncomputable
def batchedQueue : BatchedQueue α n → Collection α n :=
  .corec (BatchedQueue α) (fun s x => ⟨s.n₁ + 1, s.n₂, by have := s.hn; omega, s.inlist.push x, s.outlist⟩) (fun s => match h : s.n₂ with | 0 => (@s.inlist.head) ⟨by have := s.hn; omega⟩ | _ + 1 => (@s.outlist.back) ⟨by omega⟩) (fun s => match h : s.n₂ with | 0 => ⟨0, s.n₁ - 1, by have := s.hn; omega, #v[], s.inlist.reverse.pop⟩ | n₂ + 1 => ⟨s.n₁, n₂, by have := s.hn; omega, s.inlist, s.outlist.pop.cast (by omega)⟩)

example : @specQueue α 0 #v[] = batchedQueue ⟨0, 0, rfl, #v[], #v[]⟩ := by
  apply Collection.ext fun _ lhs rhs => ∃ s, rhs = batchedQueue s ∧ lhs = specQueue ((s.inlist.reverse ++ s.outlist).cast s.hn.symm)
  case h => exact ⟨_, rfl, rfl⟩
  case push =>
    intro n _ _ ⟨s, h₁, h₂⟩ x
    cases h₁
    cases h₂
    dsimp [specQueue, batchedQueue]
    refine ⟨_, rfl, ?_⟩
    congr
    simp [← Vector.toArray_inj]
  case peek =>
    intro n _ _ ⟨s, h₁, h₂⟩
    cases h₁
    cases h₂
    rcases s with ⟨n₁, n₂, hn, inlist, outlist⟩
    dsimp [specQueue, batchedQueue]
    simp [Vector.back]
    split <;> cases hn <;> simp
    rfl
  case pop =>
    intro n _ _ ⟨s, h₁, h₂⟩
    cases h₁
    cases h₂
    dsimp [specQueue, batchedQueue]
    refine ⟨_, rfl, ?_⟩
    congr
    rcases s with ⟨n₁, n₂, hn, inlist, outlist⟩
    simp [← Vector.toArray_inj]
    split <;> simp [Vector.eq_empty]

coinductive Stack.{u} (α : Nat → Sort u) : Nat → Sort (max 1 u) where
  push {n} (xs : Stack α n) (x : α n) : Stack α (n + 1)
  peek {n} (xs : Stack α (n + 1)) : α n
  pop {n} (xs : Stack α (n + 1)) : Stack α n

noncomputable
def stack (f : (i : Fin n) → α i) : Stack α n :=
  .corec (fun n => (i : Fin n) → α i) (fun f x => Fin.lastCases x f) (· (Fin.last _)) (· ·.castSucc) f

coinductive IndexTest : Id (Nat → Id (Nat → Id Type)) where
  get (m n : Nat) (self : IndexTest n.succ m) (k : Nat) : IndexTest n m.succ

def NatUnOp := Nat → Nat

coinductive SimpleTest : Nat → Type where
  get (n : Nat) (self : SimpleTest n) : NatUnOp

coinductive LazyProd.{u, v} (α : Type u) (β : Type v) : Type (max u v) where
  fst : α
  snd : β

coinductive DependentTest : (n : Nat) → Type where
  out n m (self : DependentTest (.add n m)) k : Fin (n.add k)
  inner n m (self : DependentTest (.add n m)) k : DependentTest (n.add k)

coinductive UnivTest : Type 1 → Type where
  get (self : UnivTest Type) : Unit

coinductive UnivTest' : Type → Type 1 where
  get {α : Type} (self : UnivTest' α) : α

coinductive UnivTest2 (α : Sort u) : α → Type where
  get (x : α) (self : UnivTest2 α x) : True
