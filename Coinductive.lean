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

-- TODO: change view format
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
    let rec findMajorIdx idx
      | .forallE _ d b _ =>
        d.withApp fun fn args => do
        if fn == .bvar idx then
          if args.any (·.hasLooseBVar idx) then
            throwError "invalid field {field.name}: invalid recursive occurrence"
          return (idx, b)
        if d.hasLooseBVar idx then
          throwError "invalid field {field.name}: invalid recursive occurrence"
        findMajorIdx (idx + 1) b
      | _ => throwError "invalid field {field.name}: missing self argument"
    let (majorIdx, ty) ← findMajorIdx 0 field.type
    let rec isRec idx
      | .forallE _ d b _ => do
        if d.hasLooseBVar idx then
          throwError "invalid field {field.name}: invalid recursive occurrence"
        isRec (idx + 1) b
      | ty =>
        ty.withApp fun fn args => do
        if fn == .bvar idx then
          if args.any (·.hasLooseBVar idx) then
            throwError "invalid field {field.name}: invalid recursive occurrence"
          return true
        if ty.hasLooseBVar idx then
          throwError "invalid field {field.name}: invalid recursive occurrence"
        return false
    return (majorIdx, ← isRec (majorIdx + 1) ty)
  withLocalDeclD `Approx type fun approxArg => do
  let fieldDecls ← (view.fields.zip viewFields).mapM fun (field, majorIdx, _) =>
    forallBoundedTelescope (field.type.instantiateRev (params.push approxArg)) majorIdx fun preArgs fieldType => do
    let eqs ← (indices.zip fieldType.bindingDomain!.getAppArgs).mapM fun (index, indexVal) => return (`h, ← mkEq index indexVal)
    withLocalDeclsDND eqs fun eqs =>
    return (field.name.componentsRev.head!, ← mkForallFVars (preArgs ++ eqs) fieldType.bindingBody!)
  let approxName := view.name.str "Approx"
  let patternName := approxName.str "Pattern"
  let patternCtorName := patternName.str "mk"
  let pattern := mkAppN (.const patternName levels) params
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
    let ihs ← (fieldDecls.zip viewFields).mapIdxM fun fieldIdx (⟨_, type⟩, _, isRec) =>
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
  let paramBinderInfos ← params.mapM fun param => do
    let param := param.fvarId!
    let bi ← param.getBinderInfo
    return (param, if bi.isExplicit then .implicit else bi)
  withNewBinderInfos paramBinderInfos do
  for (field, (majorIdx, isRec), fieldIdx) in view.fields.zip viewFields.zipIdx do
    let type := field.type.instantiateRev (params.push coind)
    addDecl <| .defnDecl {
      name := field.name
      levelParams := view.levelParams
      type := ← mkForallFVars params type
      value := ← mkLambdaFVars params <| ← forallTelescope type fun args body => do
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
  let u := getUnusedLevelParam view.levelParams
  withLocalDeclD `σ (← mkForallFVars indices (.sort (.param u))) fun σ =>
    let minors := view.fields.map fun field => (field.name.componentsRev.head!, field.type.instantiateRev (params.push σ))
    withLocalDeclsDND minors fun minors => do
    withLocalDeclD `corec (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app approx ℓ) indices) .default)) fun corec => do
    withLocalDeclD `ih (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app (.app agree ℓ) ℓ') (indices.push (.app (mkAppN (.app (.bvar (indices.size + 7)) ℓ) indices) (.bvar 0)) |>.push (.app (mkAppN (.app (.bvar (indices.size + 7)) ℓ') indices) (.bvar 0)))) .default)) fun ih =>
    withLocalDeclD `s (mkAppN σ indices) fun s => do
    let fieldsVal ← (viewFields.zip <| minors.zip fieldDecls).mapM fun ⟨(majorIdx, isRec), minor, _, type⟩ =>
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
      type := ← mkForallFVars (params.push σ ++ minors ++ indices) (.forallE `s (mkAppN σ indices) (mkAppN coind indices) .default)
      value := ← mkLambdaFVars (params.push σ ++ minors ++ indices) (.lam `s (mkAppN σ indices) (.letE `val (← mkForallFVars (#[ℓ] ++ indices) (.forallE `s (mkAppN σ indices) (mkAppN (.app approx ℓ) indices) .default)) (.app (.app (.app (.const ``Nat.rec [.max recLevel (.param u)]) (← mkLambdaFVars #[ℓ] (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app approx ℓ) indices) .default)))) (← mkLambdaFVars indices (.lam `s (mkAppN σ indices) (.const ``PUnit.unit [resultLevel]) .default))) (← mkLambdaFVars (#[ℓ, corec] ++ indices |>.push s) (mkAppN (.app patternCtor (.app approx ℓ)) (indices ++ fieldsVal)))) (.app (.app (.app (.app (.const ``Subtype.mk [resultLevel]) α) β) (.lam `ℓ (.const ``Nat []) (.app (mkAppN (.app (.bvar 1) (.bvar 0)) indices) (.bvar 2)) .default)) (.lam `ℓ (.const ``Nat []) (.lam `ℓ' (.const ``Nat []) (.lam `h (.app (.app (.const ``Nat.le []) (.bvar 1)) (.bvar 0)) (.app (mkAppN (.app (.app (.app (.app (.app (.app (.const ``Nat.le.ndrec []) (← mkLambdaFVars #[ℓ, ℓ'] (← mkForallFVars indices (.forallE `s (mkAppN σ indices) (mkAppN (.app (.app agree ℓ) ℓ') (indices.push (.app (mkAppN (.app (.bvar (indices.size + 6)) ℓ) indices) (.bvar 0)) |>.push (.app (mkAppN (.app (.bvar (indices.size + 6)) ℓ') indices) (.bvar 0)))) .default)))) (.lam `ℓ' (.const ``Nat []) (← mkLambdaFVars indices (.lam `s (mkAppN σ indices) (.const ``True.intro []) .default)) .default)) (← mkLambdaFVars (#[ℓ, ℓ', h, ih] ++ indices |>.push s) (mkAppN (.app (.app (.app agreePatternCtor (.app approx ℓ)) (.app approx ℓ')) (.app (.app agree ℓ) ℓ')) ((indices.push (mkAppN (.app (.bvar (indices.size + 8)) (.app (.const ``Nat.succ []) ℓ)) (indices |>.push (.bvar 0))) |>.push (mkAppN (.app (.bvar (indices.size + 8)) (.app (.const ``Nat.succ []) ℓ')) (indices |>.push (.bvar 0)))) ++ fieldsProperty)))) (.bvar 2)) (.bvar 1)) (.bvar 0)) indices) (.bvar 4)) .default) .implicit) .implicit)) false) .default)
      hints := .opaque -- TODO
      safety := .safe
    }
    let corec := mkAppN (.const corecName (.param u :: levels)) (params.push σ ++ minors)
    for (field, minor, majorIdx, isRec) in view.fields.zip <| minors.zip viewFields do
      forallTelescope (field.type.instantiateRev (params.push coind)) fun args body => do
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
    let fieldsVal ← (fields.zip <| viewFields.zip fieldDecls).mapM fun (field, (_, isRec), _, type) =>
      if isRec then
        forallTelescope type fun typeArgs _ =>
        mkLambdaFVars typeArgs (.app (.proj ``Subtype 0 (mkAppN field typeArgs)) ℓ)
      else
        return field
    let fieldsProperty ← (fields.zip <| viewFields.zip fieldDecls).mapM fun (field, (_, isRec), _, type) =>
      if isRec then
        forallTelescope type fun typeArgs _ =>
        mkLambdaFVars typeArgs (.app (.app (.app (.proj ``Subtype 1 (mkAppN field typeArgs)) ℓ) ℓ') h)
      else
        mkEqRefl field
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
    for (field, (majorIdx, _), fieldIdx) in view.fields.zip viewFields.zipIdx do
      forallBoundedTelescope (field.type.instantiateRev (params.push coind)) majorIdx fun args body =>
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
  let extMinors ← (view.fields.zip viewFields).mapM fun (field, majorIdx, isRec) =>
    forallBoundedTelescope (field.type.instantiateRev (params.push approxArg)) majorIdx fun fieldArgs fieldBody =>
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
  for ((_, fieldType), field, (majorIdx, isRec), fieldIdx) in fieldDecls.zip <| view.fields.zip viewFields.zipIdx do
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
    type := ← mkForallFVars (params.push r ++ extMinors ++ indices) (.forallE `lhs (mkAppN coind indices) (.forallE `rhs (mkAppN coind indices) (.forallE `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.const ``Eq [resultLevel]) (mkAppN coind indices)) (.bvar 2)) (.bvar 1)) .default) .default) .default)
    value := ← mkLambdaFVars (params.push r ++ extMinors ++ indices) (.lam `lhs (mkAppN coind indices) (.lam `rhs (mkAppN coind indices) (.lam `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.app (.app (.const ``Subtype.eq' [resultLevel]) α) β) (.bvar 2)) (.bvar 1)) (.app (.app (.app (.app (.app (.const ``funext [1, resultLevel]) (.const ``Nat [])) (.lam `ℓ (.const ``Nat []) (mkAppN (.app approx (.bvar 0)) indices) .default)) (.proj ``Subtype 0 (.bvar 2))) (.proj ``Subtype 0 (.bvar 1))) (.lam `ℓ (.const ``Nat []) (mkAppN (.app (.app (.app (.app (.const ``Nat.rec [.zero]) (← mkLambdaFVars #[ℓ] (← mkForallFVars indices (.forallE `lhs (mkAppN coind indices) (.forallE `rhs (mkAppN coind indices) (.forallE `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.app (.const ``Eq [resultLevel]) (mkAppN (.app approx ℓ) indices)) (.app (.proj ``Subtype 0 (.bvar 2)) ℓ)) (.app (.proj ``Subtype 0 (.bvar 1)) ℓ)) .default) .default) .default)))) (← mkLambdaFVars indices (.lam `lhs (mkAppN coind indices) (.lam `rhs (mkAppN coind indices) (.lam `h (mkAppN r (indices.push (.bvar 1) |>.push (.bvar 0))) (.app (.app (.const ``Eq.refl [resultLevel]) (.const ``PUnit [resultLevel])) (.const ``PUnit.unit [resultLevel])) .default) .default) .default))) (← mkLambdaFVars (#[ℓ, ih] ++ indices |>.push lhs |>.push rhs |>.push h) pf)) (.bvar 0)) (indices.push (.bvar 3) |>.push (.bvar 2) |>.push (.bvar 1))) .default))) .default) .default) .default)
  }

open Elab Parser

def coinductiveFields := leading_parser
  manyIndent <| ppLine >> checkColGe >> ppGroup (atomic (Command.declModifiers true >> ident) >> Command.declSig)

-- TODO: redo this
-- TODO: auto insert self if no indices
elab modifiers:declModifiers "coinductive " id:declId sig:declSig " where " ctor:(Command.structCtor)? fields:coinductiveFields : command => do
  let modifiers ← elabModifiers modifiers
  let ⟨name, declName, levelNames⟩ ← Command.liftTermElabM <| Term.expandDeclId (← getCurrNamespace) (← Command.getLevelNames) id modifiers
  let (binders, typeStx) := expandDeclSig sig
  let view ← Command.liftTermElabM <| Term.withLevelNames levelNames <| Term.withAutoBoundImplicit <| Term.elabBinders binders.getArgs fun params => do
    let levelNames ← Term.getLevelNames
    let type ← Term.elabType typeStx
    let ctorName ←
      if let some ctor := ctor then
        let `(Command.structCtor| $ctorModifiers:declModifiers $ctorId ::) := ctor
          | unreachable!
        pure (declName ++ ctorId.getId)
      else
        pure (declName.str "mk")
    let `(coinductiveFields| $[$fieldModifiers:declModifiers $fieldIds $fieldSigs]*) := fields
      | unreachable!
    let fields ← withAuxDecl name type declName fun aux => (fieldIds.zip fieldSigs).mapM fun (fieldId, fieldSig) =>
      let (binders, typeStx) := expandDeclSig fieldSig
      Term.elabBinders binders.getArgs fun args => do
      let type ← Term.elabType typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      return {
        name := declName ++ fieldId.getId
        type := ← instantiateMVars <| ← eraseRecAppSyntaxExpr <| (← mkForallFVars args type).abstract (params.push aux)
      }
    return {
      name := declName
      levelParams := levelNames
      type := ← mkForallFVars params type
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
/-
#eval CoinductiveType.elab {
  name := `Colist
  levelParams := `u
  type := .forallE `α (.sort (.succ (.param `u))) (.sort (.succ (.param `u))) .default
  numParams := 1
  ctorName := `Colist.mk
  fields := #[{
    name := `Colist.head
    type := .forallE `self (.bvar 0) (.app (.const ``Option [.param `u]) (.bvar 2)) .default
  }, {
    name := `Colist.tail
    type := .forallE `self (.bvar 0) (.forallE `h (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []) (.app (.app (.const ``Option.isSome [.param `u]) (.bvar 2)) )) (.const ``true []))) (.bvar 2) .default) .default
  }]
}
-/

set_option linter.unusedVariables false

coinductive Vec (α : Type u) : (n : Nat) → Type u where
  hd {n} (xs : Vec (n + 1)) : α
  tl {n} (xs : Vec (n + 1)) : Vec n

noncomputable
abbrev Vec.nil {α : Type u} : Vec α .zero :=
  .mk .zero nofun nofun

noncomputable
abbrev Vec.cons {α : Type u} {n} (hd : α) (tl : Vec α n) : Vec α n.succ :=
  .mk n.succ (fun _ => hd) fun h => Nat.succ.inj h ▸ tl

coinductive Collection.{u} (α : Type u) : (n : Nat) → Type u where
  push {n} (self : Collection n) (x : α) : Collection (n + 1)
  peek {n} (self : Collection (n + 1)) : α
  pop {n} (self : Collection (n + 1)) : Collection n

coinductive Stack.{u} (α : Nat → Sort u) : Nat → Sort (max 1 u) where
  push {n} (xs : Stack n) (x : α n) : Stack (n + 1)
  peek {n} (xs : Stack (n + 1)) : α n
  pop {n} (xs : Stack (n + 1)) : Stack n

#eval CoinductiveType.elab {
  name := `IndexTest
  levelParams := []
  type := .app (.const ``Id [.succ .zero]) (.forallE `n (.const ``Nat []) (.app (.const ``Id [.succ .zero]) (.forallE `m (.const ``Nat []) (.app (.const ``Id [.succ .zero]) (.sort (.succ .zero))) .default)) .default)
  numParams := 0
  ctorName := `IndexTest.mk
  fields := #[{
    name := `IndexTest.get
    type := .forallE `m (.const ``Nat []) (.forallE `n (.const ``Nat []) (.forallE `self (.app (.app (.bvar 2) (.app (.const ``Nat.succ []) (.bvar 0))) (.bvar 1)) (.forallE `k (.const ``Nat []) (.app (.app (.bvar 4) (.bvar 2)) (.app (.const ``Nat.succ []) (.bvar 3))) .default) .default) .default) .default
  }]
}

def NatUnOp := Nat → Nat

#eval CoinductiveType.elab {
  name := `SimpleTest
  levelParams := []
  type := .forallE `n (.const ``Nat []) (.sort (.succ .zero)) .default
  numParams := 0
  ctorName := `SimpleTest.mk
  fields := #[{
    name := `SimpleTest.get
    type := .forallE `n (.const ``Nat []) (.forallE `self (.app (.bvar 1) (.bvar 0)) (.const ``NatUnOp []) .default) .default
  }]
}

coinductive LazyProd.{u, v} (α : Type u) (β : Type v) : Type (max u v) where
  fst (self : LazyProd) : α
  snd (self : LazyProd) : β

coinductive DependentTest : (n : Nat) → Type where
  out n m (self : DependentTest (.add n m)) k : Fin (n.add k)
  inner n m (self : DependentTest (.add n m)) k : DependentTest (n.add k)

#eval CoinductiveType.elab {
  name := `UnivTest
  levelParams := []
  type := .forallE `α (.sort 3) (.sort 1) .default
  numParams := 0
  ctorName := `UnivTest.mk
  fields := #[{
    name := `UnivTest.get
    type := .forallE `self (.app (.bvar 0) (.sort 2)) (.const ``Unit []) .default
  }]
}

#eval CoinductiveType.elab {
  name := `UnivTest'
  levelParams := []
  type := .forallE `α (.sort 1) (.sort 3) .default
  numParams := 0
  ctorName := `UnivTest'.mk
  fields := #[]
}

#eval CoinductiveType.elab {
  name := `UnivTest2
  levelParams := [`u]
  type := .forallE `α (.sort (.param `u)) (.forallE `x (.bvar 0) (.sort 1) .default) .default
  numParams := 1
  ctorName := `UnivTest2.mk
  fields := #[{
    name := `UnivTest2.get
    type := .forallE `x (.bvar 1) (.forallE `self (.app (.bvar 1) (.bvar 0)) (.const ``True []) .default) .default
  }]
}
