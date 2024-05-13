import Lean

open Lean Meta

def checkRec (iv : InductiveVal) : MetaM Unit := do
  if iv.isNested then
    throwError "nested inductives are unsupported"

  let all := iv.all.toArray

  let inducts ← all.mapM fun n => do
    let iv ← getConstInfoInduct n
    return (iv, ← iv.ctors.toArray.mapM getConstInfoCtor, ← getConstInfoRec (mkRecName n))

  let levels := iv.levelParams.map .param

  let elim_level :=
    let (iv, _, rv) := inducts[0]!
    if rv.levelParams.length > iv.levelParams.length then
      .param rv.levelParams.head!
    else
      .zero

  forallBoundedTelescope iv.type iv.numParams fun params _ => do
  let motives ← inducts.mapM fun (iv, _) => do
    forallTelescopeReducing (← instantiateForall iv.type params) fun indices _ =>
    withLocalDeclD `t (mkAppN (mkAppN (.const iv.name levels) params) indices) fun major => do
    let motive ← mkForallFVars (indices.push major) <| .sort elim_level
    return (`motive, fun _ => return motive)
  withLocalDeclsD motives fun motives => do
  let minors ← motives.zip inducts |>.concatMapM fun (motive, (_, cvs, _)) => cvs.mapM fun cv => do
    forallTelescope (← instantiateForall cv.type params) fun fields t => do
    let ihs ← fields.filterMapM fun field => do
      forallTelescopeReducing (← inferType field) fun xs t =>
        t.getAppFn.constName?.bindM fun fn => do
        all.indexOf? fn |>.mapM fun idx => do
        let ih ← mkForallFVars xs <| .app (mkAppN motives[idx]! t.getAppArgs[iv.numParams:]) (mkAppN field xs)
        return (.anonymous, fun _ => return ih)
    withLocalDeclsD ihs fun ihs => do
    let minor ← mkForallFVars (fields ++ ihs) <| .app (mkAppN motive t.getAppArgs[iv.numParams:]) (mkAppN (mkAppN (.const cv.name levels) params) fields)
    return (.anonymous, fun _ => return minor)
  withLocalDeclsD minors fun minors =>
  for (motive, iv, _, rv) in motives.zip inducts do
    forallTelescopeReducing (← instantiateForall iv.type params) fun indices _ =>
    withLocalDeclD `t (mkAppN (mkAppN (.const iv.name levels) params) indices) fun major => do
    let type ← mkForallFVars (params ++ motives ++ minors ++ indices |>.push major) <| .app (mkAppN motive indices) major

    let type ← transform type fun e => return .continue e.consumeTypeAnnotations
    let rvType ← transform rv.type fun e => return .continue e.consumeTypeAnnotations
    if !type.eqv rvType then
      logInfo m!"{iv.name}{Format.line}{type}{Format.line}{rvType}"

def checkCasesOn (iv : InductiveVal) : MetaM Unit := do
  if iv.isNested then
    throwError "nested inductives are unsupported"

  let all := iv.all.toArray

  let inducts ← all.mapM fun n => do
    let iv ← getConstInfoInduct n
    return (iv, ← iv.ctors.toArray.mapM getConstInfoCtor, ← getConstInfoRec (mkRecName n))

  let levels := iv.levelParams.map .param

  let elim_level :=
    let (iv, _, rv) := inducts[0]!
    if rv.levelParams.length > iv.levelParams.length then
      .param rv.levelParams.head!
    else
      .zero

  forallBoundedTelescope iv.type iv.numParams fun params _ => do
  for (iv, cvs, _) in inducts do
    forallTelescopeReducing (← instantiateForall iv.type params) fun indices _ =>
    withLocalDeclD `t (mkAppN (mkAppN (.const iv.name levels) params) indices) fun major => do
    withLocalDeclD `motive (← mkForallFVars (indices.push major) <| .sort elim_level) fun motive => do
    let minors ← cvs.mapM fun cv => do
      forallTelescope (← instantiateForall cv.type params) fun fields t => do
      let minor ← mkForallFVars fields <| .app (mkAppN motive t.getAppArgs[iv.numParams:]) (mkAppN (mkAppN (.const cv.name levels) params) fields)
      return (.anonymous, fun _ => return minor)
    withLocalDeclsD minors fun minors => do
    let type ← mkForallFVars (params ++ #[motive] ++ indices ++ #[major] ++ minors) <| .app (mkAppN motive indices) major

    let type ← transform type fun e => return .continue e.consumeTypeAnnotations
    let casesOnType ← transform (← getConstInfo (mkCasesOnName iv.name)).type fun e => return .continue e.consumeTypeAnnotations
    if !type.eqv casesOnType then
      logInfo m!"{iv.name}{Format.line}{type}{Format.line}{casesOnType}"

run_elab
  (← getEnv).constants.forM fun _ ci => do
    if let .inductInfo iv := ci then
      if !iv.isNested then
        checkRec iv
        checkCasesOn iv

partial def mkFreshNames (names : List Name) (count : Nat) (pre := `u) (start := 1) : List Name :=
  match count with
  | 0 => []
  | count + 1 =>
    let name := pre.appendIndexAfter start
    if names.contains name then
      mkFreshNames names (count + 1) pre (start + 1)
    else
      name :: mkFreshNames names count pre (start + 1)

def withModifyLocalDecls (xs : Array Expr) (f : LocalDecl → MetaM LocalDecl) (k : MetaM α) : MetaM α := do
  let ctx ← read
  let ctx := { ctx with lctx := ← xs.foldlM (init := ctx.lctx) fun lctx x => do
    let ldecl ← f (lctx.get! x.fvarId!)
    return lctx.modifyLocalDecl x.fvarId! fun _ => ldecl
  }
  withReader (fun _ => ctx) k

def mkRecAux (rv : RecursorVal) : MetaM Unit := do
  if rv.numMotives == 1 then
    return

  forallTelescope rv.type fun args ty => do
  let params := args[:rv.numParams]
  let motives := args[rv.numParams:rv.numParams+rv.numMotives]
  let minors := args[rv.numParams+rv.numMotives:rv.numParams+rv.numMotives+rv.numMinors]
  let indicesMajor := args[rv.numParams+rv.numMotives+rv.numMinors:]

  let .sort u@(.param _) := (← motives[0]!.fvarId!.getType).getForallBody
    | return

  let levels := mkFreshNames rv.levelParams.tail! rv.numMotives
  let levelsMap : HashMap FVarId Name := .ofList <| motives.toArray.map (·.fvarId!) |>.toList |>.zip levels

  withModifyLocalDecls motives (fun ldecl => return ldecl.setType <| ldecl.type.replaceLevel (if · == u then some (.param <| levelsMap.find! ldecl.fvarId) else none)) do

  let maxLevel := .mkNaryMax (levels.map .param)
  let mut e := mkAppN (.const rv.name (.succ maxLevel :: rv.levelParams.tail!.map .param)) params

  for motive in motives do
    let level := levelsMap.find! motive.fvarId!
    e := .app e <| ← forallTelescope (← motive.fvarId!.getType) fun args _ =>
      mkLambdaFVars args <| .app (.const ``ULift [maxLevel, .param level]) (.app (.const ``PLift [.param level]) (mkAppN motive args))

  for minor in minors do
    e := .app e <| ← forallTelescope (← minor.fvarId!.getType) fun args ty => do
      let minor := mkAppN minor <| ← args.mapM fun arg => do
        forallTelescopeReducing (← arg.fvarId!.getType) fun fields type => do
        let fn := type.getAppFn
        if fn.isFVar then
          if let some level := levelsMap.find? fn.fvarId! then
            let arg := mkAppN arg fields
            let arg := .app (.app (.const ``ULift.down [maxLevel, .param level]) (.app (.const ``PLift [.param level]) type)) arg
            let arg := .app (.app (.const ``PLift.down [.param level]) type) arg
            return ← mkLambdaFVars fields arg
        return arg
      withModifyLocalDecls args (fun ldecl => do
        forallTelescopeReducing ldecl.type fun fields type => do
        let fn := type.getAppFn
        if fn.isFVar then
          if let some level := levelsMap.find? fn.fvarId! then
            return ldecl.setType <| ← mkForallFVars fields <| .app (.const ``ULift [maxLevel, .param level]) (.app (.const ``PLift [.param level]) type)
        return ldecl
      ) do
      let level := .param <| levelsMap.find! ty.getAppFn.fvarId!
      let minor := .app (.app (.const ``PLift.up [level]) ty) minor
      let minor := .app (.app (.const ``ULift.up [maxLevel, level]) (.app (.const ``PLift [level]) ty)) minor
      mkLambdaFVars args minor

  e := mkAppN e indicesMajor

  let level := .param <| levelsMap.find! ty.getAppFn.fvarId!
  e := .app (.app (.const ``ULift.down [maxLevel, level]) (.app (.const ``PLift [level]) ty)) e
  e := .app (.app (.const ``PLift.down [level]) ty) e

  let args := params ++ motives ++ minors ++ indicesMajor

  addDecl <| .defnDecl {
    name := rv.name.appendAfter "Aux"
    levelParams := levels ++ rv.levelParams.tail!
    type := ← mkForallFVars args ty
    value := ← mkLambdaFVars args e
    hints := .opaque
    safety := if rv.isUnsafe then .unsafe else .safe
  }

run_elab
  let env ← getEnv
  env.constants.forM fun _ ci => do
    let .recInfo rv := ci
      | return
    mkRecAux rv
