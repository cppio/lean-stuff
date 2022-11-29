import Lean

open Lean

private def joinMapM [Monad m] (xs : Array α) (f : α → m MessageData) : m MessageData :=
  match xs.back? with
  | none => return .nil
  | some back => do
    xs.foldrM (λ x msg => return (← f x) ++ Format.line ++ msg) (← f back) (xs.size - 1)

private def joinMap (xs : Array α) (f : α → MessageData) : MessageData :=
  Id.run <| joinMapM xs f

private def nameCmp (n₁ : Name) (n₂ : Name) : Ordering :=
  cmp n₁.components n₂.components
where
  cmp
  | [], [] => .eq
  | [], _  => .lt
  | _,  [] => .gt
  | n₁ :: l₁, n₂ :: l₂ =>
    match n₁.cmp n₂ with
    | .eq => cmp l₁ l₂
    | ord => ord

elab tk:"#print prefix " i:ident : command => do
  let i := i.getId
  let cs := (← getEnv).constants.fold (fun cs name info =>
    if i.isPrefixOf name then cs.push info else cs) #[]
  let cs := cs.qsort (nameCmp ·.name ·.name == .lt)
  logInfoAt tk <| joinMap cs fun info => info.name ++ " : " ++ info.type

private def modifyLocalDecl [Monad m] (lctx : LocalContext) (e : Expr) (f : LocalDecl → m LocalDecl) : m LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match lctx.findFVar? e with
    | none      => return lctx
    | some decl => do
      let decl ← f decl
      return { fvarIdToDecl := map.insert decl.fvarId decl
               decls        := decls.set decl.index decl }

open Meta

private partial def reduceStar (e : Expr) : MetaM Expr :=
  let rec visit (e : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache e fun _ => withIncRecDepth do
      let e ← whnf e
      match e with
      | .app .. =>
        let f     ← visit e.getAppFn
        let mut args  := e.getAppArgs
        for i in [:args.size] do
          args ← args.modifyM i visit
        return mkAppN f args
      | .lam ..        => lambdaTelescope e fun xs b => do
        let mut lctx ← getLCtx
        for x in xs do
          lctx ← modifyLocalDecl lctx x λ e => return e.setType (← visit e.type)
        withLCtx lctx (← getLocalInstances) do
          return (← mkLambdaFVars xs (← visit b)).eta
      | .forallE ..    => forallTelescope e fun xs b => do
        let mut lctx ← getLCtx
        for x in xs do
          lctx ← modifyLocalDecl lctx x λ e => return e.setType (← visit e.type)
        withLCtx lctx (← getLocalInstances) do
          mkForallFVars xs (← visit b)
      | .proj n i s .. => return mkProj n i (← visit s)
      | _                  => return e
  withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) <|
    withTransparency .all <|
      visit e |>.run

open Elab

elab tk:"#reduce*" term:term : command =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => Term.withDeclName `_reduceStar do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    logInfoAt tk (← reduceStar e)

elab tk:"#print instances " t:term : command => Command.runTermElabM fun _ => do
  let e ← Term.elabType t
  let insts ← SynthInstance.getInstances e
  logInfoAt tk <| ← joinMapM insts λ inst => return inst ++ " : " ++ (← inferType inst)
