import Lean

open Lean Meta

private def modifyLocalDecl [Monad M] (lctx : LocalContext) (e : Expr) (f : LocalDecl → M LocalDecl) : M LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match lctx.findFVar? e with
    | none      => return lctx
    | some decl => do
      let decl ← f decl
      return { fvarIdToDecl := map.insert decl.fvarId decl
               decls        := decls.set decl.index decl }

partial def reduceStar (e : Expr) : MetaM Expr :=
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

syntax "replace " ident (" : " term)? " := " term : tactic

macro_rules
  | `(tactic| replace $i $[: $t]? := $v) =>
    `(tactic| have $[: $t]? := $v; clear $i; rename _ => $i)

syntax "split " "with " binderIdent : tactic

macro_rules
  | `(tactic| split with $i) =>
    `(tactic| split <;> rename_i $i)
