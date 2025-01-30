import Lean

syntax (name := inlineFn) "inline% " term : term

open Lean Meta Elab Term

@[term_elab inlineFn]
partial def elabInlineFn : TermElab
  | `(inline%%$tk $t), expectedType? => withRef tk do
    let e ← elabTerm t expectedType?
    let appFn := e.getAppFn
    let args := e.getAppArgs
    logInfo m!"{args}"
    let .const fn us := appFn
      | throwError "expected constant, got {appFn}"
    let .some eqn ← getUnfoldEqnFor? fn true
      | throwError "{fn} has no unfold equation"
    let eqnInfo ← getConstInfo eqn
    let (xs, _, eq) ← forallMetaTelescope <| eqnInfo.type.instantiateLevelParams eqnInfo.levelParams us
    let .app (.app (.app (.const ``Eq [_]) ty) lhs) rhs := eq
      | throwError "expected Eq, got {eq}"
    let rec visit (e : Expr) : MonadCacheT Expr Unit (StateT (Array Bool) TermElabM) Unit := checkCache e fun _ => do
      match e with
      | .forallE _ d b _ | .lam _ d b _ => visit d; visit b
      | .letE _ t v b _ => visit t; visit v; visit b
      | .mdata _ b | .proj _ _ b => visit b
      | .app .. => e.withApp fun f args => do
        if f == appFn then
          modify fun fixed => fixed.zipWith (xs.zip args) fun fixed (x, arg) => fixed && x == arg
          args.forM visit
        else
          visit f
          args.forM visit
      | _ => pure ()
    let (_, fixed) ← visit rhs |>.run.run <| mkArray xs.size true
    for (x, arg, fixed) in xs.zip <| args.zip fixed do
      if fixed then
        x.mvarId!.assign arg
    let varying := xs.zip fixed |>.filterMap fun | (_, true) => none | (e, false) => some e
    logInfo m!"{← mkLambdaFVars varying lhs} = {← mkLambdaFVars varying rhs} : {← mkForallFVars varying ty}"
    modify fun s => { s with letRecsToLift := {
      ref := tk
      fvarId := sorry
      attrs := #[]
      shortDeclName := sorry
      declName := sorry
      lctx := sorry
      localInstances := sorry
      type := sorry
      val := sorry
      mvarId := sorry
      termination := .none
    } :: s.letRecsToLift }
    return e
  | _, _ => throwUnsupportedSyntax

inductive Rose (α : Type u)
  | mk (x : α) (xs : List (Rose α))

variable {α : Type u}

def Rose.id : Rose α → Rose α
  | mk x xs => mk x <| inline% xs.map id

def Rose.sizer : Rose α → Nat
  | mk x xs => inline% xs.foldr (sizer · + ·) 1

def Rose.sizel : Rose α → Nat
  | mk x xs => inline% xs.foldl (· + sizel ·) 1

#check List.map.eq_def
#check @List.map.eq_def

#print List.map.eq_def
