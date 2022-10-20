import Lean

structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

infix:25 " ≃ " => Equiv

theorem Sigma.mk.inj₁ (h : mk a b = mk a' b') : a = a' :=
  .rec (motive := λ s _ => a = s.1) rfl h

theorem Sigma.mk.inj₂ (h : mk a b = mk a' b') : inj₁ h ▸ b = b' :=
  .rec (motive := λ s h => inj₁ h ▸ b = s.2) rfl h

instance Sigma.instDecidableEq [I : DecidableEq α] [J : {a : α} → DecidableEq (β a)] : DecidableEq (Sigma β)
  | ⟨a, b⟩, ⟨a', b'⟩ =>
    match I a a' with
    | .isFalse ha => .isFalse (ha ∘ mk.inj₁)
    | .isTrue ha =>
      match J (ha ▸ b) b' with
      | .isFalse hb => .isFalse (hb ∘ mk.inj₂)
      | .isTrue hb => .isTrue (by cases ha; exact hb ▸ rfl)

theorem congrArg₂ (f : α → β → γ) : a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ :=
  congr ∘ congrArg f

inductive Fin2 : Nat → Type
  | zero : Fin2 (.succ n)
  | succ : Fin2 n → Fin2 n.succ
  deriving DecidableEq

private def Fin2.rec' {motive : ∀ n, Fin2 n → Sort u} (zero : ∀ {n}, motive (.succ n) zero) (succ : ∀ {n} i, motive n i → motive n.succ i.succ) {n} : ∀ i, motive n i
  | .zero => zero
  | .succ i => succ i (rec' zero succ i)

attribute [implemented_by Fin2.rec'] Fin2.rec

def Fin2.elim {α : Fin2 .zero → Sort u} : (i : Fin2 .zero) → α i :=
  @rec (@Nat.rec _ α λ _ _ _ => PUnit) PUnit.unit (λ _ _ => PUnit.unit) .zero

def Fin2.cases {α : Fin2 n.succ → Sort u} (zero : α zero) (succ : (i : Fin2 n) → α (succ i)) (i : Fin2 n.succ) : α i :=
  @rec (@Nat.rec _ (λ _ => PEmpty) λ n _ i => (α : Fin2 n.succ → Sort u) → α .zero → (∀ i, α (.succ i)) → α i) (λ _ zero _ => zero) (λ i _ _ _ succ => succ i) n.succ i α zero succ

def Fin2.castSucc : Fin2 n → Fin2 n.succ
  | zero => zero
  | succ i => succ i.castSucc

def Fin2.toNat : Fin2 n → Nat
  | zero => .zero
  | succ i => .succ i.toNat

def Fin2.ofNat : ∀ {n m}, n < m → Fin2 m
  | .zero, .succ _, _ => zero
  | .succ _, .succ _, h => succ (ofNat (Nat.lt_of_succ_lt_succ h))

instance : Coe (Fin2 n) Nat where
  coe := Fin2.toNat

instance : Repr (Fin2 n) where
  reprPrec i := reprPrec i.toNat

attribute [class] Nat.le
attribute [instance] Nat.le.refl
instance : ∀ {n m}, [Nat.le n m] → Nat.le n m.succ := @Nat.le.step

instance [I : Nat.le n.succ m] : OfNat (Fin2 m) n where
  ofNat := .ofNat I

theorem forallext {α : Sort u} {β β' : α → Sort v} (h : ∀ x, β x = β' x) : (∀ x, β x) = ∀ x, β' x :=
  (funext h : β = β') ▸ rfl

theorem subst_subst {α : Sort u} {β : α → Sort v} {x x' : α} (y : β x) (h : x = x') : h.symm ▸ (h ▸ y) = y := by
  cases h
  rfl

syntax (name := applyAssumption) "apply_assumption" : tactic

@[tactic applyAssumption]
def evalApplyAssumption : Lean.Elab.Tactic.Tactic := λ _ => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  mvarId.withContext do
    for decl in ← Lean.getLCtx do
      if decl.isAuxDecl then continue
      try
        Lean.Elab.Tactic.replaceMainGoal (← mvarId.apply decl.toExpr)
        return ()
      catch _ => pure ()
    Lean.Meta.throwTacticEx `apply_assumption mvarId ""

syntax (name := destruct) "destruct" term : tactic

@[tactic destruct]
def evalDestruct : Lean.Elab.Tactic.Tactic
  | `(tactic| destruct $e) => do
    let mvarId ← Lean.Elab.Tactic.getMainGoal
    mvarId.withContext do
      let t ← Lean.Elab.Tactic.elabTerm e none
      let (newMVars, _, _) ← Lean.Meta.forallMetaTelescope (← Lean.Meta.inferType t)
      let t := Lean.mkAppN t newMVars
      Lean.Elab.Tactic.replaceMainGoal (← mvarId.casesRec (Lean.Meta.isDefEq t ∘ Lean.LocalDecl.type))
  | _ => Lean.Elab.throwUnsupportedSyntax

def modifyLocalDecl [Monad M] (lctx : Lean.LocalContext) (e : Lean.Expr) (f : Lean.LocalDecl → M Lean.LocalDecl) : M Lean.LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match lctx.findFVar? e with
    | none      => return lctx
    | some decl => do
      let decl ← f decl
      return { fvarIdToDecl := map.insert decl.fvarId decl
               decls        := decls.set decl.index decl }

partial def reduceAll (e : Lean.Expr) : Lean.MetaM Lean.Expr :=
  let rec visit (e : Lean.Expr) : Lean.MonadCacheT Lean.Expr Lean.Expr Lean.MetaM Lean.Expr :=
    Lean.checkCache e fun _ => Lean.Core.withIncRecDepth do
      let e ← Lean.Meta.whnf e
      match e with
      | Lean.Expr.app .. =>
        let f     ← visit e.getAppFn
        let mut args  := e.getAppArgs
        for i in [:args.size] do
          args ← args.modifyM i visit
        return Lean.mkAppN f args
      | Lean.Expr.lam ..        => Lean.Meta.lambdaTelescope e fun xs b => do
        let mut lctx ← Lean.getLCtx
        for x in xs do
          lctx ← modifyLocalDecl lctx x λ e => return e.setType (← visit e.type)
        Lean.Meta.withLCtx lctx (← Lean.Meta.getLocalInstances) do
          Lean.Meta.mkLambdaFVars xs (← visit b)
      | Lean.Expr.forallE ..    => Lean.Meta.forallTelescope e fun xs b => do
        let mut lctx ← Lean.getLCtx
        for x in xs do
          lctx ← modifyLocalDecl lctx x λ e => return e.setType (← visit e.type)
        Lean.Meta.withLCtx lctx (← Lean.Meta.getLocalInstances) do
          Lean.Meta.mkForallFVars xs (← visit b)
      | Lean.Expr.proj n i s .. => return Lean.mkProj n i (← visit s)
      | _                  => return e
  withTheReader Lean.Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) <|
    Lean.Meta.withTransparency (mode := .all) <|
      visit e |>.run

syntax (name := reduceStar) "#reduce*" term : command

@[command_elab reduceStar]
def elabReduceStar : Lean.Elab.Command.CommandElab
  | `(#reduce*%$tk $term) => Lean.withoutModifyingEnv <| Lean.Elab.Command.runTermElabM fun _ => Lean.Elab.Term.withDeclName `_reduceAll do
    let e ← Lean.Elab.Term.elabTerm term none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.Elab.Term.levelMVarToParam (← Lean.instantiateMVars e)
    Lean.logInfoAt tk (← reduceAll e)
  | _ => Lean.Elab.throwUnsupportedSyntax
