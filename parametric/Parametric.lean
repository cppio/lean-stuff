import Lean

section

open Lean Lean.Meta

private def modifyLocalDecl [Monad M] (lctx : LocalContext) (e : Expr) (f : LocalDecl → M LocalDecl) : M LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match lctx.findFVar? e with
    | none      => return lctx
    | some decl => do
      let decl ← f decl
      return { fvarIdToDecl := map.insert decl.fvarId decl
               decls        := decls.set decl.index decl }

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
          mkLambdaFVars xs (← visit b)
      | .forallE ..    => forallTelescope e fun xs b => do
        let mut lctx ← getLCtx
        for x in xs do
          lctx ← modifyLocalDecl lctx x λ e => return e.setType (← visit e.type)
        withLCtx lctx (← getLocalInstances) do
          mkForallFVars xs (← visit b)
      | .proj n i s .. => return mkProj n i (← visit s)
      | _                  => return e
  withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) <|
    withTransparency (mode := .all) <|
      visit e |>.run

open Elab.Command Elab.Term

elab tk:"#reduce*" term:term : command =>
  withoutModifyingEnv <| runTermElabM fun _ => withDeclName `_reduceStar do
    let e ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let e ← levelMVarToParam (← instantiateMVars e)
    logInfoAt tk (← reduceStar e)

end

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

def Fin2.elim' {α : Sort u} : Fin2 .zero → α :=
  @rec (λ n _ => n.rec α λ _ _ => PUnit) PUnit.unit (λ _ _ => PUnit.unit) _

def Fin2.elim {α : Fin2 .zero → Sort u} : ∀ i, α i :=
  @rec (@Nat.rec _ α λ _ _ _ => PUnit) PUnit.unit (λ _ _ => PUnit.unit) _

def Fin2.cases' {α : Sort u} (zero : α) (succ : Fin2 n → α) (i : Fin2 n.succ) : α :=
  @rec (λ n _ => n.rec PEmpty λ n _ => (Fin2 n → α) → α) (λ _ => zero) (λ i _ succ => succ i) _ i succ

def Fin2.cases {α : Fin2 n.succ → Sort u} (zero : α zero) (succ : (i : Fin2 n) → α (succ i)) (i) : α i :=
  @rec (@Nat.rec _ (λ _ => PEmpty) λ n _ i => {α : _ → Sort u} → α .zero → (∀ i, α (.succ i)) → α i) (λ zero _ => zero) (λ i _ _ _ succ => succ i) _ i α zero succ

def Fin2.cases₁' {α : Sort u} (zero : α) : Fin2 n → α :=
  λ _ => zero

def Fin2.cases₂' {α : Sort u} (zero : α) (succ : α) : Fin2 n → α :=
  @rec (λ _ _ => α) zero (λ _ _ => succ) _

def Fin2.cases₁ {α : Fin2 (.succ .zero) → Sort u} (zero : α zero) : ∀ i, α i :=
  cases zero elim

def Fin2.cases₂ {α : Fin2 (.succ (.succ .zero)) → Sort u} (zero : α zero) (succ : α (succ .zero)) : ∀ i, α i :=
  cases zero (cases succ elim)

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
