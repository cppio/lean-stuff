import Lean

section

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

open Elab

elab tk:"#reduce*" term:term : command =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => Term.withDeclName `_reduceStar do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    logInfoAt tk (← reduceStar e)

private def nameCmp : List Name → List Name → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | n₁ :: s₁, n₂ :: s₂ =>
    match n₁.cmp n₂ with
    | .eq => nameCmp s₁ s₂
    | ord => ord

elab tk:"#print prefix" id:ident : command => do
  let cs := (← getEnv).constants.fold (λ cs name info =>
    if id.getId.isPrefixOf name then cs.push (name, info.type) else cs) #[]
  let cs := cs.qsort λ x y => nameCmp x.1.components y.1.components == .lt
  logInfoAt tk (.joinSep (cs.map λ (name, type) => name ++ " : " ++ type).toList Format.line)

elab "apply_assumption" : tactic => do
  let mvarId ← Tactic.getMainGoal
  mvarId.withContext do
    let mvarIds? ← (← getLCtx).findDeclRevM? fun decl => do
      if decl.isAuxDecl then return none
      try mvarId.apply decl.toExpr
      catch _ => return none
    match mvarIds? with
    | some mvarIds => Tactic.replaceMainGoal mvarIds
    | none => throwTacticEx `apply_assumption mvarId ""

elab "destruct" e:term : tactic => do
  let mvarId ← Tactic.getMainGoal
  mvarId.withContext do
    let e ← Tactic.elabTerm e none
    let (newMVars, _, _) ← forallMetaTelescope (← inferType e)
    let e := mkAppN e newMVars
    for decl in ← getLCtx do
      if decl.isAuxDecl then continue
      if ← isDefEq e decl.type then
        Tactic.replaceMainGoal ((← mvarId.cases decl.fvarId).map (·.mvarId)).toList
        return
    throwTacticEx `destruct mvarId ""

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

namespace Fin2

private def rec' {motive : ∀ n, Fin2 n → Sort u} (zero : ∀ {n}, motive (.succ n) zero) (succ : ∀ {n} i, motive n i → motive n.succ i.succ) {n} : ∀ i, motive n i
  | .zero => zero
  | .succ i => succ i (rec' zero succ i)

attribute [implemented_by rec'] rec

def elim' {α : Sort u} : Fin2 .zero → α :=
  @rec (λ n _ => n.rec α λ _ _ => PUnit) PUnit.unit (λ _ _ => PUnit.unit) _

def elim {α : Fin2 .zero → Sort u} : ∀ i, α i :=
  @rec (@Nat.rec _ α λ _ _ _ => PUnit) PUnit.unit (λ _ _ => PUnit.unit) _

def cases' {α : Sort u} (zero : α) (succ : Fin2 n → α) (i : Fin2 n.succ) : α :=
  @rec (λ n _ => n.rec PEmpty λ n _ => (Fin2 n → α) → α) (λ _ => zero) (λ i _ succ => succ i) _ i succ

def cases {α : Fin2 n.succ → Sort u} (zero : α zero) (succ : (i : Fin2 n) → α (succ i)) (i) : α i :=
  @rec (@Nat.rec _ (λ _ => PEmpty) λ n _ i => {α : _ → Sort u} → α .zero → (∀ i, α (.succ i)) → α i) (λ zero _ => zero) (λ i _ _ _ succ => succ i) _ i α zero succ

@[simp] theorem cases'.zero (zero succ) : @cases' n α zero succ .zero = zero := rfl
@[simp] theorem cases'.succ (zero succ i) : @cases' n α zero succ (.succ i) = succ i := rfl

@[simp] theorem cases.zero (zero succ) : @cases n α zero succ .zero = zero := rfl
@[simp] theorem cases.succ (zero succ i) : @cases n α zero succ (.succ i) = succ i := rfl

def cases₁' {α : Sort u} (zero : α) : Fin2 n → α :=
  λ _ => zero

def cases₂' {α : Sort u} (zero : α) (succ : α) : Fin2 n → α :=
  @rec (λ _ _ => α) zero (λ _ _ => succ) _

def cases₁ {α : Fin2 (.succ .zero) → Sort u} (zero : α zero) : ∀ i, α i :=
  cases zero elim

def cases₂ {α : Fin2 (.succ (.succ .zero)) → Sort u} (zero : α zero) (succ : α (succ .zero)) : ∀ i, α i :=
  cases zero (cases succ elim)

@[simp] theorem cases₁'.zero (zero i) : @cases₁' n α zero i = zero := rfl

@[simp] theorem cases₂'.zero (zero succ) : @cases₂' (.succ n) α zero succ .zero = zero := rfl
@[simp] theorem cases₂'.succ (zero succ i) : @cases₂' (.succ n) α zero succ (.succ i) = succ := rfl

@[simp] theorem cases₁.zero (zero) : @cases₁ α zero .zero = zero := rfl

@[simp] theorem cases₂.zero (zero succ) : @cases₂ α zero succ .zero = zero := rfl
@[simp] theorem cases₂.succ (zero succ) : @cases₂ α zero succ (.succ .zero) = succ := rfl

end Fin2

theorem forallext {α : Sort u} {β β' : α → Sort v} (h : ∀ x, β x = β' x) : (∀ x, β x) = ∀ x, β' x :=
  (funext h : β = β') ▸ rfl

theorem subst_subst {α : Sort u} {β : α → Sort v} {x x' : α} (y : β x) (h : x = x') : h.symm ▸ (h ▸ y) = y := by
  cases h
  rfl

syntax "para_step" : tactic

macro_rules | `(tactic| para_step) => `(tactic| split)
macro_rules | `(tactic| para_step) => `(tactic| constructor)
macro_rules | `(tactic| para_step) => `(tactic| intro)
macro_rules | `(tactic| para_step) => `(tactic| apply_assumption)

macro "parametric" : tactic => `(tactic| (repeat para_step))
