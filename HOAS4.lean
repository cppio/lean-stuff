import Mathlib.Data.Fin.Tuple.Basic
import Rec

variable {motive : ∀ n, Fin n → Sort u} (zero : ∀ {n}, motive (.succ n) 0) (succ : ∀ {n} i, motive n i → motive n.succ i.succ) in
def Fin.recL : ∀ {n} i, motive n i
  | .succ _, ⟨.zero, _⟩ => zero
  | .succ _, ⟨.succ i, h⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ (recL _)

variable {motive : ∀ n, Fin n → Sort u} (castSucc : ∀ {n} i, motive n i → motive n.succ (.castSucc i)) (last : ∀ {n}, motive (.succ n) (.last _)) in
def Fin.recR : ∀ {n} i, motive n i
  | .succ _, i =>
    if h : i = _
    then h ▸ last
    else castSucc ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.2) (h <| Fin.eq_of_val_eq ·)⟩ (recR _)

inductive Ty
  | unit : Ty
  | ar : Ty → Ty → Ty

namespace Level

inductive Exp : ∀ {n}, (Γ : Fin n → Ty) → (t : Ty) → Type
  | var (l : Fin n) : Exp Γ (Γ l)
  | triv : Exp Γ .unit
  | lam (e : Exp (Fin.lastCases t₁ Γ) t₂) : Exp Γ (.ar t₁ t₂)
  | app (e₁ : Exp Γ (.ar t₁ t₂)) (e₂ : Exp Γ t₁) : Exp Γ t₂

namespace Exp

def lift' : (e : Exp Γ t) → Exp (Fin.append Γ' Γ) t
  | var l => have := var (Γ := Fin.append Γ' Γ) (Fin.natAdd _ l); by simp at this; exact this
  | triv => triv
  | lam e => by
    rename_i n _ _ _
    refine lam <| cast (congrArg (Exp · _) <| funext <| Fin.addCases (n := n + 1) ?_ ?_) (e.lift' (Γ' := Γ')) <;> intro i <;> simp
    . apply Eq.symm
      apply Eq.trans
      apply Fin.lastCases_castSucc (i := Fin.castAdd n i)
      simp
    . cases i using Fin.lastCases <;> simp
      show _ = Fin.lastCases _ _ (Fin.castSucc <| Fin.natAdd _ _)
      simp
  | app e₁ e₂ => app e₁.lift' e₂.lift'

def lift (e : Exp Fin.elim0 t) : Exp Γ t :=
  have : Exp (Fin.append Γ Fin.elim0') t := e.lift'; by simp at this; exact this

def subst (e : Exp Γ t) (e' : Exp Fin.elim0 (Γ 0)) : Exp (Fin.tail Γ) t :=
  match e with
  | var l => l.cases e'.lift var
  | triv => triv
  | lam e => by
    refine lam <| cast (congrArg (Exp · _) <| funext λ i => ?_) <| e.subst e'
    cases i using Fin.lastCases <;> simp [Fin.tail]
    apply Fin.lastCases_castSucc (i := Fin.succ _)
  | app e₁ e₂ => app (e₁.subst e') (e₂.subst e')

def substAll {k} (e : Exp (k + n)) (es : Fin k → Exp) : Exp n :=
  match k with
  | 0 => n.zero_add ▸ e
  | k + 1 => substAll (k.add_right_comm 1 n ▸ e) (Fin.init es) |>.subst (es (.last _))

theorem cast_var (l : Fin n) (h : n = n') : h ▸ var l = var (Fin.cast h l) := by cases h; rfl

theorem cast_lam (e : Exp (.succ n)) (h : n = n') : h ▸ lam e = lam (congrArg Nat.succ h ▸ e) := by cases h; rfl

theorem cast_app (e₁ e₂ : Exp n) (h : n = n') : h ▸ app e₁ e₂ = app (h ▸ e₁) (h ▸ e₂) := by cases h; rfl

theorem lift_zero : ∀ e : Exp, e.lift = e := by
  suffices ∀ {n} (e : Exp n), e.lift' = (n.zero_add.symm ▸ e : Exp (0 + n)) from this
  intro n e
  induction e with simp [lift', cast_var, cast_lam, cast_app, *]
  | var => simp [Fin.natAdd]; rfl

theorem subst_lift : ∀ {n} (e e' : Exp), e.lift.subst e' = e.lift (n := n) := by
  suffices ∀ {n k} (e : Exp n) e', (k.succ_add n ▸ e.lift').subst e' = e.lift' (k := k) from λ {n} => this
  intro n k e e'
  induction e with simp [lift', cast_var, cast_lam, cast_app, subst, *]
  | var => simp [Fin.natAdd, Nat.succ_add]

theorem substAll_var' (l : Fin n) {k} es : substAll (var <| Fin.natAdd k l) es = var l := by
  induction k generalizing n with simp [substAll, cast_var]
  | succ _ ih =>
    simp [Fin.cast, Fin.castLe, Fin.castLt, Nat.succ_add]
    specialize ih l.succ (Fin.init es)
    simp [Fin.natAdd, Nat.add_succ] at ih
    rw [ih]
    rfl

theorem substAll_var {k} (l : Fin k) es : substAll (var <| Fin.castAdd n l) es = (es l).lift := by
  induction l using Fin.recR generalizing n with simp [substAll, cast_var]
  | castSucc l ih =>
    specialize @ih n.succ (Fin.init es)
    dsimp [Fin.cast, Fin.castAdd, Fin.castLe, Fin.castLt] at ih ⊢
    rw [ih]
    apply subst_lift (es _)
  | last =>
    dsimp [Fin.cast, Fin.castLe, Fin.castLt]
    have := substAll_var' (0 : Fin n.succ) (Fin.init es)
    dsimp [Fin.natAdd] at this
    rw [this]
    rfl

theorem substAll_lam {k} (e : Exp (.succ (k + n))) es : substAll (lam e) es = lam (substAll e es) := by
  induction k generalizing n with simp [substAll, cast_lam]
  | succ k ih => rw [ih]; simp [subst]

theorem substAll_app {k} (e₁ e₂ : Exp (k + n)) es : substAll (app e₁ e₂) es = app (substAll e₁ es) (substAll e₂ es) := by
  induction k generalizing n with simp [substAll, cast_app]
  | succ k ih => rw [ih]; simp [subst]

def rec' {motive : Exp → Sort u} (lam : ∀ e, (∀ e', motive e' → motive (e.subst e')) → motive (lam e)) (app : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (app e₁ e₂)) : ∀ e, motive e :=
  rec' Fin.elim0 finZeroElim
where
  rec' {n} (es : Fin n → Exp) (hes : ∀ l, motive (es l)) : (e : Exp n) → motive (e.substAll (n := .zero) es)
  | var l => substAll_var .. ▸ lift_zero _ ▸ hes l
  | .lam e => substAll_lam .. ▸ lam _ λ e' he' =>
    have := rec' (Fin.lastCases e' es) (Fin.lastCases (by simp; exact he') (λ i => by simp; exact hes i)) e
    by simp [substAll] at this; (conv at «this» => enter [1, 2]; apply Fin.lastCases_last); dsimp [Fin.init] at this; (conv at «this» => enter [1, 1, 2]; apply funext <| Fin.lastCases_castSucc _ _); exact this
  | .app e₁ e₂ => substAll_app .. ▸ app _ _ (rec' es hes e₁) (rec' es hes e₂)

end Exp

end Level
