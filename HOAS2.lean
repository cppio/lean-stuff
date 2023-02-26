import Common
import Rec

theorem funext' {α : Sort u} {β γ : α → Sort v} {f : ∀ x, β x} {g : ∀ x, γ x} (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  cases (funext (type_eq_of_heq <| h ·) : β = γ)
  exact heq_of_eq <| funext (eq_of_heq <| h ·)

def forall_sigma {α : Type u} {β : α → Type v} {γ : ∀ x, β x → Type w} (f : ∀ x, (y : β x) × γ x y) : (g : ∀ x, β x) × ∀ x, γ x (g x) :=
  ⟨(f · |>.1), (f · |>.2)⟩

def forall_psigma {α : Sort u} {β : α → Sort v} {γ : ∀ x, β x → Sort w} (f : ∀ x, (y : β x) ×' γ x y) : (g : ∀ x, β x) ×' ∀ x, γ x (g x) :=
  ⟨(f · |>.1), (f · |>.2)⟩

/-
def forall_subtype {α : Sort u} {β : α → Sort v} {γ : ∀ x, β x → Prop} (f : ∀ x, { y // γ x y }) : { g : ∀ x, β x // ∀ x, γ x (g x) } :=
  ⟨(f · |>.1), (f · |>.2)⟩
-/

inductive Ty
  | unit : Ty
  | ar : Ty → Ty → Ty

variable (v : Ty → Type) in
inductive Tm : Ty → Type
  | var : v t → Tm t
  | triv : Tm .unit
  | abs : (v t₁ → Tm t₂) → Tm (.ar t₁ t₂)
  | app : Tm (.ar t₁ t₂) → Tm t₁ → Tm t₂

#compile Tm

def Tm.liftRel (r : ∀ ⦃t⦄, v t → v' t → Prop) {t} : Tm v t → Tm v' t → Prop
  | var x, var x' => r x x'
  | triv, triv => True
  | abs e, abs e' => ∀ x x', r x x' → liftRel r (e x) (e' x')
  | app (t₁ := t₁) e₁ e₂, app (t₁ := t₁') e₁' e₂' => ∃ h : t₁ = t₁', liftRel r (h ▸ e₁) e₁' ∧ liftRel r (h ▸ e₂) e₂'
  | _, _ => False

def Exp t := { e : ∀ v, Tm v t // ∀ {v v'} r, Tm.liftRel r (e v) (e v') }
def Exp₁ t₁ t₂ := { e : ∀ v, v t₁ → Tm v t₂ // ∀ {v v'} r x x', r x x' → Tm.liftRel r (e v x) (e v' x') }

protected def Exp.toString (e : Exp t) : String :=
  toString (e.1 _) |>.run' .zero
where
  toString {t} : Tm (λ _ => Var) t → StateM Var String
    | .var n => return n.toString
    | .triv => return "⟨⟩"
    | .abs e => do let x ← getModify .succ; return s!"(λ{x}. {← toString (e x)})"
    | .app e₁ e₂ => return s!"({← toString e₁} {← toString e₂})"

instance : ToString (Exp t) := ⟨Exp.toString⟩

def Exp.triv : Exp .unit :=
  ⟨λ _ => .triv, λ _ => ⟨⟩⟩

def Exp.abs (e : Exp₁ t₁ t₂) : Exp (.ar t₁ t₂) :=
  ⟨λ _ => .abs (e.1 _), e.2⟩

def Exp.app (e₁ : Exp (.ar t₁ t₂)) (e₂ : Exp t₁) : Exp t₂ :=
  ⟨λ _ => .app (e₁.1 _) (e₂.1 _), λ r => ⟨rfl, e₁.2 r, e₂.2 r⟩⟩

@[simp]
theorem Exp.abs.injIff : @abs t₁ t₂ e = @abs t₁ t₂ e' ↔ e = e' :=
  ⟨λ h => Subtype.eq <| funext (Tm.abs.inj <| congrFun (congrArg (·.1) h) ·), λ | rfl => rfl⟩

@[simp]
theorem Exp.app.injIff : @app t₁ t₂ e₁ e₂ = @app t₁' t₂ e₁' e₂' ↔ t₁ = t₁' ∧ HEq e₁ e₁' ∧ HEq e₂ e₂' :=
  ⟨λ h => have := (Tm.app.inj <| congrFun (congrArg (·.1) h) ·); by
    cases this (λ _ => Empty) |>.1
    exact ⟨rfl, heq_of_eq <| Subtype.eq <| eq_of_heq <| funext' (this · |>.2.1), heq_of_eq <| Subtype.eq <| eq_of_heq <| funext' (this · |>.2.2)⟩
  , λ ⟨rfl, .refl _, .refl _⟩ => rfl⟩

@[simp] theorem Exp.triv_ne_app : triv ≠ app e₁' e₂' := λ h => nomatch congrFun (congrArg (·.1) h) λ _ => Empty
@[simp] theorem Exp.abs_ne_app : abs e ≠ app e₁' e₂' := λ h => nomatch congrFun (congrArg (·.1) h) λ _ => Empty
@[simp] theorem Exp.app_ne_triv : app e₁ e₂ ≠ triv := λ h => nomatch congrFun (congrArg (·.1) h) λ _ => Empty
@[simp] theorem Exp.app_ne_abs : app e₁ e₂ ≠ abs e' := λ h => nomatch congrFun (congrArg (·.1) h) λ _ => Empty

@[simp]
theorem Exp.ne_var {e : Exp t} {v x} : e.1 v ≠ .var x := by
  intro h
  have := h ▸ e.2 λ t (_ _ : v t) => False
  exact this

theorem Exp.eq_triv {e : Exp .unit} {v} : e.1 v = .triv → e = .triv := by
  intro h
  apply Subtype.eq
  funext v'
  have := h ▸ e.2 λ t (_ : v t) (_ : v' t) => False
  generalize e.1 v' = e' at this
  cases e' <;> dsimp! at this
  rfl

def Exp.eq_abs {e : Exp (.ar t₁ t₂)} {v e'} : e.1 v = .abs e' → (e' : _) ×' e = .abs e' := by
  intro h
  have h₁ : ∀ v', (e' : _) ×' e.1 v' = .abs e' := by
    intro v'
    have := h ▸ e.2 λ t (_ : v t) (_ : v' t) => False
    generalize e.1 v' = e' at this
    cases e' <;> dsimp! at this
    exact ⟨_, rfl⟩
  clear v e' h
  have ⟨e', h₂⟩ := forall_psigma h₁
  have h : e.1 = _ := funext h₂
  clear h₁ h₂
  refine ⟨⟨e', λ r => ?_⟩, Subtype.eq h⟩
  have := h ▸ e.2 r
  exact this

def Exp.eq_app {t₂} {e : Exp t₂} {v e₁} {e₂ : Tm v t₁} : e.1 v = .app e₁ e₂ → (e₁ : _) × (e₂ : Exp t₁) ×' e = .app e₁ e₂ := by
  intro h
  have h₁ : ∀ v', (e₁ : _) × (e₂ : Tm v' t₁) ×' e.1 v' = .app e₁ e₂ := by
    intro v'
    have := h ▸ e.2 λ t (_ : v t) (_ : v' t) => False
    generalize e.1 v' = e' at this
    cases e' <;> dsimp! at this
    cases this.1
    exact ⟨_, _, rfl⟩
  clear v e₁ e₂ h
  have ⟨e₁, h₂⟩ := forall_sigma h₁
  have ⟨e₂, h₃⟩ := forall_psigma h₂
  have h : e.1 = _ := funext h₃
  clear h₁ h₂ h₃
  refine ⟨⟨e₁, λ r => ?_⟩, ⟨e₂, λ r => ?_⟩, Subtype.eq h⟩
  all_goals
    have ⟨_, _, _⟩ := h ▸ e.2 r
    assumption

def Exp.rec {motive : ∀ t, Exp t → Sort u}
  (triv : motive .unit .triv)
  (abs : ∀ {t₁ t₂} e', motive (.ar t₁ t₂) (.abs e'))
  (app : ∀ {t₁ t₂} e₁ e₂, motive _ e₁ → motive t₁ e₂ → motive t₂ (.app e₁ e₂))
{t} e : motive t e := by
  generalize h : e.1 (λ _ => Empty) = e'
  induction e' with
  | var x => cases Exp.ne_var h
  | triv => cases Exp.eq_triv h; exact triv
  | abs => have ⟨e', h⟩ := Exp.eq_abs h; cases h; exact abs e'
  | app A B ih₁ ih₂ => have ⟨e₁, e₂, h⟩ := Exp.eq_app h; cases h; simp [Exp.app] at h; exact app e₁ e₂ (ih₁ e₁ h.1) (ih₂ e₂ h.2)

def Exp.cases {motive : ∀ t, Exp t → Sort u}
  (triv : motive .unit .triv)
  (abs : ∀ {t₁ t₂} e', motive (.ar t₁ t₂) (.abs e'))
  (app : ∀ {t₁ t₂} e₁ (e₂ : Exp t₁), motive t₂ (.app e₁ e₂))
: ∀ {t} e, motive t e :=
  @rec motive triv abs λ e₁ e₂ _ _ => app e₁ e₂

def Tm.flatten : Tm (Tm v) t → Tm v t
  | .var e => e
  | .triv => .triv
  | .abs e => .abs (.var · |> e |>.flatten)
  | .app e₁ e₂ => .app e₁.flatten e₂.flatten

theorem Tm.liftRel_flatten {t} {e : Tm (Tm v) t} {e' : Tm (Tm v') t} (h : liftRel (λ _ => liftRel r) e e') : liftRel r (flatten e) (flatten e') := by
  induction e <;> cases e' <;> try contradiction
  next => exact h
  next => exact ⟨⟩
  next ih _ => exact λ x x' hx => ih _ <| h _ _ hx
  next ih₁ ih₂ _ _ _ => cases h.1; exact ⟨rfl, ih₁ h.2.1, ih₂ h.2.2⟩

def Exp' (n : Ty → Nat) t := { e : ∀ v, (∀ t', Fin (n t') → v t') → Tm v t // ∀ {v v'} r xs xs', (∀ t' i, r (xs t' i) (xs' t' i)) → Tm.liftRel r (e v xs) (e v' xs') }

def Exp'.triv : Exp' n .unit :=
  ⟨λ _ _ => .triv, λ _ _ _ _ => ⟨⟩⟩

def Exp'.app (e₁ : Exp' n (.ar t₁ t₂)) (e₂ : Exp' n t₁) : Exp' n t₂ :=
  ⟨λ _ xs => .app (e₁.1 _ xs) (e₂.1 _ xs), λ r xs xs' hxs => ⟨rfl, e₁.2 r xs xs' hxs, e₂.2 r xs xs' hxs⟩⟩

theorem Exp'.eq_triv {e : Exp' n .unit} {v es} : e.1 v es = .triv → e = .triv := by
  intro h
  apply Subtype.eq
  funext v' es'
  have := h ▸ e.2 (λ t (_ : v t) (_ : v' t) => True) es es' λ _ _ => ⟨⟩
  generalize e.1 v' es' = e' at this
  cases e' <;> dsimp! at this
  rfl

def forall₂_sigma {α : Type u} {α₁ : α → Type u₁} {β : ∀ x, α₁ x → Type v} {γ : ∀ x y, β x y → Type w} (f : ∀ x y, (z : β x y) × γ x y z) : (g : ∀ x y, β x y) × ∀ x y, γ x y (g x y) :=
  ⟨(f · · |>.1), (f · · |>.2)⟩

def forall₂_psigma {α : Sort u} {α₁ : α → Sort u₁} {β : ∀ x, α₁ x → Sort v} {γ : ∀ x y, β x y → Sort w} (f : ∀ x y, (z : β x y) ×' γ x y z) : (g : ∀ x y, β x y) ×' ∀ x y, γ x y (g x y) :=
  ⟨(f · · |>.1), (f · · |>.2)⟩

def Exp'.eq_app {t₂} {e : Exp' n t₂} {v es e₁} {e₂ : Tm v t₁} : e.1 v es = .app e₁ e₂ → (e₁ : _) × (e₂ : Exp' n t₁) ×' e = .app e₁ e₂ := by
  intro h
  have h₁ : ∀ v' es', (e₁ : _) × (e₂ : Tm v' t₁) ×' e.1 v' es' = .app e₁ e₂ := by
    intro v' es'
    have := h ▸ e.2 (λ t (_ : v t) (_ : v' t) => True) es es' λ _ _ => ⟨⟩
    generalize e.1 v' es' = e' at this
    cases e' <;> dsimp! at this
    cases this.1
    exact ⟨_, _, rfl⟩
  clear v es e₁ e₂ h
  have ⟨e₁, h₂⟩ := forall₂_sigma h₁
  have ⟨e₂, h₃⟩ := forall₂_psigma h₂
  have h : e.1 = _ := funext (funext <| h₃ ·)
  clear h₁ h₂ h₃
  refine ⟨⟨e₁, λ r xs xs' hxs => ?_⟩, ⟨e₂, λ r xs xs' hxs => ?_⟩, Subtype.eq h⟩
  all_goals
    have ⟨_, _, _⟩ := h ▸ e.2 r xs xs' hxs
    assumption

def Exp.subst (e₁ : Exp₁ t₁ t₂) (e₂ : Exp t₁) : Exp t₂ :=
  ⟨λ _ => (e₁.1 _ (e₂.1 _)).flatten, λ _ => Tm.liftRel_flatten <| e₁.2 _ _ _ <| e₂.2 _⟩

def Exp.rec' {motive : ∀ t, Exp t → Sort u}
  (triv : motive .unit .triv)
  (abs : ∀ {t₁ t₂} e₁, (∀ e₂, motive t₁ e₂ → motive t₂ (e₂.subst e₁)) → motive (.ar t₁ t₂) (.abs e₁))
  (app : ∀ {t₁ t₂} e₁ e₂, motive _ e₁ → motive t₁ e₂ → motive t₂ (.app e₁ e₂))
{t} e : motive t e := by
  generalize h : e.1 (λ _ => Unit) = e'
  induction e' with
  | var x => cases Exp.ne_var h
  | triv => cases Exp.eq_triv h; exact triv
  | abs _ ih => have ⟨e₁, h⟩ := Exp.eq_abs h; cases h; simp [Exp.abs] at h; cases h; exact abs e₁ λ e₂ he₂ => ih () _ <| by dsimp [subst]; sorry
  | app _ _ ih₁ ih₂ => have ⟨e₁, e₂, h⟩ := Exp.eq_app h; cases h; simp [Exp.app] at h; exact app e₁ e₂ (ih₁ e₁ h.1) (ih₂ e₂ h.2)

inductive Val : Exp t → Prop
  | triv : Val .triv
  | abs : Val (.abs e)

theorem not_Val_app : ¬Val (.app e₁ e₂) := by
  intro h
  generalize he : Exp.app .. = e at h
  cases h <;> simp at he

def Val.rec' {motive : ∀ {t} (e : Exp t), Val e → Sort u}
  (triv : motive .triv .triv)
  (abs : ∀ {t₁ t₂ : Ty} {e : Exp₁ t₁ t₂}, motive (.abs e) .abs)
{t} {e : Exp t} v : motive e v :=
  match t with
  | .unit => by
    cases e using Exp.cases with
    | triv => exact triv
    | app => cases not_Val_app v
  | .ar t₁ t₂ => by
    cases e using Exp.cases with
    | abs => exact abs
    | app => cases not_Val_app v

inductive Step : Exp t → Exp t → Prop
  | app_abs : Val e₂ → Step (.app (.abs e₁) e₂) (e₂.subst e₁)
  | app₁ : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | app₂ : Val e₁ → Step e₂ e₂' → Step (.app e₁ e₂) (.app e₁ e₂')

theorem not_Step_Val {e : Exp t} (h : Val e) {e' : Exp t} : ¬Step e e' := by
  intro h'
  generalize he : e = e'' at h
  cases h <;> cases h' <;> simp at he

syntax "cases_all_tac" : tactic
macro "cases_all" : tactic => `(tactic| repeat cases_all_tac)
macro_rules | `(tactic| cases_all_tac) => `(tactic| cases ‹_ ∧ _›)
macro_rules | `(tactic| cases_all_tac) => `(tactic| cases ‹_ = _›)
macro_rules | `(tactic| cases_all_tac) => `(tactic| cases ‹HEq _ _›)

theorem Step_det {e₂ : Exp t} (h₁ : Step e e₁) (h₂ : Step e e₂) : e₁ = e₂ := by
  generalize he : e = e' at h₁
  induction h₁ <;> cases h₂ <;> simp at he <;> cases_all <;> simp at * <;> cases_all
  next => rfl
  next h => cases not_Step_Val .abs h
  next h₁ _ h₂ _ => cases not_Step_Val h₁ h₂
  next h _ => cases not_Step_Val .abs h
  next ih _ h => exact ih h rfl
  next h₂ _ _ _ h₁ => cases not_Step_Val h₁ h₂
  next h₂ _ _ h₁ _ => cases not_Step_Val h₁ h₂
  next h₁ _ _ _ h₂ => cases not_Step_Val h₁ h₂
  next ih _ h _ => exact ih h rfl

def progress (e : Exp t) : Val e ⊕' { e' // Step e e' } := by
  induction e using Exp.rec with
  | triv => exact .inl .triv
  | abs => exact .inl .abs
  | app e₁ e₂ ih₁ ih₂ =>
    refine .inr ?_
    cases ih₁ <;> rename_i ih₁
    . cases ih₂ <;> rename_i ih₂
      . cases ih₁ using Val.rec' with
        | abs => exact ⟨_, .app_abs ih₂⟩
      . exact ⟨_, .app₂ ih₁ ih₂.2⟩
    . exact ⟨_, .app₁ ih₁.2⟩

def progress' (e : Exp t) : Exp t :=
  match progress e with
  | .inl _ => e
  | .inr ⟨e, _⟩ => e

abbrev Steps {t} := ReflexiveTransitiveClosure (@Step t)

def HT (e : Exp t) : Prop :=
  match t with
  | .unit => Steps e .triv
  | .ar .. => ∃ e₁, Steps e (.abs e₁) ∧ ∀ e₂, HT e₂ → HT (e₂.subst e₁)

theorem Steps_inv (h₁ : Steps e e₁) (h₂ : Steps e e₂) (he₂ : Val e₂) : Steps e₁ e₂ := by
  induction h₂ using ReflexiveTransitiveClosure.recr with
  | base h₂ =>
    cases h₁ using ReflexiveTransitiveClosure.recr with
    | base h₁ => exact Reflexive.ofEq <| Step_det h₁ h₂
    | refl => exact .base h₂
    | trans h₁ h₁' =>
      cases Step_det h₁ h₂
      cases h₁' using ReflexiveTransitiveClosure.recr with
      | base h₁' => cases not_Step_Val he₂ h₁'
      | refl => exact .refl
      | trans h₁' => cases not_Step_Val he₂ h₁'
  | refl =>
    cases h₁ using ReflexiveTransitiveClosure.recr with
    | base h₁ => cases not_Step_Val he₂ h₁
    | refl => exact .refl
    | trans h₁ => cases not_Step_Val he₂ h₁
  | trans h₂ h₂' ih =>
    cases h₁ using ReflexiveTransitiveClosure.recr with
    | base h₁ => cases Step_det h₁ h₂; exact h₂'
    | refl => exact .trans (.base h₂) h₂'
    | trans h₁ h₁' => cases Step_det h₁ h₂; exact ih h₁' he₂

theorem Steps_HT {e' : Exp t} (h₁ : Steps e e') (h₂ : HT e') : HT e :=
  match t with
  | .unit => h₁.trans h₂
  | .ar .. => match h₂ with | ⟨_, h₂, h⟩ => ⟨_, h₁.trans h₂, h⟩

theorem HT_Steps {e' : Exp t} (h₁ : HT e) (h₂ : Steps e e') : HT e' :=
  match t with
  | .unit => Steps_inv h₂ h₁ .triv
  | .ar .. => match h₁ with | ⟨_, h₁, h⟩ => ⟨_, Steps_inv h₂ h₁ .abs, h⟩

theorem HT_imp_Steps_Val {e : Exp t} : HT e → ∃ e', Steps e e' ∧ Val e' ∧ HT e' :=
  match t with
  | .unit => λ h => ⟨.triv, h, .triv, .refl⟩
  | .ar .. => λ ⟨e', h, h'⟩ => ⟨.abs e', h, .abs, e', .refl, h'⟩

theorem All_HT {e : Exp t} : HT e := by
  induction e using Exp.rec' with
  | triv => exact .refl
  | abs e₁ ih => exact ⟨e₁, .refl, ih⟩
  | app e₁ e₂ ih₁ ih₂ =>
    have ⟨e₁', h₁, h₂⟩ := ih₁
    apply Steps_HT <| h₁.map' .app₁
    clear e₁ ih₁ h₁
    have ⟨e₂', h₁, h₃, h₄⟩ := HT_imp_Steps_Val ih₂
    apply Steps_HT <| h₁.map' (.app₂ .abs)
    clear e₂ ih₂ h₁
    apply Steps_HT <| .base <| .app_abs h₃
    exact h₂ e₂' h₄
