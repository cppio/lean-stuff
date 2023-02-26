import Common.Rel

inductive Ty
  | ar : Ty → Ty → Ty
  | unit : Ty
  | prod : Ty → Ty → Ty
  | void : Ty
  | sum : Ty → Ty → Ty

variable (v : Ty → Type) in
inductive Tm : Ty → Type
  | var : v t → Tm t
  | abs : (v t₁ → Tm t₂) → Tm (.ar t₁ t₂)
  | app : Tm (.ar t₁ t₂) → Tm t₁ → Tm t₂
  | triv : Tm .unit
  | pair : Tm t₁ → Tm t₂ → Tm (.prod t₁ t₂)
  | fst : Tm (.prod t₁ t₂) → Tm t₁
  | snd : Tm (.prod t₁ t₂) → Tm t₂
  | absurd : Tm .void → Tm t
  | inl : Tm t₁ → Tm (.sum t₁ t₂)
  | inr : Tm t₂ → Tm (.sum t₁ t₂)
  | case : Tm (.sum t₁ t₂) → (v t₁ → Tm t) → (v t₂ → Tm t) → Tm t

abbrev Exp t := ∀ v, Tm v t
def Exp₁ t₁ t₂ := ∀ v, v t₁ → Tm v t₂

@[local simp]
theorem forall_and {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨λ h => ⟨λ x => (h x).1, λ x => (h x).2⟩, λ h x => ⟨h.1 x, h.2 x⟩⟩

@[local simp]
theorem inhabited_arrow [Inhabited α] {p : Prop} : (α → p) ↔ p :=
  ⟨λ h => h default, λ h _ => h⟩

def Exp.abs (e : Exp₁ t₁ t₂) : Exp (.ar t₁ t₂) :=
  λ _ => .abs (e _)

@[simp]
theorem Exp.abs.injIff : @abs t₁ t₂ e = @abs t₁ t₂ e' ↔ e = e' := by
  constructor
  . intro h
    have h := congrFun h
    simp [abs] at h
    cases (funext h : e = e')
    simp
  . exact λ | rfl => rfl

def Exp.app (e₁ : Exp (.ar t₁ t₂)) (e₂ : Exp t₁) : Exp t₂ :=
  λ _ => .app (e₁ _) (e₂ _)

@[simp]
theorem Exp.app.injIff : @app t₁ t₂ e₁ e₂ = @app t₁' t₂ e₁' e₂' ↔ t₁ = t₁' ∧ HEq e₁ e₁' ∧ HEq e₂ e₂' := by
  constructor
  . intro h
    have h := congrFun h
    simp [app] at h
    cases h.1
    simp at h
    cases (funext h.1 : e₁ = e₁')
    simp at h
    cases (funext h : e₂ = e₂')
    simp
  . exact λ ⟨rfl, .refl _, .refl _⟩ => rfl

def Exp.triv : Exp .unit :=
  λ _ => .triv

def Exp.pair (e₁ : Exp t₁) (e₂ : Exp t₂) : Exp (.prod t₁ t₂) :=
  λ _ => .pair (e₁ _) (e₂ _)

@[simp]
theorem Exp.pair.injIff : @pair t₁ t₂ e₁ e₂ = @pair t₁ t₂ e₁' e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  constructor
  . intro h
    have h := congrFun h
    simp [pair] at h
    cases (funext h.1 : e₁ = e₁')
    simp at h
    cases (funext h : e₂ = e₂')
    simp
  . exact λ ⟨rfl, rfl⟩ => rfl

def Exp.fst (e : Exp (.prod t₁ t₂)) : Exp t₁ :=
  λ _ => .fst (e _)

@[simp]
theorem Exp.fst.injIff : @fst t₁ t₂ e = @fst t₁ t₂' e' ↔ t₂ = t₂' ∧ HEq e e' := by
  constructor
  . intro h
    have h := congrFun h
    simp [fst] at h
    cases h.1
    simp at h
    cases (funext h : e = e')
    simp
  . exact λ ⟨rfl, .refl _⟩ => rfl

def Exp.snd (e : Exp (.prod t₁ t₂)) : Exp t₂ :=
  λ _ => .snd (e _)

@[simp]
theorem Exp.snd.injIff : @snd t₁ t₂ e = @snd t₁' t₂ e' ↔ t₁ = t₁' ∧ HEq e e' := by
  constructor
  . intro h
    have h := congrFun h
    simp [snd] at h
    cases h.1
    simp at h
    cases (funext h : e = e')
    simp
  . exact λ ⟨rfl, .refl _⟩ => rfl

def Exp.absurd (e : Exp .void) : Exp t :=
  λ _ => .absurd (e _)

@[simp]
theorem Exp.absurd.injIff : @absurd t e = @absurd t e' ↔ e = e' := by
  constructor
  . intro h
    have h := congrFun h
    simp [absurd] at h
    cases (funext h : e = e')
    simp
  . exact λ | rfl => rfl

def Exp.inl (e : Exp t₁) : Exp (.sum t₁ t₂) :=
  λ _ => .inl (e _)

@[simp]
theorem Exp.inl.injIff : @inl t₁ t₂ e = @inl t₁ t₂ e' ↔ e = e' := by
  constructor
  . intro h
    have h := congrFun h
    simp [inl] at h
    cases (funext h : e = e')
    simp
  . exact λ | rfl => rfl

def Exp.inr (e : Exp t₂) : Exp (.sum t₁ t₂) :=
  λ _ => .inr (e _)

@[simp]
theorem Exp.inr.injIff : @inr t₁ t₂ e = @inr t₁ t₂ e' ↔ e = e' := by
  constructor
  . intro h
    have h := congrFun h
    simp [inr] at h
    cases (funext h : e = e')
    simp
  . exact λ | rfl => rfl

def Exp.case (e : Exp (.sum t₁ t₂)) (e₁ : Exp₁ t₁ t) (e₂ : Exp₁ t₂ t) : Exp t :=
  λ _ => .case (e _) (e₁ _) (e₂ _)

@[simp]
theorem Exp.case.injIff : @case t₁ t₂ t e e₁ e₂ = @case t₁' t₂' t e' e₁' e₂' ↔ t₁ = t₁' ∧ t₂ = t₂' ∧ HEq e e' ∧ HEq e₁ e₁' ∧ HEq e₂ e₂' := by
  constructor
  . intro h
    have h := congrFun h
    simp [case] at h
    cases h.1
    simp at h
    cases h.1
    simp at h
    cases (funext h.1 : e = e')
    simp at h
    cases (funext h.1 : e₁ = e₁')
    simp at h
    cases (funext h : e₂ = e₂')
    simp
  . exact λ ⟨rfl, rfl, .refl _, .refl _, .refl _⟩ => rfl

@[simp] theorem Exp.abs_ne_app : abs e ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.abs_ne_fst : abs e ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.abs_ne_snd : abs e ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.abs_ne_absurd : abs e ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.abs_ne_case : abs e ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_abs : app e₁ e₂ ≠ abs e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_triv : app e₁ e₂ ≠ triv := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_pair : app e₁ e₂ ≠ pair e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_fst : app e₁ e₂ ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_snd : app e₁ e₂ ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_absurd : app e₁ e₂ ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_inl : app e₁ e₂ ≠ inl e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_inr : app e₁ e₂ ≠ inr e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.app_ne_case : app e₁ e₂ ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.triv_ne_app : triv ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.triv_ne_fst : triv ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.triv_ne_snd : triv ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.triv_ne_absurd : triv ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.triv_ne_case : triv ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.pair_ne_app : pair e₁ e₂ ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.pair_ne_fst : pair e₁ e₂ ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.pair_ne_snd : pair e₁ e₂ ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.pair_ne_absurd : pair e₁ e₂ ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.pair_ne_case : pair e₁ e₂ ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_abs : fst e ≠ abs e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_app : fst e ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_triv : fst e ≠ triv := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_pair : fst e ≠ pair e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_snd : fst e ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_absurd : fst e ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_inl : fst e ≠ inl e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_inr : fst e ≠ inr e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.fst_ne_case : fst e ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_abs : snd e ≠ abs e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_app : snd e ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_triv : snd e ≠ triv := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_pair : snd e ≠ pair e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_fst : snd e ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_absurd : snd e ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_inl : snd e ≠ inl e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_inr : snd e ≠ inr e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.snd_ne_case : snd e ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_abs : absurd e ≠ abs e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_app : absurd e ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_triv : absurd e ≠ triv := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_pair : absurd e ≠ pair e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_fst : absurd e ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_snd : absurd e ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_inl : absurd e ≠ @inl _ t₂' e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_inr : absurd e ≠ @inr _ t₂' e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.absurd_ne_case : absurd e ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inl_ne_app : inl e ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inl_ne_fst : inl e ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inl_ne_snd : inl e ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inl_ne_absurd : @inl _ t₂ e ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inl_ne_inr : inl e ≠ inr e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inl_ne_case : inl e ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inr_ne_app : inr e ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inr_ne_fst : inr e ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inr_ne_snd : inr e ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inr_ne_absurd : @inr _ t₂ e ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inr_ne_inl : inr e ≠ inl e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.inr_ne_case : inr e ≠ case e' e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_abs : case e e₁ e₂ ≠ abs e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_app : case e e₁ e₂ ≠ app e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_triv : case e e₁ e₂ ≠ triv := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_pair : case e e₁ e₂ ≠ pair e₁' e₂' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_fst : case e e₁ e₂ ≠ fst e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_snd : case e e₁ e₂ ≠ snd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_absurd : case e e₁ e₂ ≠ absurd e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_inl : case e e₁ e₂ ≠ inl e' := λ h => nomatch congrFun h λ _ => Empty
@[simp] theorem Exp.case_ne_inr : case e e₁ e₂ ≠ inr e' := λ h => nomatch congrFun h λ _ => Empty

def Tm.toString : (Tm (λ _ => Nat) t) → StateM Nat String
  | .var x => return s!"x{x}"
  | .abs e => do
    let x ← getModify .succ
    return s!"(λ x{x}. {← toString (e x)})"
  | .app e₁ e₂ => return s!"({← toString e₁} {← toString e₂})"
  | .triv => return "triv"
  | .pair e₁ e₂ => return s!"pair({← toString e₁}, {← toString e₂}⟩"
  | .fst e => return s!"fst({← toString e})"
  | .snd e => return s!"snd({← toString e})"
  | .absurd e => return s!"absurd({← toString e})"
  | .inl e => return s!"inl({← toString e})"
  | .inr e => return s!"inr({← toString e})"
  | .case e e₁ e₂ => do
    let x ← getModify .succ
    let y ← getModify .succ
    return s!"case({← toString e}, {x}. {← toString (e₁ x)}, {y}. {← toString (e₂ y)})"

instance : ToString (Exp t) where
  toString e := (e _).toString.run' .zero

def Tm.flatten : Tm (Tm v) t → Tm v t
  | .var x => x
  | .abs e => .abs λ x => (e (.var x)).flatten
  | .app e₁ e₂ => .app e₁.flatten e₂.flatten
  | .triv => .triv
  | .pair e₁ e₂ => .pair e₁.flatten e₂.flatten
  | .fst e => .fst e.flatten
  | .snd e => .snd e.flatten
  | .absurd e => .absurd e.flatten
  | .inl e => .inl e.flatten
  | .inr e => .inr e.flatten
  | .case e e₁ e₂ => .case e.flatten (λ x => (e₁ (.var x)).flatten) (λ y => (e₂ (.var y)).flatten)

def Exp.subst (e₁ : Exp t₁) (e₂ : Exp₁ t₁ t₂) : Exp t₂
  | _ => Tm.flatten <| e₂ _ <| e₁ _

inductive Val : Exp t → Prop
  | abs {e : Exp₁ t₁ t₂} : Val (Exp.abs e)
  | triv : Val Exp.triv
  | pair {e₁ : Exp t₁} {e₂ : Exp t₂} : Val e₁ → Val e₂ → Val (Exp.pair e₁ e₂)
  | inl {e : Exp t₁} : Val e → Val (Exp.inl e)
  | inr {e : Exp t₂} : Val e → Val (Exp.inr e)

inductive Step : Exp t → Exp t → Prop
  | app_abs {e₁ : Exp₁ t₁ t₂} {e₂ : Exp t₁} : Val e₂ → Step (Exp.app (Exp.abs e₁) e₂) (Exp.subst e₂ e₁)
  | fst_pair {e₁ : Exp t₁} {e₂ : Exp t₂} : Val e₁ → Val e₂ → Step (Exp.fst (Exp.pair e₁ e₂)) e₁
  | snd_pair {e₁ : Exp t₁} {e₂ : Exp t₂} : Val e₁ → Val e₂ → Step (Exp.snd (Exp.pair e₁ e₂)) e₂
  | case_inl {e : Exp t₁} {e₁ : Exp₁ t₁ t} {e₂ : Exp₁ t₂ t} : Val e → Step (Exp.case (Exp.inl e) e₁ e₂) (Exp.subst e e₁)
  | case_inr {e : Exp t₂} {e₁ : Exp₁ t₁ t} {e₂ : Exp₁ t₂ t} : Val e → Step (Exp.case (Exp.inr e) e₁ e₂) (Exp.subst e e₂)

  | app₁ {e₁ e₁' : Exp (.ar t₁ t₂)} {e₂ : Exp t₁} : Step e₁ e₁' → Step (Exp.app e₁ e₂) (Exp.app e₁' e₂)
  | app₂ {e₁ : Exp (.ar t₁ t₂)} {e₂ e₂' : Exp t₁} : Val e₁ → Step e₂ e₂' → Step (Exp.app e₁ e₂) (Exp.app e₁ e₂')
  | pair₁ {e₁ e₁' : Exp t₁} {e₂ : Exp t₂} : Step e₁ e₁' → Step (Exp.pair e₁ e₂) (Exp.pair e₁' e₂)
  | pair₂ {e₁ : Exp t₁} {e₂ e₂' : Exp t₂} : Val e₁ → Step e₂ e₂' → Step (Exp.pair e₁ e₂) (Exp.pair e₁ e₂')
  | fst {e e' : Exp (.prod t₁ t₂)} : Step e e' → Step (Exp.fst e) (Exp.fst e')
  | snd {e e' : Exp (.prod t₁ t₂)} : Step e e' → Step (Exp.snd e) (Exp.snd e')
  | absurd {e e' : Exp .void} : Step e e' → Step (Exp.absurd e) (Exp.absurd e')
  | inl {e e' : Exp t₁} : Step e e' → Step (Exp.inl e) (Exp.inl e')
  | inr {e e' : Exp t₂} : Step e e' → Step (Exp.inr e) (Exp.inr e')
  | case {e e' : Exp (.sum t₁ t₂)} {e₁ : Exp₁ t₁ t} {e₂ : Exp₁ t₂ t} : Step e e' → Step (Exp.case e e₁ e₂) (Exp.case e' e₁ e₂)

syntax "subst_all_tac" : tactic
macro "subst_all" : tactic => `(tactic| repeat subst_all_tac)
macro_rules | `(tactic| subst_all_tac) => `(tactic| cases ‹_ ∧ _›)
macro_rules | `(tactic| subst_all_tac) => `(tactic| cases ‹_ = _›)
macro_rules | `(tactic| subst_all_tac) => `(tactic| cases ‹HEq _ _›)

theorem Step_nand_Val : Step e e' → Val e → False := by
  intro h₁ h₂
  generalize he' : e = e' at h₁
  induction h₂ <;> cases h₁ <;> simp at he'
  next ih _ _ _ _ _ => exact ih _ he'.1 ‹_›
  next ih _ _ _ _ _ => exact ih _ he'.2 ‹_›
  next ih _ _ _ => exact ih _ he' ‹_›
  next ih _ _ _ => exact ih _ he' ‹_›

theorem Functional : Step e e₁ → Step e e₂ → e₁ = e₂ := by
  intro h₁ h₂
  generalize he' : e = e' at h₁
  induction h₁ <;> cases h₂ <;> (try cases congrFun he' λ _ => Unit) <;> simp at he'
  case app₁ => cases ‹Step _ _› <;> subst_all <;> simp at *
  all_goals
    subst_all
    (try simp at *; subst_all; rfl)
    (try next ih _ _ => cases ih ‹_› rfl; rfl)
    (try next ih _ _ _ => cases ih ‹_› rfl; rfl)
    (try cases Step_nand_Val ‹_› ‹_›)
    (try cases flip Step_nand_Val ‹_› ‹_›)
    (try cases Step_nand_Val ‹_› (.pair ‹_› ‹_›))
    (try cases Step_nand_Val ‹_› (.inl ‹_›))
    (try cases Step_nand_Val ‹_› (.inr ‹_›))
  cases Step_nand_Val ‹_› .abs

inductive Closed : Exp t → Prop
  | abs {e : Exp₁ t₁ t₂} : Closed (Exp.abs e)
  | app {e₁ : Exp (.ar t₁ t₂)} {e₂ : Exp t₁} : Closed e₁ → Closed e₂ → Closed (Exp.app e₁ e₂)
  | triv : Closed Exp.triv
  | pair {e₁ : Exp t₁} {e₂ : Exp t₂} : Closed e₁ → Closed e₂ → Closed (Exp.pair e₁ e₂)
  | fst {e : Exp (.prod t₁ t₂)} : Closed e → Closed (Exp.fst e)
  | snd {e : Exp (.prod t₁ t₂)} : Closed e → Closed (Exp.snd e)
  | absurd {e : Exp .void} : Closed e → Closed (Exp.absurd e)
  | inl {e : Exp t₁} : Closed e → Closed (Exp.inl e)
  | inr {e : Exp t₂} : Closed e → Closed (Exp.inr e)
  | case {e : Exp (.sum t₁ t₂)} {e₁ : Exp₁ t₁ t} {e₂ : Exp₁ t₂ t} : Closed e → Closed (Exp.case e e₁ e₂)

theorem progress (h : Closed e) : Val e ∨ ∃ e', Step e e' := by
  induction h with
  | abs => exact .inl .abs
  | app _ _ ih₁ ih₂ => refine .inr ?_; cases ih₁ <;> rename_i ih₁; cases ih₂ <;> rename_i ih₂; cases ih₁; exact ⟨_, .app_abs ih₂⟩; let ⟨_, ih₂⟩ := ih₂; exact ⟨_, .app₂ ih₁ ih₂⟩; let ⟨_, ih₁⟩ := ih₁; exact ⟨_, .app₁ ih₁⟩
  | triv => exact .inl .triv
  | pair _ _ ih₁ ih₂ => cases ih₁ <;> rename_i ih₁; cases ih₂ <;> rename_i ih₂; exact .inl (.pair ih₁ ih₂); let ⟨_, ih₂⟩ := ih₂; exact .inr ⟨_, .pair₂ ih₁ ih₂⟩; let ⟨_, ih₁⟩ := ih₁; exact .inr ⟨_, .pair₁ ih₁⟩
  | fst _ ih => refine .inr ?_; cases ih <;> rename_i ih; let .pair ih₁ ih₂ := ih; exact ⟨_, .fst_pair ih₁ ih₂⟩; let ⟨_, ih⟩ := ih; exact ⟨_, .fst ih⟩
  | snd _ ih => refine .inr ?_; cases ih <;> rename_i ih; let .pair ih₁ ih₂ := ih; exact ⟨_, .snd_pair ih₁ ih₂⟩; let ⟨_, ih⟩ := ih; exact ⟨_, .snd ih⟩
  | absurd _ ih => refine .inr ?_; cases ih <;> rename_i ih; cases ih; let ⟨_, ih⟩ := ih; exact ⟨_, .absurd ih⟩
  | inl _ ih => cases ih <;> rename_i ih; exact .inl (.inl ih); let ⟨_, ih⟩ := ih; exact .inr ⟨_, .inl ih⟩
  | inr _ ih => cases ih <;> rename_i ih; exact .inl (.inr ih); let ⟨_, ih⟩ := ih; exact .inr ⟨_, .inr ih⟩
  | case _ ih => refine .inr ?_; cases ih <;> rename_i ih; (cases ih with | inl ih => exact ⟨_, .case_inl ih⟩ | inr ih => exact ⟨_, .case_inr ih⟩); let ⟨_, ih⟩ := ih; exact ⟨_, .case ih⟩

theorem Val_final (h : Val e) : ¬Step e e' := by
  intro h'
  generalize h₁ : e = e₁ at h
  induction h <;> cases h' <;> simp at h₁
  case pair₁ ih _ _ _ h _ => exact ih h h₁.1
  case pair₂ ih _ _ _ _ h => exact ih h h₁.2
  case inl ih _ _ h => exact ih h h₁
  case inr ih _ _ h => exact ih h h₁

def Halts (e : Exp t) : Prop :=
  ∃ e', Val e' ∧ ReflexiveTransitiveClosure Step e e'

def Terminates : ∀ {t}, Exp t → Prop
  | .ar .., e => ∃ e', ReflexiveTransitiveClosure Step e (Exp.abs e') ∧ ∀ e₂, Terminates e₂ → Terminates (Exp.subst e₂ e')
  | .unit, e => ReflexiveTransitiveClosure Step e Exp.triv
  | .prod .., e => ∃ e₁ e₂, ReflexiveTransitiveClosure Step e (Exp.pair e₁ e₂) ∧ Terminates e₁ ∧ Terminates e₂
  | .void, _ => False
  | .sum .., e => (∃ e₁, ReflexiveTransitiveClosure Step e (Exp.inl e₁) ∧ Terminates e₁) ∨ (∃ e₂, ReflexiveTransitiveClosure Step e (Exp.inr e₂) ∧ Terminates e₂)

theorem Steps_Terminates {e e' : Exp t} (h₁ : ReflexiveTransitiveClosure Step e e') (h₂ : Terminates e') : Terminates e :=
  match t with
  | .ar .. => match h₂ with | ⟨e', h₂, h⟩ => ⟨e', h₁.trans h₂, h⟩
  | .unit => h₁.trans h₂
  | .prod .. => match h₂ with | ⟨e₁, e₂, h₂, h⟩ => ⟨e₁, e₂, h₁.trans h₂, h⟩
  | .void => h₂
  | .sum .. => match h₂ with | .inl ⟨e', h₂, h⟩ => .inl ⟨e', h₁.trans h₂, h⟩ | .inr ⟨e', h₂, h⟩ => .inr ⟨e', h₁.trans h₂, h⟩

theorem Steps_Inv (h₁ : ReflexiveTransitiveClosure Step e e₁) (h₂ : ReflexiveTransitiveClosure Step e e₂) (he₂ : Val e₂) : ReflexiveTransitiveClosure Step e₁ e₂ := by
  induction h₂ using ReflexiveTransitiveClosure.recr with
  | base h₂ =>
    cases h₁ using ReflexiveTransitiveClosure.recr with
    | base h₁ => exact Reflexive.ofEq <| Functional h₁ h₂
    | refl => exact .base h₂
    | trans h₁ h₁' =>
      cases Functional h₁ h₂
      cases h₁' using ReflexiveTransitiveClosure.recr with
      | base h₁' => cases Val_final he₂ h₁'
      | refl => exact .refl
      | trans h₁' => cases Val_final he₂ h₁'
  | refl =>
    cases h₁ using ReflexiveTransitiveClosure.recr with
    | base h₁ => cases Val_final he₂ h₁
    | refl => exact .refl
    | trans h₁ => cases Val_final he₂ h₁
  | trans h₂ h₂' ih =>
    cases h₁ using ReflexiveTransitiveClosure.recr with
    | base h₁ => cases Functional h₁ h₂; exact h₂'
    | refl => exact .trans (.base h₂) h₂'
    | trans h₁ h₁' => cases Functional h₁ h₂; exact ih h₁' he₂

theorem Terminates_Halts {e : Exp t} : Terminates e → Halts e := by
  unfold Halts
  induction t with
  | ar => exact λ ⟨_, h, _⟩ => ⟨_, .abs, h⟩
  | unit => exact λ h => ⟨_, .triv, h⟩
  | prod _ _ ih₁ ih₂ =>
    intro ⟨e₁, e₂, h₃, h₁, h₂⟩
    have ⟨e₁', h₁', h₁⟩ := ih₁ h₁
    have ⟨e₂', h₂', h₂⟩ := ih₂ h₂
    have h₁ := ReflexiveTransitiveClosure.map' (f := (Exp.pair · e₂)) Step.pair₁ h₁
    have h₂ := ReflexiveTransitiveClosure.map' (f := Exp.pair e₁') (Step.pair₂ h₁') h₂
    exact ⟨_, .pair h₁' h₂', .trans h₃ <| .trans h₁ h₂⟩
  | void => exact λ h => nomatch h
  | sum _ _ ih₁ ih₂ =>
    intro h
    match h with
    | .inl ⟨e, h₂, h₁⟩ =>
      have ⟨e', h₁', h₁⟩ := ih₁ h₁
      have' h₁ := ReflexiveTransitiveClosure.map' (f := Exp.inl) Step.inl h₁
      exact ⟨_, .inl h₁', .trans h₂ h₁⟩
    | .inr ⟨e, h₂, h₁⟩ =>
      have ⟨e', h₁', h₁⟩ := ih₂ h₁
      have' h₁ := ReflexiveTransitiveClosure.map' (f := Exp.inr) Step.inr h₁
      exact ⟨_, .inr h₁', .trans h₂ h₁⟩

theorem Steps_Rev_Terminates {e e' : Exp t} (h₁ : ReflexiveTransitiveClosure Step e e') (h₂ : Terminates e) : Terminates e' := by
  induction t with
  | ar => exact match h₂ with | ⟨e', h₂, h⟩ => ⟨e', Steps_Inv h₁ h₂ .abs, h⟩
  | unit => exact Steps_Inv h₁ h₂ .triv
  | prod _ _ ih₁ ih₂ => exact
    match h₂ with
    | ⟨e₁, e₂, h₂, he₁, he₂⟩ =>
      have ⟨e₁', h₁', h₁''⟩ := Terminates_Halts he₁
      have ⟨e₂', h₂', h₂''⟩ := Terminates_Halts he₂
      have h₁''' := ReflexiveTransitiveClosure.map' (f := (Exp.pair · e₂)) Step.pair₁ h₁''
      have h₂''' := ReflexiveTransitiveClosure.map' (f := Exp.pair e₁') (Step.pair₂ h₁') h₂''
      ⟨e₁', e₂', Steps_Inv h₁ (h₂.trans <| h₁'''.trans h₂''') <| .pair h₁' h₂', ih₁ h₁'' he₁, ih₂ h₂'' he₂⟩
  | void => exact h₂
  | sum t₁ t₂ ih₁ ih₂ => exact
    match h₂ with
    | .inl ⟨e', h₂, h⟩ =>
      have ⟨e'', h', h''⟩ := Terminates_Halts h
      have h''' := ReflexiveTransitiveClosure.map' (f := @Exp.inl t₁ t₂) Step.inl h''
      .inl ⟨e'', Steps_Inv h₁ (h₂.trans h''') <| .inl h', ih₁ h'' h⟩
    | .inr ⟨e', h₂, h⟩ =>
      have ⟨e'', h', h''⟩ := Terminates_Halts h
      have h''' := ReflexiveTransitiveClosure.map' (f := Exp.inr) Step.inr h''
      .inr ⟨e'', Steps_Inv h₁ (h₂.trans h''') <| .inr h', ih₂ h'' h⟩

theorem All_Terminate (h : Closed e) : Terminates e := by
  induction h with
  | abs => exact ⟨_, .refl, sorry⟩
  | app _ _ ih₁ ih₂ =>
    have ⟨e₁', h₁⟩ := ih₁
    have ⟨e₂, h₂, he₂⟩ := Terminates_iff_Halts.mpr ih₂
    apply Steps_Terminates <| .map' .app₁ h₁
    apply Steps_Terminates <| .map' (.app₂ .abs) he₂
    apply Steps_Terminates <| .base <| .app_abs h₂
    sorry
  | triv => exact .refl
  | pair _ _ ih₁ ih₂ => exact ⟨_, _, .refl, ih₁, ih₂⟩
  | fst _ ih =>
    have ⟨e₁, e₂, h₁, h₂, h₃⟩ := ih
    have ⟨e₁', h₁', he₁'⟩ := Terminates_iff_Halts.mpr h₂
    have ⟨e₂', h₂', he₂'⟩ := Terminates_iff_Halts.mpr h₃
    apply Terminates_iff_Halts.mp
    have h₁ := ReflexiveTransitiveClosure.map' (f := Exp.fst) Step.fst h₁
    have h₂ := ReflexiveTransitiveClosure.map' (f := Exp.fst) Step.fst <| ReflexiveTransitiveClosure.map' (f := (Exp.pair · e₂)) Step.pair₁ he₁'
    have h₃ := ReflexiveTransitiveClosure.map' (f := Exp.fst) Step.fst <| ReflexiveTransitiveClosure.map' (f := Exp.pair e₁') (Step.pair₂ h₁') he₂'
    exact ⟨e₁', h₁', h₁.trans <| h₂.trans <| h₃.trans <| .base <| .fst_pair h₁' h₂'⟩
  | snd _ ih =>
    have ⟨e₁, e₂, h₁, h₂, h₃⟩ := ih
    have ⟨e₁', h₁', he₁'⟩ := Terminates_iff_Halts.mpr h₂
    have ⟨e₂', h₂', he₂'⟩ := Terminates_iff_Halts.mpr h₃
    apply Terminates_iff_Halts.mp
    have h₁ := ReflexiveTransitiveClosure.map' (f := Exp.snd) Step.snd h₁
    have h₂ := ReflexiveTransitiveClosure.map' (f := Exp.snd) Step.snd <| ReflexiveTransitiveClosure.map' (f := (Exp.pair · e₂)) Step.pair₁ he₁'
    have h₃ := ReflexiveTransitiveClosure.map' (f := Exp.snd) Step.snd <| ReflexiveTransitiveClosure.map' (f := Exp.pair e₁') (Step.pair₂ h₁') he₂'
    exact ⟨e₂', h₂', h₁.trans <| h₂.trans <| h₃.trans <| .base <| .snd_pair h₁' h₂'⟩
  | absurd _ ih => cases ih
  | inl _ ih => exact .inl ⟨_, .refl, ih⟩
  | inr _ ih => exact .inr ⟨_, .refl, ih⟩
  | case _ ih =>
    have ⟨e', h', he'⟩ := Terminates_iff_Halts.mpr ih
    apply Terminates_iff_Halts.mp
    cases h' with
    | inl h' => exact ⟨sorry, sorry, sorry⟩
    | inr h' => exact ⟨sorry, sorry, sorry⟩

/-
theorem Step_Halts (h : Step e e') : Halts e ↔ Halts e' := by
  induction h <;> constructor <;> (try case mpr => intro ⟨_, h₁, h₂⟩; refine ⟨_, h₁, .trans (.base ?_) h₂⟩; constructor; repeat assumption)
    <;> intro ⟨_, h₁, h₂⟩
    <;> refine ⟨_, h₁, ?_⟩
    <;> cases h₂ using ReflexiveTransitiveClosure.recr
    <;> (try cases Functional ‹_› (by constructor; repeat assumption); exact .refl)
    <;> (try cases Functional ‹_› (by constructor; repeat assumption); assumption)
    <;> (try generalize he' : Exp.app _ _ = e' at h₁; cases h₁ <;> simp at he'; done)
    <;> (try generalize he' : Exp.case _ _ _ = e' at h₁; cases h₁ <;> simp at he'; done)
    <;> (try generalize he' : Exp.fst _ = e' at h₁; cases h₁ <;> simp at he'; done)
    <;> (try generalize he' : Exp.snd _ = e' at h₁; cases h₁ <;> simp at he'; done)
    <;> (try generalize he' : Exp.pair _ _ = e' at h₁; cases h₁; simp at he'; subst_all; cases Step_nand_Val ‹_› ‹_›; done)
  . cases Functional ‹_› (.app₂ ‹_› ‹_›); exact .refl
  . cases Functional ‹_› (.app₂ ‹_› ‹_›); assumption
  . cases Functional ‹_› (.pair₂ ‹_› ‹_›); exact .refl
  . cases Functional ‹_› (.pair₂ ‹_› ‹_›); assumption
  . generalize he' : Exp.absurd _ = e' at h₁; cases h₁ <;> simp at he'
  . generalize he' : Exp.inl _ = e' at h₁; cases h₁ <;> simp at he'; subst_all; cases Step_nand_Val ‹_› ‹_›
  . generalize he' : Exp.inr _ = e' at h₁; cases h₁ <;> simp at he'; subst_all; cases Step_nand_Val ‹_› ‹_›

theorem Step_Terminates (h : Terminates e) (h' : Step e e') : Terminates e' := by
  induction h'
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . dsimp [Terminates] at h ⊢
    cases h with | _ h₁ h₂ =>
    constructor
    . rw [← Step_Halts (.pair₁ ‹_›)]
      assumption
    cases h₂ with | _ h₂ h₃ =>
    constructor
    . sorry
    . dsimp [Terminates] at h₃
      sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry

def A : Ty := .void
def B : Ty := .void
def C : Ty := .void
#eval (λ _ => .abs λ f => .abs λ x => .abs λ y => .app (.var f) (.pair (.var x) (.var y)) : Exp (.ar (.ar (.prod A B) C) (.ar A (.ar B C))))
#eval (λ _ => .abs λ f => .abs λ xy => .app (.app (.var f) (.fst (.var xy))) (.snd (.var xy)) : Exp (.ar (.ar A (.ar B C)) (.ar (.prod A B) C)))-/
