import Logic.Util

namespace Logic.Propositional.Linear

opaque BasePropn : Type

variable {Propn : Type}

inductive Ctx
  | nil
  | cons (Δ : Ctx) (A : Propn)

local notation "Ctx" => Ctx (Propn := Propn)

inductive Split : (Δ Δ₁ Δ₂ : Ctx) → Type
  | nil : Split .nil .nil .nil
  | cons₁ (s : Split Δ Δ₁ Δ₂) : Split (Δ.cons A) (Δ₁.cons A) Δ₂
  | cons₂ (s : Split Δ Δ₁ Δ₂) : Split (Δ.cons A) Δ₁ (Δ₂.cons A)

local notation "Split" => Split (Propn := Propn)

def Split.triv₁ : ∀ {Δ}, Split Δ Δ .nil
  | .nil => nil
  | .cons .. => triv₁.cons₁

def Split.triv₂ : ∀ {Δ}, Split Δ .nil Δ
  | .nil => nil
  | .cons .. => triv₂.cons₂

theorem Split.eq_triv₁ : ∀ s, (⟨Δ₁, s⟩ : Σ Δ₁, Split Δ Δ₁ .nil) = ⟨Δ, triv₁⟩
  | nil => rfl
  | cons₁ s => let .refl _ := s.eq_triv₁; rfl

theorem Split.eq_triv₂ : ∀ s, (⟨Δ₂, s⟩ : Σ Δ₂, Split Δ .nil Δ₂) = ⟨Δ, triv₂⟩
  | nil => rfl
  | cons₂ s => let .refl _ := s.eq_triv₂; rfl

def Split.flip : (s : Split Δ Δ₁ Δ₂) → Split Δ Δ₂ Δ₁
  | nil => nil
  | cons₁ s => s.flip.cons₂
  | cons₂ s => s.flip.cons₁

def Split.shift : (s : Split Δ Δ₁ Δ₂) → (s₁ : Split Δ₁ Δ₁₁ Δ₁₂) → {Δ'} × Split Δ Δ₁₁ Δ' × Split Δ' Δ₁₂ Δ₂
  | s, nil => ⟨triv₂, s⟩
  | cons₁ s, cons₁ s₁ => let ⟨s, s'⟩ := s.shift s₁; ⟨s.cons₁, s'⟩
  | cons₁ s, cons₂ s₁ => let ⟨s, s'⟩ := s.shift s₁; ⟨s.cons₂, s'.cons₁⟩
  | cons₂ s, s₁ => let ⟨s, s'⟩ := s.shift s₁; ⟨s.cons₂, s'.cons₂⟩

inductive Split₁ : (Δ : Ctx) → (A : Propn) → (Δ' : Ctx) → Type
  | here : Split₁ (Δ.cons A) A Δ
  | there (s : Split₁ Δ A Δ') : Split₁ (Δ.cons B) A (Δ'.cons B)

def Split₁.toSplit : (s : Split₁ Δ A Δ') → Split Δ (.cons .nil A) Δ'
  | here => .cons₁ .triv₂
  | there s => s.toSplit.cons₂

def Split₁.ofSplit : (s : Split Δ (.cons .nil A) Δ') → Split₁ Δ A Δ'
  | .cons₁ s => let .refl _ := s.eq_triv₂; here
  | .cons₂ s => (ofSplit s).there

def Split.shift₁ (s : Split Δ Δ₁ Δ₂) (s₁ : Split₁ Δ₁ A Δ₁₂) : {Δ'} × Split₁ Δ A Δ' × Split Δ' Δ₁₂ Δ₂ :=
  let ⟨s, s'⟩ := s.shift s₁.toSplit
  ⟨.ofSplit s, s'⟩

inductive Subst (J : (Δ : Ctx) → (A : Propn) → Type) : (Δ Δ' : Ctx) → Type
  | nil : Subst J .nil .nil
  | cons (s : Split Δ' Δ₁ Δ₂) (D : J Δ₁ A) (δ : Subst J Δ Δ₂) : Subst J (Δ.cons A) Δ'

local notation "Subst" => Subst (Propn := Propn)

def Subst.map (f : ∀ {Δ A}, (D : J Δ A) → J' Δ A) : (δ : Subst J Δ Δ') → Subst J' Δ Δ'
  | nil => nil
  | cons s D δ => cons s (f D) (δ.map @f)

def Subst.split : (δ : Subst J Δ Δ') → (s : Split Δ Δ₁ Δ₂) → {Δ₁' Δ₂'} × Split Δ' Δ₁' Δ₂' × Subst J Δ₁ Δ₁' × Subst J Δ₂ Δ₂'
  | nil, .nil => ⟨.nil, nil, nil⟩
  | cons s' D δ, .cons₁ s => let ⟨s, δ₁, δ₂⟩ := δ.split s; let ⟨s, s'⟩ := s'.flip.shift s.flip; ⟨s.flip, cons s'.flip D δ₁, δ₂⟩
  | cons s' D δ, .cons₂ s => let ⟨s, δ₁, δ₂⟩ := δ.split s; let ⟨s, s'⟩ := s'.flip.shift s; ⟨s, δ₁, cons s'.flip D δ₂⟩

def Subst.split₁ (δ : Subst J Δ Δ') (s : Split₁ Δ A Δ₂) : {Δ₁' Δ₂'} × Split Δ' Δ₁' Δ₂' × J Δ₁' A × Subst J Δ₂ Δ₂' :=
  let ⟨s, cons s' D nil, δ⟩ := δ.split s.toSplit
  let .refl _ := s'.eq_triv₁
  ⟨s, D, δ⟩

inductive Hyp : (Δ : Ctx) → (A : Propn) → Type
  | mk : Hyp (.cons .nil A) A

def Subst.split₁' (δ : Subst Hyp Δ Δ') (s : Split₁ Δ A Δ₂) : {Δ₂'} × Split₁ Δ' A Δ₂' × Subst Hyp Δ₂ Δ₂' :=
  let ⟨s, cons s' .mk nil, δ⟩ := δ.split s.toSplit
  let .refl _ := s'.eq_triv₁
  ⟨.ofSplit s, δ⟩

class Judge (J : (Δ : Ctx) → (A : Propn) → Type) where
  hyp : J (.cons .nil A) A

local notation "Judge" => Judge (Propn := Propn)

instance Hyp.judge : Judge Hyp where
  hyp := mk

def Subst.id [j : Judge J] : ∀ {Δ}, Subst J Δ Δ
  | .nil => nil
  | .cons .. => cons (.cons₁ .triv₂) j.hyp id

def Subst.lift [j : Judge J] : (δ : Subst J Δ Δ') → Subst J (Δ.cons A) (Δ'.cons A) :=
  cons (.cons₁ .triv₂) j.hyp

def Subst.exchange : Subst Hyp (Ctx.cons Δ A |>.cons B) (Δ.cons B |>.cons A) :=
  cons (.cons₂ (.cons₁ .triv₂)) .mk id

def Subst.exchange₂ : Subst Hyp (Ctx.cons Δ A |>.cons B |>.cons C) (Δ.cons B |>.cons C |>.cons A) :=
  cons (.cons₂ (.cons₁ .triv₂)) .mk exchange

unif_hint (J : (x : α) → (Δ : Ctx) → (A : Propn) → Type) (Δ Δ' : Ctx) (x : α) where
  J ≟ fun _ => Hyp
  ⊢ Subst Hyp Δ Δ' ≟ Subst (J x) Δ Δ'
