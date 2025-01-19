import Logic.Propositional.Structural
import Logic.Propositional.Linear

namespace Logic.Propositional.Validity.Classical

inductive Propn
  | base (P : Linear.BasePropn)
  | one
  | zero
  | top
  | bot
  | neg (A : Propn)
  | tensor (A B : Propn)
  | plus (A B : Propn)
  | with (A B : Propn)
  | par (A B : Propn)
  | bang (A : Propn)
  | quest (A : Propn)

local notation "SCtx" => Structural.Ctx (Propn := Propn)
local notation "LCtx" => Linear.Ctx (Propn := Propn)
local notation "SHyp" => Structural.Hyp (Propn := Propn)
local notation "LHyp" => Linear.Hyp (Propn := Propn)
local notation "Split" => Linear.Split (Propn := Propn)
local notation "Split₁" => Linear.Split₁ (Propn := Propn)
local notation "SSubst" => Structural.Subst (Propn := Propn)
local notation "LSubst" => Linear.Subst (Propn := Propn)

/-! Sequent Calculus -/

namespace SC

inductive Seq : (Γ₁ Γ₂ : SCtx) → (Δ₁ Δ₂ : LCtx) → Type
  | id : Seq Γ₁ Γ₂ (.cons .nil (.base P)) (.cons .nil (.base P))
  | validR (v : SHyp Γ₂ A) (D : Seq Γ₁ Γ₂ Δ₁ (Δ₂.cons A)) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | validL (u : SHyp Γ₁ A) (D : Seq Γ₁ Γ₂ (Δ₁.cons A) Δ₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | oneR : Seq Γ₁ Γ₂ .nil (.cons .nil .one)
  | oneL (s : Split₁ Δ₁ .one Δ₁') (D : Seq Γ₁ Γ₂ Δ₁' Δ₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | zeroL (s : Split₁ Δ₁ .zero Δ₁') : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | topR (s : Split₁ Δ₂ .top Δ₂') : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | botR (s : Split₁ Δ₂ .bot Δ₂') (D : Seq Γ₁ Γ₂ Δ₁ Δ₂') : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | botL : Seq Γ₁ Γ₂ (.cons .nil .bot) .nil
  | negR (s : Split₁ Δ₂ A.neg Δ₂') (D : Seq Γ₁ Γ₂ (Δ₁.cons A) Δ₂') : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | negL (s : Split₁ Δ₁ A.neg Δ₁') (D : Seq Γ₁ Γ₂ Δ₁' (Δ₂.cons A)) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | tensorR (s : Split₁ Δ₂ (A.tensor B) Δ₂') (s₁ : Split Δ₁ Δ₁₁ Δ₁₂) (s₂ : Split Δ₂' Δ₂₁' Δ₂₂') (D₁ : Seq Γ₁ Γ₂ Δ₁₁ (Δ₂₁'.cons A)) (D₂ : Seq Γ₁ Γ₂ Δ₁₂ (Δ₂₂'.cons B)) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | tensorL (s : Split₁ Δ₁ (A.tensor B) Δ₁') (D : Seq Γ₁ Γ₂ (Δ₁'.cons A |>.cons B) Δ₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | plusR₁ (s : Split₁ Δ₂ (A.plus B) Δ₂') (D : Seq Γ₁ Γ₂ Δ₁ (Δ₂'.cons A)) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | plusR₂ (s : Split₁ Δ₂ (.plus A B) Δ₂') (D : Seq Γ₁ Γ₂ Δ₁ (Δ₂'.cons B)) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | plusL (s : Split₁ Δ₁ (A.plus B) Δ₁') (D₁ : Seq Γ₁ Γ₂ (Δ₁'.cons A) Δ₂) (D₂ : Seq Γ₁ Γ₂ (Δ₁'.cons B) Δ₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | withR (s : Split₁ Δ₂ (A.with B) Δ₂') (D₁ : Seq Γ₁ Γ₂ Δ₁ (Δ₂'.cons A)) (D₂ : Seq Γ₁ Γ₂ Δ₁ (Δ₂'.cons B)) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | withL₁ (s : Split₁ Δ₁ (A.with B) Δ₁') (D : Seq Γ₁ Γ₂ (Δ₁'.cons A) Δ₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | withL₂ (s : Split₁ Δ₁ (.with A B) Δ₁') (D : Seq Γ₁ Γ₂ (Δ₁'.cons B) Δ₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | parR (s : Split₁ Δ₂ (A.par B) Δ₂') (D : Seq Γ₁ Γ₂ Δ₁ (Δ₂'.cons A |>.cons B)) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | parL (s : Split₁ Δ₁ (A.par B) Δ₁') (s₁ : Split Δ₁' Δ₁₁' Δ₁₂') (s₂ : Split Δ₂ Δ₂₁ Δ₂₂) (D₁ : Seq Γ₁ Γ₂ (Δ₁₁'.cons A) Δ₂₁) (D₂ : Seq Γ₁ Γ₂ (Δ₁₂'.cons B) Δ₂₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | bangR (D : Seq Γ₁ Γ₂ .nil (.cons .nil A)) : Seq Γ₁ Γ₂ .nil (.cons .nil A.bang)
  | bangL (s : Split₁ Δ₁ A.bang Δ₁') (D : Seq (Γ₁.cons A) Γ₂ Δ₁' Δ₂) : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | questR (s : Split₁ Δ₂ A.quest Δ₂') (D : Seq Γ₁ (Γ₂.cons A) Δ₁ Δ₂') : Seq Γ₁ Γ₂ Δ₁ Δ₂
  | questL (D : Seq Γ₁ Γ₂ (.cons .nil A) .nil) : Seq Γ₁ Γ₂ (.cons .nil A.quest) .nil

def Seq.substS (γ₁ : SSubst SHyp Γ₁ Γ₁') (γ₂ : SSubst SHyp Γ₂ Γ₂') : (D : Seq Γ₁ Γ₂ Δ₁ Δ₂) → Seq Γ₁' Γ₂' Δ₁ Δ₂
  | id => id
  | validR v D => validR (γ₂ v) (D.substS γ₁ γ₂)
  | validL u D => validL (γ₁ u) (D.substS γ₁ γ₂)
  | oneR => oneR
  | oneL s D => oneL s (D.substS γ₁ γ₂)
  | zeroL s => zeroL s
  | topR s => topR s
  | botR s D => botR s (D.substS γ₁ γ₂)
  | botL => botL
  | negR s D => negR s (D.substS γ₁ γ₂)
  | negL s D => negL s (D.substS γ₁ γ₂)
  | tensorR s s₁ s₂ D₁ D₂ => tensorR s s₁ s₂ (D₁.substS γ₁ γ₂) (D₂.substS γ₁ γ₂)
  | tensorL s D => tensorL s (D.substS γ₁ γ₂)
  | plusR₁ s D => plusR₁ s (D.substS γ₁ γ₂)
  | plusR₂ s D => plusR₂ s (D.substS γ₁ γ₂)
  | plusL s D₁ D₂ => plusL s (D₁.substS γ₁ γ₂) (D₂.substS γ₁ γ₂)
  | withR s D₁ D₂ => withR s (D₁.substS γ₁ γ₂) (D₂.substS γ₁ γ₂)
  | withL₁ s D => withL₁ s (D.substS γ₁ γ₂)
  | withL₂ s D => withL₂ s (D.substS γ₁ γ₂)
  | parR s D => parR s (D.substS γ₁ γ₂)
  | parL s s₁ s₂ D₁ D₂ => parL s s₁ s₂ (D₁.substS γ₁ γ₂) (D₂.substS γ₁ γ₂)
  | bangR D => bangR (D.substS γ₁ γ₂)
  | bangL s D => bangL s (D.substS γ₁.lift γ₂)
  | questR s D => questR s (D.substS γ₁ γ₂.lift)
  | questL D => questL (D.substS γ₁ γ₂)

def Seq.subst (δ₁ : LSubst LHyp Δ₁ Δ₁') (δ₂ : LSubst LHyp Δ₂ Δ₂') : (D : Seq Γ₁ Γ₂ Δ₁ Δ₂) → Seq Γ₁ Γ₂ Δ₁' Δ₂'
  | id => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; id
  | validR v D => validR v (D.subst δ₁ δ₂.lift)
  | validL u D => validL u (D.subst δ₁.lift δ₂)
  | oneR => let .nil := δ₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; oneR
  | oneL s D => let ⟨s, δ₁⟩ := δ₁.split₁' s; oneL s (D.subst δ₁ δ₂)
  | zeroL s => let ⟨s, _⟩ := δ₁.split₁' s; zeroL s
  | topR s => let ⟨s, _⟩ := δ₂.split₁' s; topR s
  | botR s D => let ⟨s, δ₂⟩ := δ₂.split₁' s; botR s (D.subst δ₁ δ₂)
  | botL => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .nil := δ₂; botL
  | negR s D => let ⟨s, δ₂⟩ := δ₂.split₁' s; negR s (D.subst δ₁.lift δ₂)
  | negL s D => let ⟨s, δ₁⟩ := δ₁.split₁' s; negL s (D.subst δ₁ δ₂.lift)
  | tensorR s s₁ s₂ D₁ D₂ => let ⟨s, δ₂⟩ := δ₂.split₁' s; let ⟨s₁, δ₁₁, δ₁₂⟩ := δ₁.split s₁; let ⟨s₂, δ₂₁, δ₂₂⟩ := δ₂.split s₂; tensorR s s₁ s₂ (D₁.subst δ₁₁ δ₂₁.lift) (D₂.subst δ₁₂ δ₂₂.lift)
  | tensorL s D => let ⟨s, δ₁⟩ := δ₁.split₁' s; tensorL s (D.subst δ₁.lift.lift δ₂)
  | plusR₁ s D => let ⟨s, δ₂⟩ := δ₂.split₁' s; plusR₁ s (D.subst δ₁ δ₂.lift)
  | plusR₂ s D => let ⟨s, δ₂⟩ := δ₂.split₁' s; plusR₂ s (D.subst δ₁ δ₂.lift)
  | plusL s D₁ D₂ => let ⟨s, δ₁⟩ := δ₁.split₁' s; plusL s (D₁.subst δ₁.lift δ₂) (D₂.subst δ₁.lift δ₂)
  | withR s D₁ D₂ => let ⟨s, δ₂⟩ := δ₂.split₁' s; withR s (D₁.subst δ₁ δ₂.lift) (D₂.subst δ₁ δ₂.lift)
  | withL₁ s D => let ⟨s, δ₁⟩ := δ₁.split₁' s; withL₁ s (D.subst δ₁.lift δ₂)
  | withL₂ s D => let ⟨s, δ₁⟩ := δ₁.split₁' s; withL₂ s (D.subst δ₁.lift δ₂)
  | parR s D => let ⟨s, δ₂⟩ := δ₂.split₁' s; parR s (D.subst δ₁ δ₂.lift.lift)
  | parL s s₁ s₂ D₁ D₂ => let ⟨s, δ₁⟩ := δ₁.split₁' s; let ⟨s₁, δ₁₁, δ₁₂⟩ := δ₁.split s₁; let ⟨s₂, δ₂₁, δ₂₂⟩ := δ₂.split s₂; parL s s₁ s₂ (D₁.subst δ₁₁.lift δ₂₁) (D₂.subst δ₁₂.lift δ₂₂)
  | bangR D => let .nil := δ₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; bangR D
  | bangL s D => let ⟨s, δ₁⟩ := δ₁.split₁' s; bangL s (D.subst δ₁ δ₂)
  | questR s D => let ⟨s, δ₂⟩ := δ₂.split₁' s; questR s (D.subst δ₁ δ₂)
  | questL D => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .nil := δ₂; questL D

def Seq.id' : ∀ {A}, Seq Γ₁ Γ₂ (.cons .nil A) (.cons .nil A)
  | .base _ => id
  | .one => oneL .here oneR
  | .zero => zeroL .here
  | .top => topR .here
  | .bot => botR .here botL
  | .neg _ => negR .here (negL (.there .here) id')
  | .tensor .. => tensorL .here (tensorR .here (.cons₂ .triv₁) .nil id' id')
  | .plus .. => plusL .here (plusR₁ .here id') (plusR₂ .here id')
  | .with .. => withR .here (withL₁ .here id') (withL₂ .here id')
  | .par .. => parR .here (parL .here .nil (.cons₂ .triv₁) id' id')
  | .bang _ => bangL .here (bangR (validL .here id'))
  | .quest _ => questR .here (questL (validR .here id'))

@[simp]
def Seq.sizeOf : (D : Seq Γ₁ Γ₂ Δ₁ Δ₂) → Nat
  | id | oneR | zeroL _ | topR _ | botL => 0
  | validR _ D | validL _ D | oneL _ D | botR _ D | negR _ D | negL _ D | tensorL _ D | plusR₁ _ D | plusR₂ _ D | withL₁ _ D | withL₂ _ D | parR _ D | bangR D | bangL _ D | questR _ D | questL D => D.sizeOf + 1
  | tensorR _ _ _ D₁ D₂ | plusL _ D₁ D₂ | withR _ D₁ D₂ | parL _ _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_substS (γ₁ : SSubst SHyp Γ₁ Γ₁') (γ₂ : SSubst SHyp Γ₂ Γ₂') (D : Seq Γ₁ Γ₂ Δ₁ Δ₂) : (D.substS γ₁ γ₂).sizeOf = D.sizeOf :=
  by induction D generalizing Γ₁' Γ₂' <;> simp! only [*]

@[simp]
theorem Seq.sizeOf_subst (δ₁ : LSubst LHyp Δ₁ Δ₁') (δ₂ : LSubst LHyp Δ₂ Δ₂') (D : Seq Γ₁ Γ₂ Δ₁ Δ₂) : (D.subst δ₁ δ₂).sizeOf = D.sizeOf := by
  induction D generalizing Δ₁' Δ₂' <;> simp! only [*]
  case id => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; rfl
  case oneR => let .nil := δ₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; rfl
  case botL => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .nil := δ₂; rfl
  case bangR => let .nil := δ₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; rfl
  case questL => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .nil := δ₂; rfl

mutual

set_option maxHeartbeats 800000

def Seq.cut (s₁ : Split Δ₁ Δ₁₁ Δ₁₂) (s₂ : Split Δ₂ Δ₂₁ Δ₂₂) : (D : Seq Γ₁ Γ₂ Δ₁₁ (Δ₂₁.cons A)) → (E : Seq Γ₁ Γ₂ (Δ₁₂.cons A) Δ₂₂) → Seq Γ₁ Γ₂ Δ₁ Δ₂
  | id, id => let .refl _ := s₁.eq_triv₁; let .refl _ := s₂.eq_triv₂; id

  | oneR, oneL .here E => let .refl _ := s₁.eq_triv₂; let .refl _ := s₂.eq_triv₂; E
  | botR .here D, botL => let .refl _ := s₁.eq_triv₁; let .refl _ := s₂.eq_triv₁; D
  | negR .here D, negL .here E => cut s₁.flip s₂.flip E D
  | tensorR .here s₁' s₂' D₁ D₂, tensorL .here E => let ⟨s₁, s₁'⟩ := s₁.shift s₁'; let ⟨s₂, s₂'⟩ := s₂.shift s₂'; cut s₁ s₂ D₁ (cut s₁'.cons₂ s₂' D₂ E)
  | plusR₁ .here D, plusL .here E₁ _ => cut s₁ s₂ D E₁
  | plusR₂ .here D, plusL .here _ E₂ => cut s₁ s₂ D E₂
  | withR .here D₁ _, withL₁ .here E => cut s₁ s₂ D₁ E
  | withR .here _ D₂, withL₂ .here E => cut s₁ s₂ D₂ E
  | parR .here D, parL .here s₁' s₂' E₁ E₂ => let ⟨s₁, s₁'⟩ := s₁.flip.shift s₁'; let ⟨s₂, s₂'⟩ := s₂.flip.shift s₂'; cut s₁.flip s₂.flip (cut s₁'.flip s₂'.flip.cons₁ D E₂) E₁
  | bangR D, bangL .here E => let .refl _ := s₁.eq_triv₂; let .refl _ := s₂.eq_triv₂; cut! D E
  | questR .here D, questL E => let .refl _ := s₁.eq_triv₁; let .refl _ := s₂.eq_triv₁; cut? D E

  | validR v D, E => validR v (cut s₁ s₂.cons₁ (D.subst .id .exchange) E)
  | validL u D, E => validL u (cut s₁.cons₁ s₂ D E)
  | oneL s D, E => let ⟨s, s₁⟩ := s₁.shift₁ s; oneL s (cut s₁ s₂ D E)
  | zeroL s, _ => let ⟨s, _⟩ := s₁.shift₁ s; zeroL s
  | topR (.there s), _ => let ⟨s, _⟩ := s₂.shift₁ s; topR s
  | botR (.there s) D, E => let ⟨s, s₂⟩ := s₂.shift₁ s; botR s (cut s₁ s₂ D E)
  | negR (.there s) D, E => let ⟨s, s₂⟩ := s₂.shift₁ s; negR s (cut s₁.cons₁ s₂ D E)
  | negL s D, E => let ⟨s, s₁⟩ := s₁.shift₁ s; negL s (cut s₁ s₂.cons₁ (D.subst .id .exchange) E)
  | tensorR (.there s) s₁' (.cons₁ s₂') D₁ D₂, E => let ⟨s, s₂⟩ := s₂.shift₁ s; let ⟨s₁', s₁⟩ := s₁.shift s₁'.flip; let ⟨s₂', s₂⟩ := s₂.shift s₂'.flip; tensorR s s₁'.flip s₂'.flip (cut s₁ s₂.cons₁ (D₁.subst .id .exchange) E) D₂
  | tensorR (.there s) s₁' (.cons₂ s₂') D₁ D₂, E => let ⟨s, s₂⟩ := s₂.shift₁ s; let ⟨s₁', s₁⟩ := s₁.shift s₁'; let ⟨s₂', s₂⟩ := s₂.shift s₂'; tensorR s s₁' s₂' D₁ (cut s₁ s₂.cons₁ (D₂.subst .id .exchange) E)
  | tensorL s D, E => let ⟨s, s₁⟩ := s₁.shift₁ s; tensorL s (cut s₁.cons₁.cons₁ s₂ D E)
  | plusR₁ (.there s) D, E => let ⟨s, s₂⟩ := s₂.shift₁ s; plusR₁ s (cut s₁ s₂.cons₁ (D.subst .id .exchange) E)
  | plusR₂ (.there s) D, E => let ⟨s, s₂⟩ := s₂.shift₁ s; plusR₂ s (cut s₁ s₂.cons₁ (D.subst .id .exchange) E)
  | plusL s D₁ D₂, E => let ⟨s, s₁⟩ := s₁.shift₁ s; plusL s (cut s₁.cons₁ s₂ D₁ E) (cut s₁.cons₁ s₂ D₂ E)
  | withR (.there s) D₁ D₂, E => let ⟨s, s₂⟩ := s₂.shift₁ s; withR s (cut s₁ s₂.cons₁ (D₁.subst .id .exchange) E) (cut s₁ s₂.cons₁ (D₂.subst .id .exchange) E)
  | withL₁ s D, E => let ⟨s, s₁⟩ := s₁.shift₁ s; withL₁ s (cut s₁.cons₁ s₂ D E)
  | withL₂ s D, E => let ⟨s, s₁⟩ := s₁.shift₁ s; withL₂ s (cut s₁.cons₁ s₂ D E)
  | parR (.there s) D, E => let ⟨s, s₂⟩ := s₂.shift₁ s; parR s (cut s₁ s₂.cons₁.cons₁ (D.subst .id .exchange₂) E)
  | parL s s₁' (.cons₁ s₂') D₁ D₂, E => let ⟨s, s₁⟩ := s₁.shift₁ s; let ⟨s₁', s₁⟩ := s₁.shift s₁'.flip; let ⟨s₂', s₂⟩ := s₂.shift s₂'.flip; parL s s₁'.flip s₂'.flip (cut s₁.cons₁ s₂ D₁ E) D₂
  | parL s s₁' (.cons₂ s₂') D₁ D₂, E => let ⟨s, s₁⟩ := s₁.shift₁ s; let ⟨s₁', s₁⟩ := s₁.shift s₁'; let ⟨s₂', s₂⟩ := s₂.shift s₂'; parL s s₁' s₂' D₁ (cut s₁.cons₁ s₂ D₂ E)
  | bangL s D, E => let ⟨s, s₁⟩ := s₁.shift₁ s; bangL s (cut s₁ s₂ D (E.substS .weakening .id))
  | questR (.there s) D, E => let ⟨s, s₂⟩ := s₂.shift₁ s; questR s (cut s₁ s₂ D (E.substS .id .weakening))

  | D, validR v E => validR v (cut s₁ s₂.cons₂ D E)
  | D, validL u E => validL u (cut s₁.cons₂ s₂ D (E.subst .exchange .id))
  | D, oneL (.there s) E => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; oneL s (cut s₁.flip s₂ D E)
  | _, zeroL (.there s) => let ⟨s, _⟩ := s₁.flip.shift₁ s; zeroL s
  | _, topR s => let ⟨s, _⟩ := s₂.flip.shift₁ s; topR s
  | D, botR s E => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; botR s (cut s₁ s₂.flip D E)
  | D, negR s E => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; negR s (cut s₁.cons₂ s₂.flip D (E.subst .exchange .id))
  | D, negL (.there s) E => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; negL s (cut s₁.flip s₂.cons₂ D E)
  | D, tensorR s (.cons₁ s₁') s₂' E₁ E₂ => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; let ⟨s₁', s₁⟩ := s₁.flip.shift s₁'.flip; let ⟨s₂', s₂⟩ := s₂.shift s₂'.flip; tensorR s s₁'.flip s₂'.flip (cut s₁.flip s₂.flip.cons₂ D E₁) E₂
  | D, tensorR s (.cons₂ s₁') s₂' E₁ E₂ => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; let ⟨s₁', s₁⟩ := s₁.flip.shift s₁'; let ⟨s₂', s₂⟩ := s₂.shift s₂'; tensorR s s₁' s₂' E₁ (cut s₁.flip s₂.flip.cons₂ D E₂)
  | D, tensorL (.there s) E => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; tensorL s (cut s₁.flip.cons₂.cons₂ s₂ D (E.subst .exchange₂ .id))
  | D, plusR₁ s E => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; plusR₁ s (cut s₁ s₂.flip.cons₂ D E)
  | D, plusR₂ s E => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; plusR₂ s (cut s₁ s₂.flip.cons₂ D E)
  | D, plusL (.there s) E₁ E₂ => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; plusL s (cut s₁.flip.cons₂ s₂ D (E₁.subst .exchange .id)) (cut s₁.flip.cons₂ s₂ D (E₂.subst .exchange .id))
  | D, withR s E₁ E₂ => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; withR s (cut s₁ s₂.flip.cons₂ D E₁) (cut s₁ s₂.flip.cons₂ D E₂)
  | D, withL₁ (.there s) E => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; withL₁ s (cut s₁.flip.cons₂ s₂ D (E.subst .exchange .id))
  | D, withL₂ (.there s) E => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; withL₂ s (cut s₁.flip.cons₂ s₂ D (E.subst .exchange .id))
  | D, parR s E => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; parR s (cut s₁ s₂.flip.cons₂.cons₂ D E)
  | D, parL (.there s) (.cons₁ s₁') s₂' E₁ E₂ => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; let ⟨s₁', s₁⟩ := s₁.shift s₁'.flip; let ⟨s₂', s₂⟩ := s₂.flip.shift s₂'.flip; parL s s₁'.flip s₂'.flip (cut s₁.flip.cons₂ s₂.flip D (E₁.subst .exchange .id)) E₂
  | D, parL (.there s) (.cons₂ s₁') s₂' E₁ E₂ => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; let ⟨s₁', s₁⟩ := s₁.shift s₁'; let ⟨s₂', s₂⟩ := s₂.flip.shift s₂'; parL s s₁' s₂' E₁ (cut s₁.flip.cons₂ s₂.flip D (E₂.subst .exchange .id))
  | D, bangL (.there s) E => let ⟨s, s₁⟩ := s₁.flip.shift₁ s; bangL s (cut s₁.flip s₂ (D.substS .weakening .id) E)
  | D, questR s E => let ⟨s, s₂⟩ := s₂.flip.shift₁ s; questR s (cut s₁ s₂.flip (D.substS .id .weakening) E)

  termination_by D E => (A, 0, D.sizeOf, E.sizeOf)

def Seq.cut! : (D : Seq Γ₁ Γ₂ .nil (.cons .nil A)) → (E : Seq (Γ₁.cons A) Γ₂ Δ₁ Δ₂) → Seq Γ₁ Γ₂ Δ₁ Δ₂
  | D, validL .here E => cut .triv₂ .triv₂ D (cut! D E)

  | _, id => id
  | D, validR v E => validR v (cut! D E)
  | D, validL (.there u) E => validL u (cut! D E)
  | _, oneR => oneR
  | D, oneL s E => oneL s (cut! D E)
  | _, zeroL s => zeroL s
  | _, topR s => topR s
  | D, botR s E => botR s (cut! D E)
  | _, botL => botL
  | D, negR s E => negR s (cut! D E)
  | D, negL s E => negL s (cut! D E)
  | D, tensorR s s₁ s₂ E₁ E₂ => tensorR s s₁ s₂ (cut! D E₁) (cut! D E₂)
  | D, tensorL s E => tensorL s (cut! D E)
  | D, plusR₁ s E => plusR₁ s (cut! D E)
  | D, plusR₂ s E => plusR₂ s (cut! D E)
  | D, plusL s E₁ E₂ => plusL s (cut! D E₁) (cut! D E₂)
  | D, withR s E₁ E₂ => withR s (cut! D E₁) (cut! D E₂)
  | D, withL₁ s E => withL₁ s (cut! D E)
  | D, withL₂ s E => withL₂ s (cut! D E)
  | D, parR s E => parR s (cut! D E)
  | D, parL s s₁ s₂ E₁ E₂ => parL s s₁ s₂ (cut! D E₁) (cut! D E₂)
  | D, bangR E => bangR (cut! D E)
  | D, bangL s E => bangL s (cut! (D.substS .weakening .id) (E.substS .exchange .id))
  | D, questR s E => questR s (cut! (D.substS .id .weakening) E)
  | D, questL E => questL (cut! D E)

  termination_by D E => (A, 1, D.sizeOf, E.sizeOf)

def Seq.cut? : (D : Seq Γ₁ (Γ₂.cons A) Δ₁ Δ₂) → (E : Seq Γ₁ Γ₂ (.cons .nil A) .nil) → Seq Γ₁ Γ₂ Δ₁ Δ₂
  | validR .here D, E => cut .triv₁ .triv₁ (cut? D E) E

  | id, _ => id
  | validR (.there v) D, E => validR v (cut? D E)
  | validL u D, E => validL u (cut? D E)
  | oneR, _ => oneR
  | oneL s D, E => oneL s (cut? D E)
  | zeroL s, _ => zeroL s
  | topR s, _ => topR s
  | botR s D, E => botR s (cut? D E)
  | botL, _ => botL
  | negR s D, E => negR s (cut? D E)
  | negL s D, E => negL s (cut? D E)
  | tensorR s s₁ s₂ D₁ D₂, E => tensorR s s₁ s₂ (cut? D₁ E) (cut? D₂ E)
  | tensorL s D, E => tensorL s (cut? D E)
  | plusR₁ s D, E => plusR₁ s (cut? D E)
  | plusR₂ s D, E => plusR₂ s (cut? D E)
  | plusL s D₁ D₂, E => plusL s (cut? D₁ E) (cut? D₂ E)
  | withR s D₁ D₂, E => withR s (cut? D₁ E) (cut? D₂ E)
  | withL₁ s D, E => withL₁ s (cut? D E)
  | withL₂ s D, E => withL₂ s (cut? D E)
  | parR s D, E => parR s (cut? D E)
  | parL s s₁ s₂ D₁ D₂, E => parL s s₁ s₂ (cut? D₁ E) (cut? D₂ E)
  | bangR D, E => bangR (cut? D E)
  | bangL s D, E => bangL s (cut? D (E.substS .weakening .id))
  | questR s D, E => questR s (cut? (D.substS .id .exchange) (E.substS .id .weakening))
  | questL D, E => questL (cut? D E)

  termination_by D E => (A, 1, D.sizeOf, E.sizeOf)

end

end SC
