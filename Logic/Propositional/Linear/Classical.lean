import Logic.Propositional.Linear

namespace Logic.Propositional.Linear.Intuitionistic

opaque BasePropn : Type

inductive Propn
  | base (P : BasePropn)
  | one
  | zero
  | top
  | bot
  | neg (A : Propn)
  | tensor (A B : Propn)
  | plus (A B : Propn)
  | with (A B : Propn)
  | par (A B : Propn)

local notation "Ctx" => Ctx (Propn := Propn)

/-! Sequent Calculus -/

namespace SC

inductive Seq : (Δ₁ Δ₂ : Ctx) → Type
  | id : Seq (.cons .nil (.base P)) (.cons .nil (.base P))
  | oneR : Seq .nil (.cons .nil .one)
  | oneL (s : Split₁ Δ₁ .one Δ₁') (D : Seq Δ₁' Δ₂) : Seq Δ₁ Δ₂
  | zeroL (s : Split₁ Δ₁ .zero Δ₁') : Seq Δ₁ Δ₂
  | topR (s : Split₁ Δ₂ .top Δ₂') : Seq Δ₁ Δ₂
  | botR (s : Split₁ Δ₂ .bot Δ₂') (D : Seq Δ₁ Δ₂') : Seq Δ₁ Δ₂
  | botL : Seq (.cons .nil .bot) .nil
  | negR (s : Split₁ Δ₂ A.neg Δ₂') (D : Seq (Δ₁.cons A) Δ₂') : Seq Δ₁ Δ₂
  | negL (s : Split₁ Δ₁ A.neg Δ₁') (D : Seq Δ₁' (Δ₂.cons A)) : Seq Δ₁ Δ₂
  | tensorR (s : Split₁ Δ₂ (A.tensor B) Δ₂') (s₁ : Split Δ₁ Δ₁₁ Δ₁₂) (s₂ : Split Δ₂' Δ₂₁' Δ₂₂') (D₁ : Seq Δ₁₁ (Δ₂₁'.cons A)) (D₂ : Seq Δ₁₂ (Δ₂₂'.cons B)) : Seq Δ₁ Δ₂
  | tensorL (s : Split₁ Δ₁ (A.tensor B) Δ₁') (D : Seq (Δ₁'.cons A |>.cons B) Δ₂) : Seq Δ₁ Δ₂
  | plusR₁ (s : Split₁ Δ₂ (A.plus B) Δ₂') (D : Seq Δ₁ (Δ₂'.cons A)) : Seq Δ₁ Δ₂
  | plusR₂ (s : Split₁ Δ₂ (.plus A B) Δ₂') (D : Seq Δ₁ (Δ₂'.cons B)) : Seq Δ₁ Δ₂
  | plusL (s : Split₁ Δ₁ (A.plus B) Δ₁') (D₁ : Seq (Δ₁'.cons A) Δ₂) (D₂ : Seq (Δ₁'.cons B) Δ₂) : Seq Δ₁ Δ₂
  | withR (s : Split₁ Δ₂ (A.with B) Δ₂') (D₁ : Seq Δ₁ (Δ₂'.cons A)) (D₂ : Seq Δ₁ (Δ₂'.cons B)) : Seq Δ₁ Δ₂
  | withL₁ (s : Split₁ Δ₁ (A.with B) Δ₁') (D : Seq (Δ₁'.cons A) Δ₂) : Seq Δ₁ Δ₂
  | withL₂ (s : Split₁ Δ₁ (.with A B) Δ₁') (D : Seq (Δ₁'.cons B) Δ₂) : Seq Δ₁ Δ₂
  | parR (s : Split₁ Δ₂ (A.par B) Δ₂') (D : Seq Δ₁ (Δ₂'.cons A |>.cons B)) : Seq Δ₁ Δ₂
  | parL (s : Split₁ Δ₁ (A.par B) Δ₁') (s₁ : Split Δ₁' Δ₁₁' Δ₁₂') (s₂ : Split Δ₂ Δ₂₁ Δ₂₂) (D₁ : Seq (Δ₁₁'.cons A) Δ₂₁) (D₂ : Seq (Δ₁₂'.cons B) Δ₂₂) : Seq Δ₁ Δ₂

def Seq.subst (δ₁ : Subst Hyp Δ₁ Δ₁') (δ₂ : Subst Hyp Δ₂ Δ₂') : (D : Seq Δ₁ Δ₂) → Seq Δ₁' Δ₂'
  | id => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; id
  | oneR => let .nil := δ₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; oneR
  | oneL s D => let ⟨_, s, δ₁⟩ := δ₁.split₁' s; oneL (.ofSplit s) (D.subst δ₁ δ₂)
  | zeroL s => let ⟨_, s, _⟩ := δ₁.split₁' s; zeroL (.ofSplit s)
  | topR s => let ⟨_, s, _⟩ := δ₂.split₁' s; topR (.ofSplit s)
  | botR s D => let ⟨_, s, δ₂⟩ := δ₂.split₁' s; botR (.ofSplit s) (D.subst δ₁ δ₂)
  | botL => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .nil := δ₂; botL
  | negR s D => let ⟨_, s, δ₂⟩ := δ₂.split₁' s; negR (.ofSplit s) (D.subst δ₁.lift δ₂)
  | negL s D => let ⟨_, s, δ₁⟩ := δ₁.split₁' s; negL (.ofSplit s) (D.subst δ₁ δ₂.lift)
  | tensorR s s₁ s₂ D₁ D₂ => let ⟨_, s, δ₂⟩ := δ₂.split₁' s; let ⟨_, _, s₁, δ₁₁, δ₁₂⟩ := δ₁.split s₁; let ⟨_, _, s₂, δ₂₁, δ₂₂⟩ := δ₂.split s₂; tensorR (.ofSplit s) s₁ s₂ (D₁.subst δ₁₁ δ₂₁.lift) (D₂.subst δ₁₂ δ₂₂.lift)
  | tensorL s D => let ⟨_, s, δ₁⟩ := δ₁.split₁' s; tensorL (.ofSplit s) (D.subst δ₁.lift.lift δ₂)
  | plusR₁ s D => let ⟨_, s, δ₂⟩ := δ₂.split₁' s; plusR₁ (.ofSplit s) (D.subst δ₁ δ₂.lift)
  | plusR₂ s D => let ⟨_, s, δ₂⟩ := δ₂.split₁' s; plusR₂ (.ofSplit s) (D.subst δ₁ δ₂.lift)
  | plusL s D₁ D₂ => let ⟨_, s, δ₁⟩ := δ₁.split₁' s; plusL (.ofSplit s) (D₁.subst δ₁.lift δ₂) (D₂.subst δ₁.lift δ₂)
  | withR s D₁ D₂ => let ⟨_, s, δ₂⟩ := δ₂.split₁' s; withR (.ofSplit s) (D₁.subst δ₁ δ₂.lift) (D₂.subst δ₁ δ₂.lift)
  | withL₁ s D => let ⟨_, s, δ₁⟩ := δ₁.split₁' s; withL₁ (.ofSplit s) (D.subst δ₁.lift δ₂)
  | withL₂ s D => let ⟨_, s, δ₁⟩ := δ₁.split₁' s; withL₂ (.ofSplit s) (D.subst δ₁.lift δ₂)
  | parR s D => let ⟨_, s, δ₂⟩ := δ₂.split₁' s; parR (.ofSplit s) (D.subst δ₁ δ₂.lift.lift)
  | parL s s₁ s₂ D₁ D₂ => let ⟨_, s, δ₁⟩ := δ₁.split₁' s; let ⟨_, _, s₁, δ₁₁, δ₁₂⟩ := δ₁.split s₁; let ⟨_, _, s₂, δ₂₁, δ₂₂⟩ := δ₂.split s₂; parL (.ofSplit s) s₁ s₂ (D₁.subst δ₁₁.lift δ₂₁) (D₂.subst δ₁₂.lift δ₂₂)

def Seq.id' : ∀ {A}, Seq (.cons .nil A) (.cons .nil A)
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

@[simp]
def Seq.sizeOf : (D : Seq Δ₁ Δ₂) → Nat
  | id | oneR | zeroL _ | topR _ | botL => 0
  | oneL _ D | botR _ D | negR _ D | negL _ D | tensorL _ D | plusR₁ _ D | plusR₂ _ D | withL₁ _ D | withL₂ _ D | parR _ D => D.sizeOf + 1
  | tensorR _ _ _ D₁ D₂ | plusL _ D₁ D₂ | withR _ D₁ D₂ | parL _ _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_subst (δ₁ : Subst Hyp Δ₁ Δ₁') (δ₂ : Subst Hyp Δ₂ Δ₂') (D : Seq Δ₁ Δ₂) : (D.subst δ₁ δ₂).sizeOf = D.sizeOf := by
  induction D generalizing Δ₁' Δ₂' <;> simp! only [*]
  case id => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; rfl
  case oneR => let .nil := δ₁; let .cons s .mk .nil := δ₂; let .refl _ := s.eq_triv₁; rfl
  case botL => let .cons s .mk .nil := δ₁; let .refl _ := s.eq_triv₁; let .nil := δ₂; rfl

set_option maxHeartbeats 300000 in
def Seq.cut (s₁ : Split Δ₁ Δ₁₁ Δ₁₂) (s₂ : Split Δ₂ Δ₂₁ Δ₂₂) : (D : Seq Δ₁₁ (Δ₂₁.cons A)) → (E : Seq (Δ₁₂.cons A) Δ₂₂) → Seq Δ₁ Δ₂
  | id, id => let .refl _ := s₁.eq_triv₁; let .refl _ := s₂.eq_triv₂; id
  | oneR, oneL .here E => let .refl _ := s₁.eq_triv₂; let .refl _ := s₂.eq_triv₂; E
  | botR .here D, botL => let .refl _ := s₁.eq_triv₁; let .refl _ := s₂.eq_triv₁; D
  | negR .here D, negL .here E => cut s₁.flip s₂.flip E D
  | tensorR .here s₁' s₂' D₁ D₂, tensorL .here E => let ⟨_, s₁, s₁'⟩ := s₁.shift s₁'; let ⟨_, s₂, s₂'⟩ := s₂.shift s₂'; cut s₁ s₂ D₁ (cut s₁'.cons₂ s₂' D₂ E)
  | plusR₁ .here D, plusL .here E₁ _ => cut s₁ s₂ D E₁
  | plusR₂ .here D, plusL .here _ E₂ => cut s₁ s₂ D E₂
  | withR .here D₁ _, withL₁ .here E => cut s₁ s₂ D₁ E
  | withR .here _ D₂, withL₂ .here E => cut s₁ s₂ D₂ E
  | parR .here D, parL .here s₁' s₂' E₁ E₂ => let ⟨_, s₁, s₁'⟩ := s₁.flip.shift s₁'; let ⟨_, s₂, s₂'⟩ := s₂.flip.shift s₂'; cut s₁.flip s₂.flip (cut s₁'.flip s₂'.flip.cons₁ D E₂) E₁
  | oneL s D, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; oneL s (cut s₁ s₂ D E)
  | zeroL s, _ => let ⟨_, s, _⟩ := s₁.shift₁ s; zeroL s
  | topR (.there s), _ => let ⟨_, s, _⟩ := s₂.shift₁ s; topR s
  | botR (.there s) D, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; botR s (cut s₁ s₂ D E)
  | negR (.there s) D, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; negR s (cut s₁.cons₁ s₂ D E)
  | negL s D, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; negL s (cut s₁ s₂.cons₁ (D.subst .id .exchange) E)
  | tensorR (.there s) s₁' (.cons₁ s₂') D₁ D₂, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.shift s₁'.flip; let ⟨_, s₂', s₂⟩ := s₂.shift s₂'.flip; tensorR s s₁'.flip s₂'.flip (cut s₁ s₂.cons₁ (D₁.subst .id .exchange) E) D₂
  | tensorR (.there s) s₁' (.cons₂ s₂') D₁ D₂, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.shift s₁'; let ⟨_, s₂', s₂⟩ := s₂.shift s₂'; tensorR s s₁' s₂' D₁ (cut s₁ s₂.cons₁ (D₂.subst .id .exchange) E)
  | tensorL s D, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; tensorL s (cut s₁.cons₁.cons₁ s₂ D E)
  | plusR₁ (.there s) D, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; plusR₁ s (cut s₁ s₂.cons₁ (D.subst .id .exchange) E)
  | plusR₂ (.there s) D, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; plusR₂ s (cut s₁ s₂.cons₁ (D.subst .id .exchange) E)
  | plusL s D₁ D₂, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; plusL s (cut s₁.cons₁ s₂ D₁ E) (cut s₁.cons₁ s₂ D₂ E)
  | withR (.there s) D₁ D₂, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; withR s (cut s₁ s₂.cons₁ (D₁.subst .id .exchange) E) (cut s₁ s₂.cons₁ (D₂.subst .id .exchange) E)
  | withL₁ s D, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; withL₁ s (cut s₁.cons₁ s₂ D E)
  | withL₂ s D, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; withL₂ s (cut s₁.cons₁ s₂ D E)
  | parR (.there s) D, E => let ⟨_, s, s₂⟩ := s₂.shift₁ s; parR s (cut s₁ s₂.cons₁.cons₁ (D.subst .id .exchange₂) E)
  | parL s s₁' (.cons₁ s₂') D₁ D₂, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.shift s₁'.flip; let ⟨_, s₂', s₂⟩ := s₂.shift s₂'.flip; parL s s₁'.flip s₂'.flip (cut s₁.cons₁ s₂ D₁ E) D₂
  | parL s s₁' (.cons₂ s₂') D₁ D₂, E => let ⟨_, s, s₁⟩ := s₁.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.shift s₁'; let ⟨_, s₂', s₂⟩ := s₂.shift s₂'; parL s s₁' s₂' D₁ (cut s₁.cons₁ s₂ D₂ E)
  | D, oneL (.there s) E => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; oneL s (cut s₁.flip s₂ D E)
  | _, zeroL (.there s) => let ⟨_, s, _⟩ := s₁.flip.shift₁ s; zeroL s
  | _, topR s => let ⟨_, s, _⟩ := s₂.flip.shift₁ s; topR s
  | D, botR s E => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; botR s (cut s₁ s₂.flip D E)
  | D, negR s E => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; negR s (cut s₁.cons₂ s₂.flip D (E.subst .exchange .id))
  | D, negL (.there s) E => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; negL s (cut s₁.flip s₂.cons₂ D E)
  | D, tensorR s (.cons₁ s₁') s₂' E₁ E₂ => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.flip.shift s₁'.flip; let ⟨_, s₂', s₂⟩ := s₂.shift s₂'.flip; tensorR s s₁'.flip s₂'.flip (cut s₁.flip s₂.flip.cons₂ D E₁) E₂
  | D, tensorR s (.cons₂ s₁') s₂' E₁ E₂ => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.flip.shift s₁'; let ⟨_, s₂', s₂⟩ := s₂.shift s₂'; tensorR s s₁' s₂' E₁ (cut s₁.flip s₂.flip.cons₂ D E₂)
  | D, tensorL (.there s) E => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; tensorL s (cut s₁.flip.cons₂.cons₂ s₂ D (E.subst .exchange₂ .id))
  | D, plusR₁ s E => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; plusR₁ s (cut s₁ s₂.flip.cons₂ D E)
  | D, plusR₂ s E => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; plusR₂ s (cut s₁ s₂.flip.cons₂ D E)
  | D, plusL (.there s) E₁ E₂ => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; plusL s (cut s₁.flip.cons₂ s₂ D (E₁.subst .exchange .id)) (cut s₁.flip.cons₂ s₂ D (E₂.subst .exchange .id))
  | D, withR s E₁ E₂ => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; withR s (cut s₁ s₂.flip.cons₂ D E₁) (cut s₁ s₂.flip.cons₂ D E₂)
  | D, withL₁ (.there s) E => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; withL₁ s (cut s₁.flip.cons₂ s₂ D (E.subst .exchange .id))
  | D, withL₂ (.there s) E => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; withL₂ s (cut s₁.flip.cons₂ s₂ D (E.subst .exchange .id))
  | D, parR s E => let ⟨_, s, s₂⟩ := s₂.flip.shift₁ s; parR s (cut s₁ s₂.flip.cons₂.cons₂ D E)
  | D, parL (.there s) (.cons₁ s₁') s₂' E₁ E₂ => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.shift s₁'.flip; let ⟨_, s₂', s₂⟩ := s₂.flip.shift s₂'.flip; parL s s₁'.flip s₂'.flip (cut s₁.flip.cons₂ s₂.flip D (E₁.subst .exchange .id)) E₂
  | D, parL (.there s) (.cons₂ s₁') s₂' E₁ E₂ => let ⟨_, s, s₁⟩ := s₁.flip.shift₁ s; let ⟨_, s₁', s₁⟩ := s₁.shift s₁'; let ⟨_, s₂', s₂⟩ := s₂.flip.shift s₂'; parL s s₁' s₂' E₁ (cut s₁.flip.cons₂ s₂.flip D (E₂.subst .exchange .id))
  termination_by D E => (A, D.sizeOf, E.sizeOf)

end SC
