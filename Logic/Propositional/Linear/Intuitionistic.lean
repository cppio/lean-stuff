import Logic.Propositional.Linear

namespace Logic.Propositional.Linear.Intuitionistic

inductive Propn
  | base (P : BasePropn)
  | one
  | zero
  | top
  | tensor (A B : Propn)
  | plus (A B : Propn)
  | with (A B : Propn)
  | lolli (A B : Propn)

local notation "Ctx" => Ctx (Propn := Propn)

/-! Natural Deduction -/

namespace ND

inductive True : (Δ : Ctx) → (A : Propn) → Type
  | hyp : True (.cons .nil A) A
  | oneI : True .nil .one
  | oneE (s : Split Δ Δ₁ Δ₂) (D : True Δ₁ .one) (D₁ : True Δ₂ C) : True Δ C
  | zeroE (s : Split Δ Δ₁ Δ₂) (D : True Δ₁ .zero) : True Δ C
  | topI : True Δ .top
  | tensorI (s : Split Δ Δ₁ Δ₂) (D₁ : True Δ₁ A) (D₂ : True Δ₂ B) : True Δ (A.tensor B)
  | tensorE (s : Split Δ Δ₁ Δ₂) (D : True Δ₁ (A.tensor B)) (D₁ : True (Δ₂.cons A |>.cons B) C) : True Δ C
  | plusI₁ (D : True Δ A) : True Δ (A.plus B)
  | plusI₂ (D : True Δ B) : True Δ (.plus A B)
  | plusE (s : Split Δ Δ₁ Δ₂) (D : True Δ₁ (A.plus B)) (D₁ : True (Δ₂.cons A) C) (D₂ : True (Δ₂.cons B) C) : True Δ C
  | withI (D₁ : True Δ A) (D₂ : True Δ B) : True Δ (A.with B)
  | withE₁ (D : True Δ (A.with B)) : True Δ A
  | withE₂ (D : True Δ (.with A B)) : True Δ B
  | lolliI (D : True (Δ.cons A) B) : True Δ (A.lolli B)
  | lolliE (s : Split Δ Δ₁ Δ₂) (D : True Δ₁ (A.lolli B)) (D₁ : True Δ₂ A) : True Δ B

instance True.judge : Judge True where
  hyp := hyp

def True.subst (δ : Subst True Δ Δ') : (D : True Δ A) → True Δ' A
  | hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | oneI => let .nil := δ; oneI
  | oneE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; oneE s (D.subst δ₁) (D₁.subst δ₂)
  | zeroE s D => let ⟨s, δ₁, _⟩ := δ.split s; zeroE s (D.subst δ₁)
  | topI => topI
  | tensorI s D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; tensorI s (D₁.subst δ₁) (D₂.subst δ₂)
  | tensorE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; tensorE s (D.subst δ₁) (D₁.subst δ₂.lift.lift)
  | plusI₁ D => plusI₁ (D.subst δ)
  | plusI₂ D => plusI₂ (D.subst δ)
  | plusE s D D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; plusE s (D.subst δ₁) (D₁.subst δ₂.lift) (D₂.subst δ₂.lift)
  | withI D₁ D₂ => withI (D₁.subst δ) (D₂.subst δ)
  | withE₁ D => withE₁ (D.subst δ)
  | withE₂ D => withE₂ (D.subst δ)
  | lolliI D => lolliI (D.subst δ.lift)
  | lolliE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; lolliE s (D.subst δ₁) (D₁.subst δ₂)

end ND

/-! Verifications and Uses -/

namespace VU

mutual

inductive Verif : (Δ : Ctx) → (A : Propn) → Type
  | uv (D : Use Δ (.base P)) : Verif Δ (.base P)
  | oneI : Verif .nil .one
  | oneE (s : Split Δ Δ₁ Δ₂) (D : Use Δ₁ .one) (D₁ : Verif Δ₂ C) : Verif Δ C
  | zeroE (s : Split Δ Δ₁ Δ₂) (D : Use Δ₁ .zero) : Verif Δ C
  | topI : Verif Δ .top
  | tensorI (s : Split Δ Δ₁ Δ₂) (D₁ : Verif Δ₁ A) (D₂ : Verif Δ₂ B) : Verif Δ (A.tensor B)
  | tensorE (s : Split Δ Δ₁ Δ₂) (D : Use Δ₁ (A.tensor B)) (D₁ : Verif (Δ₂.cons A |>.cons B) C) : Verif Δ C
  | plusI₁ (D : Verif Δ A) : Verif Δ (A.plus B)
  | plusI₂ (D : Verif Δ B) : Verif Δ (.plus A B)
  | plusE (s : Split Δ Δ₁ Δ₂) (D : Use Δ₁ (A.plus B)) (D₁ : Verif (Δ₂.cons A) C) (D₂ : Verif (Δ₂.cons B) C) : Verif Δ C
  | withI (D₁ : Verif Δ A) (D₂ : Verif Δ B) : Verif Δ (A.with B)
  | lolliI (D : Verif (Δ.cons A) B) : Verif Δ (A.lolli B)

inductive Use : (Δ : Ctx) → (A : Propn) → Type
  | hyp : Use (.cons .nil A) A
  | withE₁ (D : Use Δ (A.with B)) : Use Δ A
  | withE₂ (D : Use Δ (.with A B)) : Use Δ B
  | lolliE (s : Split Δ Δ₁ Δ₂) (D : Use Δ₁ (A.lolli B)) (D₁ : Verif Δ₂ A) : Use Δ B

end

instance Use.judge : Judge Use where
  hyp := hyp

mutual

def Verif.subst (δ : Subst Use Δ Δ') : (D : Verif Δ A) → Verif Δ' A
  | .uv D => .uv (D.subst δ)
  | .oneI => let .nil := δ; .oneI
  | .oneE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .oneE s (D.subst δ₁) (D₁.subst δ₂)
  | .zeroE s D => let ⟨s, δ₁, _⟩ := δ.split s; .zeroE s (D.subst δ₁)
  | .topI => .topI
  | .tensorI s D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .tensorI s (D₁.subst δ₁) (D₂.subst δ₂)
  | .tensorE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .tensorE s (D.subst δ₁) (D₁.subst δ₂.lift.lift)
  | .plusI₁ D => .plusI₁ (D.subst δ)
  | .plusI₂ D => .plusI₂ (D.subst δ)
  | .plusE s D D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .plusE s (D.subst δ₁) (D₁.subst δ₂.lift) (D₂.subst δ₂.lift)
  | .withI D₁ D₂ => .withI (D₁.subst δ) (D₂.subst δ)
  | .lolliI D => .lolliI (D.subst δ.lift)

def Use.subst (δ : Subst Use Δ Δ') : (D : Use Δ A) → Use Δ' A
  | .hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | .withE₁ D => .withE₁ (D.subst δ)
  | .withE₂ D => .withE₂ (D.subst δ)
  | .lolliE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .lolliE s (D.subst δ₁) (D₁.subst δ₂)

end

def Verif.uv' (D : Use Δ A) : Verif Δ A :=
  match A with
  | .base _ => uv D
  | .one => oneE .triv₁ D oneI
  | .zero => zeroE .triv₁ D
  | .top => topI
  | .tensor .. => tensorE .triv₁ D (tensorI (.cons₂ .triv₁) (uv' .hyp) (uv' .hyp))
  | .plus .. => plusE .triv₁ D (plusI₁ (uv' .hyp)) (plusI₂ (uv' .hyp))
  | .with .. => withI (uv' (.withE₁ D)) (uv' (.withE₂ D))
  | .lolli .. => lolliI (uv' (.lolliE (.cons₂ .triv₁) D (uv' .hyp)))

instance Verif.judge : Judge Verif where
  hyp := uv' .hyp

mutual

def Verif.toTrue : (D : Verif Δ A) → ND.True Δ A
  | .uv D => D.toTrue
  | .oneI => .oneI
  | .oneE s D D₁ => .oneE s D.toTrue D₁.toTrue
  | .zeroE s D => .zeroE s D.toTrue
  | .topI => .topI
  | .tensorI s D₁ D₂ => .tensorI s D₁.toTrue D₂.toTrue
  | .tensorE s D D₁ => .tensorE s D.toTrue D₁.toTrue
  | .plusI₁ D => .plusI₁ D.toTrue
  | .plusI₂ D => .plusI₂ D.toTrue
  | .plusE s D D₁ D₂ => .plusE s D.toTrue D₁.toTrue D₂.toTrue
  | .withI D₁ D₂ => .withI D₁.toTrue D₂.toTrue
  | .lolliI D => .lolliI D.toTrue

def Use.toTrue : (D : Use Δ A) → ND.True Δ A
  | .hyp => .hyp
  | .withE₁ D => .withE₁ D.toTrue
  | .withE₂ D => .withE₂ D.toTrue
  | .lolliE s D D₁ => .lolliE s D.toTrue D₁.toTrue

end

end VU

/-! Sequent Calculus -/

inductive SC.Seq : (Δ : Ctx) → (A : Propn) → Type
  | id : Seq (.cons .nil (.base P)) (.base P)
  | oneR : Seq .nil .one
  | oneL (s : Split₁ Δ .one Δ') (D : Seq Δ' C) : Seq Δ C
  | zeroL (s : Split₁ Δ .zero Δ') : Seq Δ C
  | topR : Seq Δ .top
  | tensorR (s : Split Δ Δ₁ Δ₂) (D₁ : Seq Δ₁ A) (D₂ : Seq Δ₂ B) : Seq Δ (A.tensor B)
  | tensorL (s : Split₁ Δ (A.tensor B) Δ') (D : Seq (Δ'.cons A |>.cons B) C) : Seq Δ C
  | plusR₁ (D : Seq Δ A) : Seq Δ (A.plus B)
  | plusR₂ (D : Seq Δ B) : Seq Δ (.plus A B)
  | plusL (s : Split₁ Δ (A.plus B) Δ') (D₁ : Seq (Δ'.cons A) C) (D₂ : Seq (Δ'.cons B) C) : Seq Δ C
  | withR (D₁ : Seq Δ A) (D₂ : Seq Δ B) : Seq Δ (A.with B)
  | withL₁ (s : Split₁ Δ (A.with B) Δ') (D : Seq (Δ'.cons A) C) : Seq Δ C
  | withL₂ (s : Split₁ Δ (.with A B) Δ') (D : Seq (Δ'.cons B) C) : Seq Δ C
  | lolliR (D : Seq (Δ.cons A) B) : Seq Δ (A.lolli B)
  | lolliL (s : Split₁ Δ (A.lolli B) Δ') (s' : Split Δ' Δ₁ Δ₂) (D₁ : Seq Δ₁ A) (D₂ : Seq (Δ₂.cons B) C) : Seq Δ C

class SCJudge (J) extends Judge J where
  cut (s : Split Δ Δ₁ Δ₂) (D' : J Δ₁ A) (D : ∀ {Δ}, (s : Split₁ Δ A Δ₂) → SC.Seq Δ C) : SC.Seq Δ C

instance Hyp.scJudge : SCJudge Hyp where
  cut s D' D := D (let .mk := D'; .ofSplit s)

namespace SC

def Seq.subst [j : SCJudge J] (δ : Subst J Δ Δ') : (D : Seq Δ A) → Seq Δ' A
  | id => let .cons s D' .nil := δ; j.cut s D' fun | .here => id
  | oneR => let .nil := δ; oneR
  | oneL s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => oneL s (D.subst δ)
  | zeroL s => let ⟨s, D', _⟩ := δ.split₁ s; j.cut s D' zeroL
  | topR => topR
  | tensorR s D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; tensorR s (D₁.subst δ₁) (D₂.subst δ₂)
  | tensorL s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => tensorL s (D.subst δ.lift.lift)
  | plusR₁ D => plusR₁ (D.subst δ)
  | plusR₂ D => plusR₂ (D.subst δ)
  | plusL s D₁ D₂ => let ⟨s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => plusL s (D₁.subst δ.lift) (D₂.subst δ.lift)
  | withR D₁ D₂ => withR (D₁.subst δ) (D₂.subst δ)
  | withL₁ s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => withL₁ s (D.subst δ.lift)
  | withL₂ s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => withL₂ s (D.subst δ.lift)
  | lolliR D => lolliR (D.subst δ.lift)
  | lolliL s s' D₁ D₂ => let ⟨s, D', δ⟩ := δ.split₁ s; let ⟨s', δ₁, δ₂⟩ := δ.split s'; j.cut s D' fun s => lolliL s s' (D₁.subst δ₁) (D₂.subst δ₂.lift)

def Seq.id' : ∀ {A}, Seq (.cons .nil A) A
  | .base _ => id
  | .one => oneL .here oneR
  | .zero => zeroL .here
  | .top => topR
  | .tensor .. => tensorL .here (tensorR (.cons₂ .triv₁) id' id')
  | .plus .. => plusL .here (plusR₁ id') (plusR₂ id')
  | .with .. => withR (withL₁ .here id') (withL₂ .here id')
  | .lolli .. => lolliR (lolliL (.there .here) .triv₁ id' id')

@[simp]
def Seq.sizeOf : (D : Seq Δ A) → Nat
  | id | oneR | zeroL _ | topR => 0
  | oneL _ D | tensorL _ D | plusR₁ D | plusR₂ D | withL₁ _ D | withL₂ _ D | lolliR D => D.sizeOf + 1
  | tensorR _ D₁ D₂ | plusL _ D₁ D₂ | withR D₁ D₂ | lolliL _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_subst (δ : Subst Hyp Δ Δ') (D : Seq Δ A) : (D.subst δ).sizeOf = D.sizeOf := by
  induction D generalizing Δ' <;> simp! only [*]
  case id => let .cons s .mk .nil := δ; let .refl _ := s.eq_triv₁; rfl
  case oneR => let .nil := δ; rfl

def Seq.cut (s : Split Δ Δ₁ Δ₂) : (D : Seq Δ₁ A) → (E : Seq (Δ₂.cons A) C) → Seq Δ C
  | D, id => let .refl _ := s.eq_triv₁; D
  | oneR, oneL .here E => let .refl _ := s.eq_triv₂; E
  | tensorR s' D₁ D₂, tensorL .here E => let ⟨s, s'⟩ := s.shift s'; cut s D₁ (cut s'.cons₂ D₂ E)
  | plusR₁ D, plusL .here E₁ _ => cut s D E₁
  | plusR₂ D, plusL .here _ E₂ => cut s D E₂
  | withR D₁ _, withL₁ .here E => cut s D₁ E
  | withR _ D₂, withL₂ .here E => cut s D₂ E
  | lolliR D, lolliL .here s₂ E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift s₂.flip; cut s.flip (cut s' E₁ D) E₂
  | oneL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; oneL s (cut s' D E)
  | zeroL s', _ => let ⟨s, _⟩ := s.shift₁ s'; zeroL s
  | tensorL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; tensorL s (cut s'.cons₁.cons₁ D E)
  | plusL s' D₁ D₂, E => let ⟨s, s'⟩ := s.shift₁ s'; plusL s (cut s'.cons₁ D₁ E) (cut s'.cons₁ D₂ E)
  | withL₁ s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; withL₁ s (cut s'.cons₁ D E)
  | withL₂ s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; withL₂ s (cut s'.cons₁ D E)
  | lolliL s' s'' D₁ D₂, E => let ⟨s, s'⟩ := s.shift₁ s'; let ⟨s', s''⟩ := s'.shift s''; lolliL s s' D₁ (cut s''.cons₁ D₂ E)
  | D, oneL (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; oneL s (cut s'.flip D E)
  | _, zeroL (.there s') => let ⟨s, _⟩ := s.flip.shift₁ s'; zeroL s
  | _, topR => topR
  | D, tensorR (.cons₁ s') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift s'.flip; tensorR s.flip (cut s'.flip D E₁) E₂
  | D, tensorR (.cons₂ s') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift s'; tensorR s E₁ (cut s'.flip D E₂)
  | D, tensorL (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; tensorL s (cut s'.flip.cons₂.cons₂ D (E.subst .exchange₂))
  | D, plusR₁ E => plusR₁ (cut s D E)
  | D, plusR₂ E => plusR₂ (cut s D E)
  | D, plusL (.there s') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift₁ s'; plusL s (cut s'.flip.cons₂ D (E₁.subst .exchange)) (cut s'.flip.cons₂ D (E₂.subst .exchange))
  | D, withR E₁ E₂ => withR (cut s D E₁) (cut s D E₂)
  | D, withL₁ (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; withL₁ s (cut s'.flip.cons₂ D (E.subst .exchange))
  | D, withL₂ (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; withL₂ s (cut s'.flip.cons₂ D (E.subst .exchange))
  | D, lolliR E => lolliR (cut s.cons₂ D (E.subst .exchange))
  | D, lolliL (.there s') (.cons₁ s'') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift₁ s'; let ⟨s', s''⟩ := s'.shift s''.flip; lolliL s s'.flip (cut s''.flip D E₁) E₂
  | D, lolliL (.there s') (.cons₂ s'') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift₁ s'; let ⟨s', s''⟩ := s'.shift s''; lolliL s s' E₁ (cut s''.flip.cons₂ D (E₂.subst .exchange))
  termination_by D E => (A, D.sizeOf, E.sizeOf)

instance Seq.scJudge : SCJudge Seq where
  hyp := id'
  cut s D' D := cut s D' (D .here)

def Seq.toVerif : (D : Seq Δ A) → VU.Verif Δ A
  | id => .uv .hyp
  | oneR => .oneI
  | oneL s D => .oneE s.toSplit .hyp D.toVerif
  | zeroL s => .zeroE s.toSplit .hyp
  | topR => .topI
  | tensorR s D₁ D₂ => .tensorI s D₁.toVerif D₂.toVerif
  | tensorL s D => .tensorE s.toSplit .hyp D.toVerif
  | plusR₁ D => .plusI₁ D.toVerif
  | plusR₂ D => .plusI₂ D.toVerif
  | plusL s D₁ D₂ => .plusE s.toSplit .hyp D₁.toVerif D₂.toVerif
  | withR D₁ D₂ => .withI D₁.toVerif D₂.toVerif
  | withL₁ s D => D.toVerif.subst (.cons s.toSplit (VU.Use.withE₁ .hyp) .id)
  | withL₂ s D => D.toVerif.subst (.cons s.toSplit (VU.Use.withE₂ .hyp) .id)
  | lolliR D => .lolliI D.toVerif
  | lolliL s s' D₁ D₂ => let ⟨s, s'⟩ := s.toSplit.flip.shift s'.flip; D₂.toVerif.subst (.cons s.flip (VU.Use.lolliE s'.flip .hyp D₁.toVerif) .id)

end SC

def ND.True.toSeq : (D : True Δ A) → SC.Seq Δ A
  | hyp => .id'
  | oneI => .oneR
  | oneE s D D₁ => .cut s D.toSeq (.oneL .here D₁.toSeq)
  | zeroE s D => .cut s D.toSeq (.zeroL .here)
  | topI => .topR
  | tensorI s D₁ D₂ => .tensorR s D₁.toSeq D₂.toSeq
  | tensorE s D D₁ => .cut s D.toSeq (.tensorL .here D₁.toSeq)
  | plusI₁ D => .plusR₁ D.toSeq
  | plusI₂ D => .plusR₂ D.toSeq
  | plusE s D D₁ D₂ => .cut s D.toSeq (.plusL .here D₁.toSeq D₂.toSeq)
  | withI D₁ D₂ => .withR D₁.toSeq D₂.toSeq
  | withE₁ D => .cut .triv₁ D.toSeq (.withL₁ .here .id')
  | withE₂ D => .cut .triv₁ D.toSeq (.withL₂ .here .id')
  | lolliI D => .lolliR D.toSeq
  | lolliE s D D₁ => .cut s D.toSeq (.lolliL .here .triv₁ D₁.toSeq .id')

def VU.Verif.subst' (δ : Subst Verif Δ Δ') (D : Verif Δ A) : Verif Δ' A :=
  (D.toTrue.toSeq.subst (δ.map fun D => D.toTrue.toSeq)).toVerif
