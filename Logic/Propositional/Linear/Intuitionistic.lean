opaque BasePropn : Type

inductive Propn
  | base (P : BasePropn)
  | one
  | zero
  | top
  | tensor (A B : Propn)
  | plus (A B : Propn)
  | with (A B : Propn)
  | lolli (A B : Propn)

inductive Ctx
  | nil
  | cons (Δ : Ctx) (A : Propn)

inductive Split : (Δ Δ₁ Δ₂ : Ctx) → Type
  | nil : Split .nil .nil .nil
  | cons₁ (s : Split Δ Δ₁ Δ₂) : Split (Δ.cons A) (Δ₁.cons A) Δ₂
  | cons₂ (s : Split Δ Δ₁ Δ₂) : Split (Δ.cons A) Δ₁ (Δ₂.cons A)

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

def Split.shift₁ : (s : Split Δ Δ₁ Δ₂) → (s₁ : Split Δ₁ Δ₁₁ Δ₁₂) → Σ Δ', Split Δ Δ₁₁ Δ' × Split Δ' Δ₁₂ Δ₂
  | s, nil => ⟨_, triv₂, s⟩
  | cons₁ s, cons₁ s₁ => let ⟨_, s, s'⟩ := s.shift₁ s₁; ⟨_, s.cons₁, s'⟩
  | cons₁ s, cons₂ s₁ => let ⟨_, s, s'⟩ := s.shift₁ s₁; ⟨_, s.cons₂, s'.cons₁⟩
  | cons₂ s, s₁ => let ⟨_, s, s'⟩ := s.shift₁ s₁; ⟨_, s.cons₂, s'.cons₂⟩

inductive Subst (J : (Δ : Ctx) → (A : Propn) → Type) : (Δ Δ' : Ctx) → Type
  | nil : Subst J .nil .nil
  | cons (s : Split Δ' Δ₁ Δ₂) (D : J Δ₁ A) (δ : Subst J Δ Δ₂) : Subst J (Δ.cons A) Δ'

def Subst.split : (δ : Subst J Δ Δ') → ∀ {Δ₁ Δ₂}, (s : Split Δ Δ₁ Δ₂) → Σ Δ₁' Δ₂', Split Δ' Δ₁' Δ₂' × Subst J Δ₁ Δ₁' × Subst J Δ₂ Δ₂'
  | nil, _, _, .nil => ⟨_, _, .nil, nil, nil⟩
  | cons s' D δ, _, _, .cons₁ s => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; let ⟨_, s, s'⟩ := s'.flip.shift₁ s.flip; ⟨_, _, s.flip, cons s'.flip D δ₁, δ₂⟩
  | cons s' D δ, _, _, .cons₂ s => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; let ⟨_, s, s'⟩ := s'.flip.shift₁ s; ⟨_, _, s, δ₁, cons s'.flip D δ₂⟩

inductive Hyp : (Δ : Ctx) → (A : Propn) → Type
  | mk : Hyp (.cons .nil A) A

class Judge (J : (Δ : Ctx) → (A : Propn) → Type) where
  hyp : J (.cons .nil A) A

instance Hyp.judge : Judge Hyp where
  hyp := mk

def Subst.id [j : Judge J] : ∀ {Δ}, Subst J Δ Δ
  | .nil => nil
  | .cons .. => cons (.cons₁ .triv₂) j.hyp id

def Subst.lift [j : Judge J] {Δ Δ' A} : (δ : Subst J Δ Δ') → Subst J (Δ.cons A) (Δ'.cons A) :=
  cons (.cons₁ .triv₂) j.hyp

def Subst.map (f : ∀ {Δ A}, (D : J Δ A) → J' Δ A) {Δ Δ'} : (δ : Subst J Δ Δ') → Subst J' Δ Δ'
  | nil => nil
  | cons s D δ => cons s (f D) (δ.map @f)

def Subst.exchange : Subst Hyp (Ctx.cons Δ A |>.cons B) (Δ.cons B |>.cons A) :=
  cons (.cons₂ (.cons₁ .triv₂)) .mk id

def Subst.exchange₂ : Subst Hyp (Ctx.cons Δ A |>.cons B |>.cons C) (Δ.cons B |>.cons C |>.cons A) :=
  cons (.cons₂ (.cons₁ .triv₂)) .mk exchange

inductive Split₁ : (Δ : Ctx) → (A : Propn) → (Δ' : Ctx) → Type
  | here : Split₁ (Δ.cons A) A Δ
  | there (s : Split₁ Δ A Δ') : Split₁ (Δ.cons B) A (Δ'.cons B)

def Split₁.toSplit : (s : Split₁ Δ A Δ') → Split Δ (.cons .nil A) Δ'
  | here => .cons₁ .triv₂
  | there s => s.toSplit.cons₂

def Split₁.ofSplit : (s : Split Δ (.cons .nil A) Δ') → Split₁ Δ A Δ'
  | .cons₁ s => let .refl _ := s.eq_triv₂; here
  | .cons₂ s => (ofSplit s).there

def Subst.split₁ (δ : Subst J Δ Δ') {A Δ₂} (s : Split₁ Δ A Δ₂) : Σ Δ₁' Δ₂', Split Δ' Δ₁' Δ₂' × J Δ₁' A × Subst J Δ₂ Δ₂' :=
  let ⟨_, _, s, cons s' D nil, δ⟩ := δ.split s.toSplit
  let .refl _ := s'.eq_triv₁
  ⟨_, _, s, D, δ⟩

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

def True.subst (δ : Subst True Δ Δ') {A} : (D : True Δ A) → True Δ' A
  | hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | oneI => let .nil := δ; oneI
  | oneE s D D₁ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; oneE s (D.subst δ₁) (D₁.subst δ₂)
  | zeroE s D => let ⟨_, _, s, δ₁, _⟩ := δ.split s; zeroE s (D.subst δ₁)
  | topI => topI
  | tensorI s D₁ D₂ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; tensorI s (D₁.subst δ₁) (D₂.subst δ₂)
  | tensorE s D D₁ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; tensorE s (D.subst δ₁) (D₁.subst δ₂.lift.lift)
  | plusI₁ D => plusI₁ (D.subst δ)
  | plusI₂ D => plusI₂ (D.subst δ)
  | plusE s D D₁ D₂ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; plusE s (D.subst δ₁) (D₁.subst δ₂.lift) (D₂.subst δ₂.lift)
  | withI D₁ D₂ => withI (D₁.subst δ) (D₂.subst δ)
  | withE₁ D => withE₁ (D.subst δ)
  | withE₂ D => withE₂ (D.subst δ)
  | lolliI D => lolliI (D.subst δ.lift)
  | lolliE s D D₁ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; lolliE s (D.subst δ₁) (D₁.subst δ₂)

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

def Verif.subst {Δ Δ'} (δ : Subst Use Δ Δ') {A} : (D : Verif Δ A) → Verif Δ' A
  | .uv D => .uv (D.subst δ)
  | .oneI => let .nil := δ; .oneI
  | .oneE s D D₁ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; .oneE s (D.subst δ₁) (D₁.subst δ₂)
  | .zeroE s D => let ⟨_, _, s, δ₁, _⟩ := δ.split s; .zeroE s (D.subst δ₁)
  | .topI => .topI
  | .tensorI s D₁ D₂ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; .tensorI s (D₁.subst δ₁) (D₂.subst δ₂)
  | .tensorE s D D₁ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; .tensorE s (D.subst δ₁) (D₁.subst δ₂.lift.lift)
  | .plusI₁ D => .plusI₁ (D.subst δ)
  | .plusI₂ D => .plusI₂ (D.subst δ)
  | .plusE s D D₁ D₂ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; .plusE s (D.subst δ₁) (D₁.subst δ₂.lift) (D₂.subst δ₂.lift)
  | .withI D₁ D₂ => .withI (D₁.subst δ) (D₂.subst δ)
  | .lolliI D => .lolliI (D.subst δ.lift)

def Use.subst {Δ Δ'} (δ : Subst Use Δ Δ') {A} : (D : Use Δ A) → Use Δ' A
  | .hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | .withE₁ D => .withE₁ (D.subst δ)
  | .withE₂ D => .withE₂ (D.subst δ)
  | .lolliE s D D₁ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; .lolliE s (D.subst δ₁) (D₁.subst δ₂)

end

def Verif.uv' (D : Use Δ A) : Verif Δ A :=
  match A with
  | .base _ => uv D
  | .one => oneE .triv₁ D oneI
  | .zero => zeroE .triv₁ D
  | .top => topI
  | .tensor .. => tensorE .triv₁ D (tensorI (.cons₂ (.cons₁ .nil)) (uv' .hyp) (uv' .hyp))
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

def Seq.subst [j : SCJudge J] {Δ Δ'} (δ : Subst J Δ Δ') {A} : (D : Seq Δ A) → Seq Δ' A
  | id => let .cons s D' .nil := δ; j.cut s D' fun | .here => id
  | oneR => let .nil := δ; oneR
  | oneL s D => let ⟨_, _, s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => oneL s (D.subst δ)
  | zeroL s => let ⟨_, _, s, D', _⟩ := δ.split₁ s; j.cut s D' zeroL
  | topR => topR
  | tensorR s D₁ D₂ => let ⟨_, _, s, δ₁, δ₂⟩ := δ.split s; tensorR s (D₁.subst δ₁) (D₂.subst δ₂)
  | tensorL s D => let ⟨_, _, s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => tensorL s (D.subst δ.lift.lift)
  | plusR₁ D => plusR₁ (D.subst δ)
  | plusR₂ D => plusR₂ (D.subst δ)
  | plusL s D₁ D₂ => let ⟨_, _, s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => plusL s (D₁.subst δ.lift) (D₂.subst δ.lift)
  | withR D₁ D₂ => withR (D₁.subst δ) (D₂.subst δ)
  | withL₁ s D => let ⟨_, _, s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => withL₁ s (D.subst δ.lift)
  | withL₂ s D => let ⟨_, _, s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => withL₂ s (D.subst δ.lift)
  | lolliR D => lolliR (D.subst δ.lift)
  | lolliL s s' D₁ D₂ => let ⟨_, _, s, D', δ⟩ := δ.split₁ s; let ⟨_, _, s', δ₁, δ₂⟩ := δ.split s'; j.cut s D' fun s => lolliL s s' (D₁.subst δ₁) (D₂.subst δ₂.lift)

def Seq.id' : Seq (.cons .nil A) A :=
  match A with
  | .base _ => id
  | .one => oneL .here oneR
  | .zero => zeroL .here
  | .top => topR
  | .tensor .. => tensorL .here (tensorR (.cons₂ (.cons₁ .nil)) id' id')
  | .plus .. => plusL .here (plusR₁ id') (plusR₂ id')
  | .with .. => withR (withL₁ .here id') (withL₂ .here id')
  | .lolli .. => lolliR (lolliL (.there .here) (.cons₁ .nil) id' id')

@[simp]
def Seq.sizeOf : (D : Seq Δ A) → Nat
  | id | oneR | zeroL _ | topR => 0
  | oneL _ D | tensorL _ D | plusR₁ D | plusR₂ D | withL₁ _ D | withL₂ _ D | lolliR D => D.sizeOf + 1
  | tensorR _ D₁ D₂ | plusL _ D₁ D₂ | withR D₁ D₂ | lolliL _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_subst (δ : Subst Hyp Δ Δ') {A} (D : Seq Δ A) : (D.subst δ).sizeOf = D.sizeOf := by
  induction D generalizing Δ' <;> simp! only [*]
  case id => let .cons s .mk .nil := δ; let .refl _ := s.eq_triv₁; rfl
  case oneR => let .nil := δ; rfl

def Seq.cut (s : Split Δ Δ₁ Δ₂) : (D : Seq Δ₁ A) → (E : Seq (Δ₂.cons A) C) → Seq Δ C
  | D, id => let .refl _ := s.eq_triv₁; D
  | oneR, oneL .here E => let .refl _ := s.eq_triv₂; E
  | tensorR s' D₁ D₂, tensorL .here E => let ⟨_, s, s'⟩ := s.shift₁ s'; cut s D₁ (cut s'.cons₂ D₂ E)
  | plusR₁ D, plusL .here E₁ _ => cut s D E₁
  | plusR₂ D, plusL .here _ E₂ => cut s D E₂
  | withR D₁ _, withL₁ .here E => cut s D₁ E
  | withR _ D₂, withL₂ .here E => cut s D₂ E
  | lolliR D, lolliL .here s₂ E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s₂.flip; cut s.flip (cut s' E₁ D) E₂
  | oneL s' D, E => let ⟨_, s, s'⟩ := s.shift₁ s'.toSplit; oneL (.ofSplit s) (cut s' D E)
  | zeroL s', _ => let ⟨_, s, _⟩ := s.shift₁ s'.toSplit; zeroL (.ofSplit s)
  | tensorL s' D, E => let ⟨_, s, s'⟩ := s.shift₁ s'.toSplit; tensorL (.ofSplit s) (cut s'.cons₁.cons₁ D E)
  | plusL s' D₁ D₂, E => let ⟨_, s, s'⟩ := s.shift₁ s'.toSplit; plusL (.ofSplit s) (cut s'.cons₁ D₁ E) (cut s'.cons₁ D₂ E)
  | withL₁ s' D, E => let ⟨_, s, s'⟩ := s.shift₁ s'.toSplit; withL₁ (.ofSplit s) (cut s'.cons₁ D E)
  | withL₂ s' D, E => let ⟨_, s, s'⟩ := s.shift₁ s'.toSplit; withL₂ (.ofSplit s) (cut s'.cons₁ D E)
  | lolliL s' s'' D₁ D₂, E => let ⟨_, s, s'⟩ := s.shift₁ s'.toSplit; let ⟨_, s', s''⟩ := s'.shift₁ s''; lolliL (.ofSplit s) s' D₁ (cut s''.cons₁ D₂ E)
  | D, oneL (.there s') E => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; oneL (.ofSplit s) (cut s'.flip D E)
  | _, zeroL (.there s') => let ⟨_, s, _⟩ := s.flip.shift₁ s'.toSplit; zeroL (.ofSplit s)
  | _, topR => topR
  | D, tensorR (.cons₁ s') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.flip; tensorR s.flip (cut s'.flip D E₁) E₂
  | D, tensorR (.cons₂ s') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'; tensorR s E₁ (cut s'.flip D E₂)
  | D, tensorL (.there s') E => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; tensorL (.ofSplit s) (cut s'.flip.cons₂.cons₂ D (E.subst .exchange₂))
  | D, plusR₁ E => plusR₁ (cut s D E)
  | D, plusR₂ E => plusR₂ (cut s D E)
  | D, plusL (.there s') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; plusL (.ofSplit s) (cut s'.flip.cons₂ D (E₁.subst .exchange)) (cut s'.flip.cons₂ D (E₂.subst .exchange))
  | D, withR E₁ E₂ => withR (cut s D E₁) (cut s D E₂)
  | D, withL₁ (.there s') E => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; withL₁ (.ofSplit s) (cut s'.flip.cons₂ D (E.subst .exchange))
  | D, withL₂ (.there s') E => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; withL₂ (.ofSplit s) (cut s'.flip.cons₂ D (E.subst .exchange))
  | D, lolliR E => lolliR (cut s.cons₂ D (E.subst .exchange))
  | D, lolliL (.there s') (.cons₁ s'') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; let ⟨_, s', s''⟩ := s'.shift₁ s''.flip; lolliL (.ofSplit s) s'.flip (cut s''.flip D E₁) E₂
  | D, lolliL (.there s') (.cons₂ s'') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; let ⟨_, s', s''⟩ := s'.shift₁ s''; lolliL (.ofSplit s) s' E₁ (cut s''.flip.cons₂ D (E₂.subst .exchange))
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
  | lolliL s s' D₁ D₂ => let ⟨_, s, s'⟩ := s.toSplit.flip.shift₁ s'.flip; D₂.toVerif.subst (.cons s.flip (VU.Use.lolliE s'.flip .hyp D₁.toVerif) .id)

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

def VU.Verif.subst' (δ : Subst Verif Δ Δ') {A} (D : Verif Δ A) : Verif Δ' A :=
  (D.toTrue.toSeq.subst (δ.map fun D => D.toTrue.toSeq)).toVerif
