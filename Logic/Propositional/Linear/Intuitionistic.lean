namespace Logic.Propositional.Linear.Intuitionistic

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
  | cons (Γ : Ctx) (A : Propn)

def Ctx.append (Γ : Ctx) : (Γ' : Ctx) → Ctx
  | nil => Γ
  | cons Γ' A => (Γ.append Γ').cons A

theorem Ctx.nil_append : ∀ {Γ}, nil.append Γ = Γ
  | nil => rfl
  | cons .. => congrArg (cons · _) nil_append

theorem Ctx.append_append : ∀ {Γ''}, append Γ (Γ'.append Γ'') = (Γ.append Γ').append Γ''
  | nil => rfl
  | cons .. => congrArg (cons · _) append_append

inductive Split : (Γ Γ₁ Γ₂ : Ctx) → Type
  | nil : Split .nil .nil .nil
  | cons₁ (s : Split Γ Γ₁ Γ₂) : Split (Γ.cons A) (Γ₁.cons A) Γ₂
  | cons₂ (s : Split Γ Γ₁ Γ₂) : Split (Γ.cons A) Γ₁ (Γ₂.cons A)

def Split.triv₁ : ∀ {Γ}, Split Γ Γ .nil
  | .nil => nil
  | .cons .. => triv₁.cons₁

def Split.triv₂ : ∀ {Γ}, Split Γ .nil Γ
  | .nil => nil
  | .cons .. => triv₂.cons₂

theorem Split.eq_triv₁ : ∀ s, (⟨Γ₁, s⟩ : Σ Γ₁, Split Γ Γ₁ .nil) = ⟨Γ, triv₁⟩
  | nil => rfl
  | cons₁ s => let .refl _ := s.eq_triv₁; rfl

theorem Split.eq_triv₂ : ∀ s, (⟨Γ₂, s⟩ : Σ Γ₂, Split Γ .nil Γ₂) = ⟨Γ, triv₂⟩
  | nil => rfl
  | cons₂ s => let .refl _ := s.eq_triv₂; rfl

def Split.flip : (s : Split Γ Γ₁ Γ₂) → Split Γ Γ₂ Γ₁
  | nil => nil
  | cons₁ s => s.flip.cons₂
  | cons₂ s => s.flip.cons₁

def Split.shift₁ : (s : Split Γ Γ₁ Γ₂) → (s₁ : Split Γ₁ Γ₁₁ Γ₁₂) → Σ Γ', Split Γ Γ₁₁ Γ' × Split Γ' Γ₁₂ Γ₂
  | s, nil => ⟨_, triv₂, s⟩
  | cons₁ s, cons₁ s₁ => let ⟨_, s, s'⟩ := s.shift₁ s₁; ⟨_, s.cons₁, s'⟩
  | cons₁ s, cons₂ s₁ => let ⟨_, s, s'⟩ := s.shift₁ s₁; ⟨_, s.cons₂, s'.cons₁⟩
  | cons₂ s, s₁ => let ⟨_, s, s'⟩ := s.shift₁ s₁; ⟨_, s.cons₂, s'.cons₂⟩

def Split.mkAppend : ∀ {Γ₂}, Split (Γ₁.append Γ₂) Γ₁ Γ₂
  | .nil => triv₁
  | .cons .. => mkAppend.cons₂

def Split.append₂ (s : Split Γ Γ₁ Γ₂) : ∀ {Γ'}, Split (Γ.append Γ') Γ₁ (Γ₂.append Γ')
  | .nil => s
  | .cons .. => s.append₂.cons₂

def Split.append₂' : (s : Split Γ Γ₁ Γ₂) → ∀ {Γ'}, Split (.append Γ' Γ) Γ₁ (Γ'.append Γ₂)
  | nil => triv₂
  | cons₁ s => s.append₂'.cons₁
  | cons₂ s => s.append₂'.cons₂

inductive Subst (J : (Γ : Ctx) → (A : Propn) → Type) : (Γ Γ' : Ctx) → Type
  | nil : Subst J .nil .nil
  | cons (s : Split Γ' Γ₁ Γ₂) (D : J Γ₁ A) (γ : Subst J Γ Γ₂) : Subst J (Γ.cons A) Γ'

def Subst.split : (γ : Subst J Γ Γ') → ∀ {Γ₁ Γ₂}, (s : Split Γ Γ₁ Γ₂) → Σ Γ₁' Γ₂', Split Γ' Γ₁' Γ₂' × Subst J Γ₁ Γ₁' × Subst J Γ₂ Γ₂'
  | nil, _, _, .nil => ⟨_, _, .nil, nil, nil⟩
  | cons s' D γ, _, _, .cons₁ s => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; let ⟨_, s, s'⟩ := s'.flip.shift₁ s.flip; ⟨_, _, s.flip, cons s'.flip D γ₁, γ₂⟩
  | cons s' D γ, _, _, .cons₂ s => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; let ⟨_, s, s'⟩ := s'.flip.shift₁ s; ⟨_, _, s, γ₁, cons s'.flip D γ₂⟩

def Subst.append (γ₁ : Subst J Γ₁ Γ₁') : (γ₂ : Subst J Γ₂ Γ₂') → Subst J (Γ₁.append Γ₂) (Γ₁'.append Γ₂')
  | nil => γ₁
  | cons s D γ₂ => cons s.append₂' D (γ₁.append γ₂)

def Subst.consAppend (D : J (.cons .nil A) A) : ∀ {Γ₂}, (γ : Subst J (.append Γ₁ Γ₂) Γ') → Subst J ((Γ₁.cons A).append Γ₂) (Γ'.cons A)
  | .nil, γ => cons (.cons₁ .triv₂) D γ
  | .cons .., cons s D' γ => cons s.cons₂ D' (γ.consAppend D)

inductive Hyp : (Γ : Ctx) → (A : Propn) → Type
  | mk : Hyp (.cons .nil A) A

def Split.toSubst : (s : Split Γ Γ₁ Γ₂) → Subst Hyp (Γ₁.append Γ₂) Γ
  | nil => .nil
  | cons₁ s => .consAppend .mk s.toSubst
  | cons₂ s => .cons triv₂.cons₁ .mk s.toSubst

class JudgeTrans (J J' : (Γ : Ctx) → (A : Propn) → Type) where
  transform (D : J Γ A) : J' Γ A

instance JudgeTrans.id : JudgeTrans J J where
  transform D := D

abbrev Judge : (J : (Γ : Ctx) → (A : Propn) → Type) → Type :=
  JudgeTrans Hyp

def Subst.id [j : Judge J] : ∀ {Γ}, Subst J Γ Γ
  | .nil => nil
  | .cons .. => cons (.cons₁ .triv₂) (j.transform .mk) id

def Subst.lift [j : Judge J] {Γ Γ' A} : (γ : Subst J Γ Γ') → Subst J (Γ.cons A) (Γ'.cons A) :=
  cons (.cons₁ .triv₂) (j.transform .mk)

def Subst.map (jt : JudgeTrans J J') {Γ Γ'} : (γ : Subst J Γ Γ') → Subst J' Γ Γ'
  | nil => nil
  | cons s D γ => cons s (jt.transform D) (γ.map jt)

def Subst.exchange : Subst Hyp (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A) :=
  cons (.cons₂ (.cons₁ .triv₂)) .mk id

def Subst.exchange₂ : Subst Hyp (Ctx.cons Γ A |>.cons B |>.cons C) (Γ.cons B |>.cons C |>.cons A) :=
  cons (.cons₂ (.cons₁ .triv₂)) .mk exchange

inductive Split₁ : (Γ : Ctx) → (A : Propn) → (Γ' : Ctx) → Type
  | here : Split₁ (Γ.cons A) A Γ
  | there (s : Split₁ Γ A Γ') : Split₁ (Γ.cons B) A (Γ'.cons B)

def Split₁.toSplit : (s : Split₁ Γ A Γ') → Split Γ (.cons .nil A) Γ'
  | here => .cons₁ .triv₂
  | there s => s.toSplit.cons₂

def Split₁.ofSplit : (s : Split Γ (.cons .nil A) Γ') → Split₁ Γ A Γ'
  | .cons₁ s => let .refl _ := s.eq_triv₂; here
  | .cons₂ s => (ofSplit s).there

def Subst.split₁ (γ : Subst Hyp Γ Γ') {A Γ₂} (s : Split₁ Γ A Γ₂) : Σ Γ₂', Split₁ Γ' A Γ₂' × Subst Hyp Γ₂ Γ₂' :=
  let ⟨_, _, s, cons s' .mk nil, γ⟩ := γ.split s.toSplit
  let .cons₁ .nil := s'
  ⟨_, .ofSplit s, γ⟩

-- Natural Deduction
namespace ND

inductive True : (Γ : Ctx) → (A : Propn) → Type
  | hyp : True (.cons .nil A) A
  | oneI : True .nil .one
  | oneE (s : Split Γ Γ₁ Γ₂) (D : True Γ₁ .one) (D₁ : True Γ₂ C) : True Γ C
  | zeroE (s : Split Γ Γ₁ Γ₂) (D : True Γ₁ .zero) : True Γ C
  | topI : True Γ .top
  | tensorI (s : Split Γ Γ₁ Γ₂) (D₁ : True Γ₁ A) (D₂ : True Γ₂ B) : True Γ (A.tensor B)
  | tensorE (s : Split Γ Γ₁ Γ₂) (D : True Γ₁ (A.tensor B)) (D₁ : True (Γ₂.cons A |>.cons B) C) : True Γ C
  | plusI₁ (D : True Γ A) : True Γ (A.plus B)
  | plusI₂ (D : True Γ B) : True Γ (.plus A B)
  | plusE (s : Split Γ Γ₁ Γ₂) (D : True Γ₁ (A.plus B)) (D₁ : True (Γ₂.cons A) C) (D₂ : True (Γ₂.cons B) C) : True Γ C
  | withI (D₁ : True Γ A) (D₂ : True Γ B) : True Γ (A.with B)
  | withE₁ (D : True Γ (A.with B)) : True Γ A
  | withE₂ (D : True Γ (.with A B)) : True Γ B
  | lolliI (D : True (Γ.cons A) B) : True Γ (A.lolli B)
  | lolliE (s : Split Γ Γ₁ Γ₂) (D : True Γ₁ (A.lolli B)) (D₁ : True Γ₂ A) : True Γ B

instance True.judge : Judge True where
  transform | .mk => hyp

def True.subst [j : Judge J] [jt : JudgeTrans J True] {Γ Γ'} (γ : Subst J Γ Γ') {A} : (D : True Γ A) → True Γ' A
  | hyp => let .cons s D .nil := γ; let .refl _ := s.eq_triv₁; jt.transform D
  | oneI => let .nil := γ; oneI
  | oneE s D D₁ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; oneE s (D.subst γ₁) (D₁.subst γ₂)
  | zeroE s D => let ⟨_, _, s, γ₁, _⟩ := γ.split s; zeroE s (D.subst γ₁)
  | topI => topI
  | tensorI s D₁ D₂ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; tensorI s (D₁.subst γ₁) (D₂.subst γ₂)
  | tensorE s D D₁ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; tensorE s (D.subst γ₁) (D₁.subst γ₂.lift.lift)
  | plusI₁ D => plusI₁ (D.subst γ)
  | plusI₂ D => plusI₂ (D.subst γ)
  | plusE s D D₁ D₂ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; plusE s (D.subst γ₁) (D₁.subst γ₂.lift) (D₂.subst γ₂.lift)
  | withI D₁ D₂ => withI (D₁.subst γ) (D₂.subst γ)
  | withE₁ D => withE₁ (D.subst γ)
  | withE₂ D => withE₂ (D.subst γ)
  | lolliI D => lolliI (D.subst γ.lift)
  | lolliE s D D₁ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; lolliE s (D.subst γ₁) (D₁.subst γ₂)

end ND

-- Verifications and Uses
namespace VU

mutual

inductive Verif : (Γ : Ctx) → (A : Propn) → Type
  | uv (D : Use Γ (.base P)) : Verif Γ (.base P)
  | oneI : Verif .nil .one
  | oneE (s : Split Γ Γ₁ Γ₂) (D : Use Γ₁ .one) (D₁ : Verif Γ₂ C) : Verif Γ C
  | zeroE (s : Split Γ Γ₁ Γ₂) (D : Use Γ₁ .zero) : Verif Γ C
  | topI : Verif Γ .top
  | tensorI (s : Split Γ Γ₁ Γ₂) (D₁ : Verif Γ₁ A) (D₂ : Verif Γ₂ B) : Verif Γ (A.tensor B)
  | tensorE (s : Split Γ Γ₁ Γ₂) (D : Use Γ₁ (A.tensor B)) (D₁ : Verif (Γ₂.cons A |>.cons B) C) : Verif Γ C
  | plusI₁ (D : Verif Γ A) : Verif Γ (A.plus B)
  | plusI₂ (D : Verif Γ B) : Verif Γ (.plus A B)
  | plusE (s : Split Γ Γ₁ Γ₂) (D : Use Γ₁ (A.plus B)) (D₁ : Verif (Γ₂.cons A) C) (D₂ : Verif (Γ₂.cons B) C) : Verif Γ C
  | withI (D₁ : Verif Γ A) (D₂ : Verif Γ B) : Verif Γ (A.with B)
  | lolliI (D : Verif (Γ.cons A) B) : Verif Γ (A.lolli B)

inductive Use : (Γ : Ctx) → (A : Propn) → Type
  | hyp : Use (.cons .nil A) A
  | withE₁ (D : Use Γ (A.with B)) : Use Γ A
  | withE₂ (D : Use Γ (.with A B)) : Use Γ B
  | lolliE (s : Split Γ Γ₁ Γ₂) (D : Use Γ₁ (A.lolli B)) (D₁ : Verif Γ₂ A) : Use Γ B

end

instance Use.judge : Judge Use where
  transform | .mk => hyp

mutual

def Verif.subst [j : Judge J] [jt : JudgeTrans J Use] {Γ Γ'} (γ : Subst J Γ Γ') {A} : (D : Verif Γ A) → Verif Γ' A
  | .uv D => .uv (D.subst γ)
  | .oneI => let .nil := γ; .oneI
  | .oneE s D D₁ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; .oneE s (D.subst γ₁) (D₁.subst γ₂)
  | .zeroE s D => let ⟨_, _, s, γ₁, _⟩ := γ.split s; .zeroE s (D.subst γ₁)
  | .topI => .topI
  | .tensorI s D₁ D₂ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; .tensorI s (D₁.subst γ₁) (D₂.subst γ₂)
  | .tensorE s D D₁ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; .tensorE s (D.subst γ₁) (D₁.subst γ₂.lift.lift)
  | .plusI₁ D => .plusI₁ (D.subst γ)
  | .plusI₂ D => .plusI₂ (D.subst γ)
  | .plusE s D D₁ D₂ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; .plusE s (D.subst γ₁) (D₁.subst γ₂.lift) (D₂.subst γ₂.lift)
  | .withI D₁ D₂ => .withI (D₁.subst γ) (D₂.subst γ)
  | .lolliI D => .lolliI (D.subst γ.lift)

def Use.subst [j : Judge J] [jt : JudgeTrans J Use] {Γ Γ'} (γ : Subst J Γ Γ') {A} : (D : Use Γ A) → Use Γ' A
  | .hyp => let .cons s D .nil := γ; let .refl _ := s.eq_triv₁; jt.transform D
  | .withE₁ D => .withE₁ (D.subst γ)
  | .withE₂ D => .withE₂ (D.subst γ)
  | .lolliE s D D₁ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; .lolliE s (D.subst γ₁) (D₁.subst γ₂)

end

def Verif.uv' (D : Use Γ A) : Verif Γ A :=
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
  transform | .mk => uv' .hyp

mutual

def Verif.toTrue : (D : Verif Γ A) → ND.True Γ A
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

def Use.toTrue : (D : Use Γ A) → ND.True Γ A
  | .hyp => .hyp
  | .withE₁ D => .withE₁ D.toTrue
  | .withE₂ D => .withE₂ D.toTrue
  | .lolliE s D D₁ => .lolliE s D.toTrue D₁.toTrue

end

end VU

-- Sequent Calculus
namespace SC

inductive Seq : (Γ : Ctx) → (A : Propn) → Type
  | id : Seq (.cons .nil (.base P)) (.base P)
  | oneR : Seq .nil .one
  | oneL (s : Split₁ Γ .one Γ') (D : Seq Γ' C) : Seq Γ C
  | zeroL (s : Split₁ Γ .zero Γ') : Seq Γ C
  | topR : Seq Γ .top
  | tensorR (s : Split Γ Γ₁ Γ₂) (D₁ : Seq Γ₁ A) (D₂ : Seq Γ₂ B) : Seq Γ (A.tensor B)
  | tensorL (s : Split₁ Γ (A.tensor B) Γ') (D : Seq (Γ'.cons A |>.cons B) C) : Seq Γ C
  | plusR₁ (D : Seq Γ A) : Seq Γ (A.plus B)
  | plusR₂ (D : Seq Γ B) : Seq Γ (.plus A B)
  | plusL (s : Split₁ Γ (A.plus B) Γ') (D₁ : Seq (Γ'.cons A) C) (D₂ : Seq (Γ'.cons B) C) : Seq Γ C
  | withR (D₁ : Seq Γ A) (D₂ : Seq Γ B) : Seq Γ (A.with B)
  | withL₁ (s : Split₁ Γ (A.with B) Γ') (D : Seq (Γ'.cons A) C) : Seq Γ C
  | withL₂ (s : Split₁ Γ (.with A B) Γ') (D : Seq (Γ'.cons B) C) : Seq Γ C
  | lolliR (D : Seq (Γ.cons A) B) : Seq Γ (A.lolli B)
  | lolliL (s : Split₁ Γ (A.lolli B) Γ') (s' : Split Γ' Γ₁ Γ₂) (D₁ : Seq Γ₁ A) (D₂ : Seq (Γ₂.cons B) C) : Seq Γ C

def Seq.rename (γ : Subst Hyp Γ Γ') {A} : (D : Seq Γ A) → Seq Γ' A
  | id => let .cons s .mk .nil := γ; let .refl _ := s.eq_triv₁; id
  | oneR => let .nil := γ; oneR
  | oneL s D => let ⟨_, s, γ⟩ := γ.split₁ s; oneL s (D.rename γ)
  | zeroL s => let ⟨_, s, _⟩ := γ.split₁ s; zeroL s
  | topR => topR
  | tensorR s D₁ D₂ => let ⟨_, _, s, γ₁, γ₂⟩ := γ.split s; tensorR s (D₁.rename γ₁) (D₂.rename γ₂)
  | tensorL s D => let ⟨_, s, γ⟩ := γ.split₁ s; tensorL s (D.rename γ.lift.lift)
  | plusR₁ D => plusR₁ (D.rename γ)
  | plusR₂ D => plusR₂ (D.rename γ)
  | plusL s D₁ D₂ => let ⟨_, s, γ⟩ := γ.split₁ s; plusL s (D₁.rename γ.lift) (D₂.rename γ.lift)
  | withR D₁ D₂ => withR (D₁.rename γ) (D₂.rename γ)
  | withL₁ s D => let ⟨_, s, γ⟩ := γ.split₁ s; withL₁ s (D.rename γ.lift)
  | withL₂ s D => let ⟨_, s, γ⟩ := γ.split₁ s; withL₂ s (D.rename γ.lift)
  | lolliR D => lolliR (D.rename γ.lift)
  | lolliL s s' D₁ D₂ => let ⟨_, s, γ⟩ := γ.split₁ s; let ⟨_, _, s', γ₁, γ₂⟩ := γ.split s'; lolliL s s' (D₁.rename γ₁) (D₂.rename γ₂.lift)

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
def Seq.sizeOf : (D : Seq Γ A) → Nat
  | id | oneR | zeroL _ | topR => 0
  | oneL _ D | tensorL _ D | plusR₁ D | plusR₂ D | withL₁ _ D | withL₂ _ D | lolliR D => D.sizeOf + 1
  | tensorR _ D₁ D₂ | plusL _ D₁ D₂ | withR D₁ D₂ | lolliL _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename (γ : Subst Hyp Γ Γ') {A} (D : Seq Γ A) : (D.rename γ).sizeOf = D.sizeOf := by
  induction D generalizing Γ' <;> simp! only [*]
  case id => let .cons s .mk .nil := γ; let .refl _ := s.eq_triv₁; rfl
  case oneR => let .nil := γ; rfl

def Seq.cut (s : Split Γ Γ₁ Γ₂) : (D : Seq Γ₁ A) → (E : Seq (Γ₂.cons A) C) → Seq Γ C
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
  | D, tensorL (.there s') E => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; tensorL (.ofSplit s) (cut s'.flip.cons₂.cons₂ D (E.rename .exchange₂))
  | D, plusR₁ E => plusR₁ (cut s D E)
  | D, plusR₂ E => plusR₂ (cut s D E)
  | D, plusL (.there s') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; plusL (.ofSplit s) (cut s'.flip.cons₂ D (E₁.rename .exchange)) (cut s'.flip.cons₂ D (E₂.rename .exchange))
  | D, withR E₁ E₂ => withR (cut s D E₁) (cut s D E₂)
  | D, withL₁ (.there s') E => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; withL₁ (.ofSplit s) (cut s'.flip.cons₂ D (E.rename .exchange))
  | D, withL₂ (.there s') E => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; withL₂ (.ofSplit s) (cut s'.flip.cons₂ D (E.rename .exchange))
  | D, lolliR E => lolliR (cut s.cons₂ D (E.rename .exchange))
  | D, lolliL (.there s') (.cons₁ s'') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; let ⟨_, s', s''⟩ := s'.shift₁ s''.flip; lolliL (.ofSplit s) s'.flip (cut s''.flip D E₁) E₂
  | D, lolliL (.there s') (.cons₂ s'') E₁ E₂ => let ⟨_, s, s'⟩ := s.flip.shift₁ s'.toSplit; let ⟨_, s', s''⟩ := s'.shift₁ s''; lolliL (.ofSplit s) s' E₁ (cut s''.flip.cons₂ D (E₂.rename .exchange))
  termination_by D E => (A, D.sizeOf, E.sizeOf)

def Seq.multicut : (γ : Subst Seq Γ₂ Γ₂') → ∀ {Γ₁ A}, (D : Seq (.append Γ₁ Γ₂) A) → Seq (Γ₁.append Γ₂') A
  | .nil, _, _, D => D
  | .cons s D' γ, _, _, D => (Ctx.append_append ▸ multicut γ (cut (.append₂ (.flip .mkAppend)) D' D)).rename (.append .id s.toSubst)

def Seq.subst (γ : Subst Seq Γ Γ') {A} (D : Seq Γ A) : Seq Γ' A :=
  (Ctx.nil_append ▸ multicut γ (Γ₁ := .nil) (A := A) (Ctx.nil_append ▸ D) :)

def Seq.toVerif : (D : Seq Γ A) → VU.Verif Γ A
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

def ND.True.toSeq : (D : True Γ A) → SC.Seq Γ A
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

def VU.Verif.subst' (γ : Subst Verif Γ Γ') {A} (D : Verif Γ A) : Verif Γ' A :=
  (D.toTrue.toSeq.subst (γ.map ⟨fun D => D.toTrue.toSeq⟩)).toVerif
