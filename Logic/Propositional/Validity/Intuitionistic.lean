import Logic.Propositional.Structural
import Logic.Propositional.Linear

namespace Logic.Propositional.Validity.Intuitionistic

inductive Propn
  | base (P : Linear.BasePropn)
  | one
  | zero
  | top
  | tensor (A B : Propn)
  | plus (A B : Propn)
  | with (A B : Propn)
  | lolli (A B : Propn)
  | bang (A : Propn)

local notation "SCtx" => Structural.Ctx (Propn := Propn)
local notation "LCtx" => Linear.Ctx (Propn := Propn)
local notation "SHyp" => Structural.Hyp (Propn := Propn)
local notation "LHyp" => Linear.Hyp (Propn := Propn)
local notation "Split" => Linear.Split (Propn := Propn)
local notation "Split₁" => Linear.Split₁ (Propn := Propn)
local notation "SSubst" => Structural.Subst (Propn := Propn)
local notation "LSubst" => Linear.Subst (Propn := Propn)
local notation "LJudge" => Linear.Judge (Propn := Propn)

/-! Natural Deduction -/

namespace ND

inductive True : (Γ : SCtx) → (Δ : LCtx) → (A : Propn) → Type
  | hyp : True Γ (.cons .nil A) A
  | validHyp (u : SHyp Γ A) : True Γ .nil A
  | oneI : True Γ .nil .one
  | oneE (s : Split Δ Δ₁ Δ₂) (D : True Γ Δ₁ .one) (D₁ : True Γ Δ₂ C) : True Γ Δ C
  | zeroE (s : Split Δ Δ₁ Δ₂) (D : True Γ Δ₁ .zero) : True Γ Δ C
  | topI : True Γ Δ .top
  | tensorI (s : Split Δ Δ₁ Δ₂) (D₁ : True Γ Δ₁ A) (D₂ : True Γ Δ₂ B) : True Γ Δ (A.tensor B)
  | tensorE (s : Split Δ Δ₁ Δ₂) (D : True Γ Δ₁ (A.tensor B)) (D₁ : True Γ (Δ₂.cons A |>.cons B) C) : True Γ Δ C
  | plusI₁ (D : True Γ Δ A) : True Γ Δ (A.plus B)
  | plusI₂ (D : True Γ Δ B) : True Γ Δ (.plus A B)
  | plusE (s : Split Δ Δ₁ Δ₂) (D : True Γ Δ₁ (A.plus B)) (D₁ : True Γ (Δ₂.cons A) C) (D₂ : True Γ (Δ₂.cons B) C) : True Γ Δ C
  | withI (D₁ : True Γ Δ A) (D₂ : True Γ Δ B) : True Γ Δ (A.with B)
  | withE₁ (D : True Γ Δ (A.with B)) : True Γ Δ A
  | withE₂ (D : True Γ Δ (.with A B)) : True Γ Δ B
  | lolliI (D : True Γ (Δ.cons A) B) : True Γ Δ (A.lolli B)
  | lolliE (s : Split Δ Δ₁ Δ₂) (D : True Γ Δ₁ (A.lolli B)) (D₁ : True Γ Δ₂ A) : True Γ Δ B
  | bangI (D : True Γ .nil A) : True Γ .nil A.bang
  | bangE (s : Split Δ Δ₁ Δ₂) (D : True Γ Δ₁ A.bang) (D₁ : True (Γ.cons A) Δ₂ C) : True Γ Δ C

instance True.judge : LJudge (True Γ) where
  hyp := hyp

def True.substS (γ : SSubst SHyp Γ Γ') : (D : True Γ Δ A) → True Γ' Δ A
  | hyp => hyp
  | validHyp u => validHyp (γ u)
  | oneI => oneI
  | oneE s D D₁ => oneE s (D.substS γ) (D₁.substS γ)
  | zeroE s D => zeroE s (D.substS γ)
  | topI => topI
  | tensorI s D₁ D₂ => tensorI s (D₁.substS γ) (D₂.substS γ)
  | tensorE s D D₁ => tensorE s (D.substS γ) (D₁.substS γ)
  | plusI₁ D => plusI₁ (D.substS γ)
  | plusI₂ D => plusI₂ (D.substS γ)
  | plusE s D D₁ D₂ => plusE s (D.substS γ) (D₁.substS γ) (D₂.substS γ)
  | withI D₁ D₂ => withI (D₁.substS γ) (D₂.substS γ)
  | withE₁ D => withE₁ (D.substS γ)
  | withE₂ D => withE₂ (D.substS γ)
  | lolliI D => lolliI (D.substS γ)
  | lolliE s D D₁ => lolliE s (D.substS γ) (D₁.substS γ)
  | bangI D => bangI (D.substS γ)
  | bangE s D D₁ => bangE s (D.substS γ) (D₁.substS γ.lift)

def True.subst (δ : LSubst (True Γ) Δ Δ') : (D : True Γ Δ A) → True Γ Δ' A
  | hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | validHyp u => let .nil := δ; validHyp u
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
  | bangI D => let .nil := δ; bangI D
  | bangE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; bangE s (D.subst δ₁) (D₁.subst (δ₂.map (substS .weakening)))

end ND

/-! Verifications and Uses -/

namespace VU

mutual

inductive Verif : (Γ : SCtx) → (Δ : LCtx) → (A : Propn) → Type
  | uv (D : Use Γ Δ (.base P)) : Verif Γ Δ (.base P)
  | oneI : Verif Γ .nil .one
  | oneE (s : Split Δ Δ₁ Δ₂) (D : Use Γ Δ₁ .one) (D₁ : Verif Γ Δ₂ C) : Verif Γ Δ C
  | zeroE (s : Split Δ Δ₁ Δ₂) (D : Use Γ Δ₁ .zero) : Verif Γ Δ C
  | topI : Verif Γ Δ .top
  | tensorI (s : Split Δ Δ₁ Δ₂) (D₁ : Verif Γ Δ₁ A) (D₂ : Verif Γ Δ₂ B) : Verif Γ Δ (A.tensor B)
  | tensorE (s : Split Δ Δ₁ Δ₂) (D : Use Γ Δ₁ (A.tensor B)) (D₁ : Verif Γ (Δ₂.cons A |>.cons B) C) : Verif Γ Δ C
  | plusI₁ (D : Verif Γ Δ A) : Verif Γ Δ (A.plus B)
  | plusI₂ (D : Verif Γ Δ B) : Verif Γ Δ (.plus A B)
  | plusE (s : Split Δ Δ₁ Δ₂) (D : Use Γ Δ₁ (A.plus B)) (D₁ : Verif Γ (Δ₂.cons A) C) (D₂ : Verif Γ (Δ₂.cons B) C) : Verif Γ Δ C
  | withI (D₁ : Verif Γ Δ A) (D₂ : Verif Γ Δ B) : Verif Γ Δ (A.with B)
  | lolliI (D : Verif Γ (Δ.cons A) B) : Verif Γ Δ (A.lolli B)
  | bangI (D : Verif Γ .nil A) : Verif Γ .nil A.bang
  | bangE (s : Split Δ Δ₁ Δ₂) (D : Use Γ Δ₁ A.bang) (D₁ : Verif (Γ.cons A) Δ₂ C) : Verif Γ Δ C

inductive Use : (Γ : SCtx) → (Δ : LCtx) → (A : Propn) → Type
  | hyp : Use Γ (.cons .nil A) A
  | validHyp (u : SHyp Γ A) : Use Γ .nil A
  | withE₁ (D : Use Γ Δ (A.with B)) : Use Γ Δ A
  | withE₂ (D : Use Γ Δ (.with A B)) : Use Γ Δ B
  | lolliE (s : Split Δ Δ₁ Δ₂) (D : Use Γ Δ₁ (A.lolli B)) (D₁ : Verif Γ Δ₂ A) : Use Γ Δ B

end

instance Use.judge : LJudge (Use Γ) where
  hyp := hyp

mutual

def Verif.substS (γ : SSubst SHyp Γ Γ') : (D : Verif Γ Δ A) → Verif Γ' Δ A
  | .uv D => .uv (D.substS γ)
  | .oneI => .oneI
  | .oneE s D D₁ => .oneE s (D.substS γ) (D₁.substS γ)
  | .zeroE s D => .zeroE s (D.substS γ)
  | .topI => .topI
  | .tensorI s D₁ D₂ => .tensorI s (D₁.substS γ) (D₂.substS γ)
  | .tensorE s D D₁ => .tensorE s (D.substS γ) (D₁.substS γ)
  | .plusI₁ D => .plusI₁ (D.substS γ)
  | .plusI₂ D => .plusI₂ (D.substS γ)
  | .plusE s D D₁ D₂ => .plusE s (D.substS γ) (D₁.substS γ) (D₂.substS γ)
  | .withI D₁ D₂ => .withI (D₁.substS γ) (D₂.substS γ)
  | .lolliI D => .lolliI (D.substS γ)
  | .bangI D => .bangI (D.substS γ)
  | .bangE s D D₁ => .bangE s (D.substS γ) (D₁.substS γ.lift)

def Use.substS (γ : SSubst SHyp Γ Γ') : (D : Use Γ Δ A) → Use Γ' Δ A
  | .hyp => .hyp
  | .validHyp u => .validHyp (γ u)
  | .withE₁ D => .withE₁ (D.substS γ)
  | .withE₂ D => .withE₂ (D.substS γ)
  | .lolliE s D D₁ => .lolliE s (D.substS γ) (D₁.substS γ)

end

mutual

def Verif.subst (δ : LSubst (Use Γ) Δ Δ') : (D : Verif Γ Δ A) → Verif Γ Δ' A
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
  | .bangI D => let .nil := δ; .bangI D
  | .bangE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .bangE s (D.subst δ₁) (D₁.subst (δ₂.map (.substS .weakening)))

def Use.subst (δ : LSubst (Use Γ) Δ Δ') : (D : Use Γ Δ A) → Use Γ Δ' A
  | .hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | .validHyp u => let .nil := δ; .validHyp u
  | .withE₁ D => .withE₁ (D.subst δ)
  | .withE₂ D => .withE₂ (D.subst δ)
  | .lolliE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .lolliE s (D.subst δ₁) (D₁.subst δ₂)

end

def Verif.uv' (D : Use Γ Δ A) : Verif Γ Δ A :=
  match A with
  | .base _ => uv D
  | .one => oneE .triv₁ D oneI
  | .zero => zeroE .triv₁ D
  | .top => topI
  | .tensor .. => tensorE .triv₁ D (tensorI (.cons₂ .triv₁) (uv' .hyp) (uv' .hyp))
  | .plus .. => plusE .triv₁ D (plusI₁ (uv' .hyp)) (plusI₂ (uv' .hyp))
  | .with .. => withI (uv' (.withE₁ D)) (uv' (.withE₂ D))
  | .lolli .. => lolliI (uv' (.lolliE (.cons₂ .triv₁) D (uv' .hyp)))
  | .bang _ => bangE .triv₁ D (bangI (uv' (.validHyp .here)))

instance Verif.judge : LJudge (Verif Γ) where
  hyp := uv' .hyp

mutual

def Verif.toTrue : (D : Verif Γ Δ A) → ND.True Γ Δ A
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
  | .bangI D => .bangI D.toTrue
  | .bangE s D D₁ => .bangE s D.toTrue D₁.toTrue

def Use.toTrue : (D : Use Γ Δ A) → ND.True Γ Δ A
  | .hyp => .hyp
  | .validHyp u => .validHyp u
  | .withE₁ D => .withE₁ D.toTrue
  | .withE₂ D => .withE₂ D.toTrue
  | .lolliE s D D₁ => .lolliE s D.toTrue D₁.toTrue

end

end VU

/-! Sequent Calculus -/

namespace SC

inductive Seq : (Γ : SCtx) → (Δ : LCtx) → (A : Propn) → Type
  | id : Seq Γ (.cons .nil (.base P)) (.base P)
  | validL (u : SHyp Γ A) (D : Seq Γ (Δ.cons A) C) : Seq Γ Δ C
  | oneR : Seq Γ .nil .one
  | oneL (s : Split₁ Δ .one Δ') (D : Seq Γ Δ' C) : Seq Γ Δ C
  | zeroL (s : Split₁ Δ .zero Δ') : Seq Γ Δ C
  | topR : Seq Γ Δ .top
  | tensorR (s : Split Δ Δ₁ Δ₂) (D₁ : Seq Γ Δ₁ A) (D₂ : Seq Γ Δ₂ B) : Seq Γ Δ (A.tensor B)
  | tensorL (s : Split₁ Δ (A.tensor B) Δ') (D : Seq Γ (Δ'.cons A |>.cons B) C) : Seq Γ Δ C
  | plusR₁ (D : Seq Γ Δ A) : Seq Γ Δ (A.plus B)
  | plusR₂ (D : Seq Γ Δ B) : Seq Γ Δ (.plus A B)
  | plusL (s : Split₁ Δ (A.plus B) Δ') (D₁ : Seq Γ (Δ'.cons A) C) (D₂ : Seq Γ (Δ'.cons B) C) : Seq Γ Δ C
  | withR (D₁ : Seq Γ Δ A) (D₂ : Seq Γ Δ B) : Seq Γ Δ (A.with B)
  | withL₁ (s : Split₁ Δ (A.with B) Δ') (D : Seq Γ (Δ'.cons A) C) : Seq Γ Δ C
  | withL₂ (s : Split₁ Δ (.with A B) Δ') (D : Seq Γ (Δ'.cons B) C) : Seq Γ Δ C
  | lolliR (D : Seq Γ (Δ.cons A) B) : Seq Γ Δ (A.lolli B)
  | lolliL (s : Split₁ Δ (A.lolli B) Δ') (s' : Split Δ' Δ₁ Δ₂) (D₁ : Seq Γ Δ₁ A) (D₂ : Seq Γ (Δ₂.cons B) C) : Seq Γ Δ C
  | bangR (D : Seq Γ .nil A) : Seq Γ .nil A.bang
  | bangL (s : Split₁ Δ A.bang Δ') (D : Seq (Γ.cons A) Δ' C) : Seq Γ Δ C

class SeqJudge (J : (Γ : SCtx) → (Δ : LCtx) → (A : Propn) → Type) where
  [judge : LJudge (J Γ)]
  cut (s : Split Δ Δ₁ Δ₂) (D' : J Γ Δ₁ A) (D : ∀ {Δ}, (s : Split₁ Δ A Δ₂) → Seq Γ Δ C) : Seq Γ Δ C
  weaken (D : J Γ Δ A) : J (Γ.cons B) Δ A

attribute [instance] SeqJudge.judge

instance seqJudgeHyp : SeqJudge fun _ => LHyp where
  cut s D' D := D (let .mk := D'; .ofSplit s)
  weaken D := D

def Seq.substS (γ : SSubst SHyp Γ Γ') : (D : Seq Γ Δ A) → Seq Γ' Δ A
  | id => id
  | validL u D => validL (γ u) (D.substS γ)
  | oneR => oneR
  | oneL s D => oneL s (D.substS γ)
  | zeroL s => zeroL s
  | topR => topR
  | tensorR s D₁ D₂ => tensorR s (D₁.substS γ) (D₂.substS γ)
  | tensorL s D => tensorL s (D.substS γ)
  | plusR₁ D => plusR₁ (D.substS γ)
  | plusR₂ D => plusR₂ (D.substS γ)
  | plusL s D₁ D₂ => plusL s (D₁.substS γ) (D₂.substS γ)
  | withR D₁ D₂ => withR (D₁.substS γ) (D₂.substS γ)
  | withL₁ s D => withL₁ s (D.substS γ)
  | withL₂ s D => withL₂ s (D.substS γ)
  | lolliR D => lolliR (D.substS γ)
  | lolliL s s' D₁ D₂ => lolliL s s' (D₁.substS γ) (D₂.substS γ)
  | bangR D => bangR (D.substS γ)
  | bangL s D => bangL s (D.substS γ.lift)

def Seq.subst [j : SeqJudge J] (δ : LSubst (J Γ) Δ Δ') : (D : Seq Γ Δ A) → Seq Γ Δ' A
  | id => let .cons s D' .nil := δ; j.cut s D' fun | .here => id
  | validL u D => validL u (D.subst δ.lift)
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
  | bangR D => let .nil := δ; bangR D
  | bangL s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cut s D' fun s => bangL s (D.subst (δ.map j.weaken))

def Seq.id' : ∀ {A}, Seq Γ (.cons .nil A) A
  | .base _ => id
  | .one => oneL .here oneR
  | .zero => zeroL .here
  | .top => topR
  | .tensor .. => tensorL .here (tensorR (.cons₂ .triv₁) id' id')
  | .plus .. => plusL .here (plusR₁ id') (plusR₂ id')
  | .with .. => withR (withL₁ .here id') (withL₂ .here id')
  | .lolli .. => lolliR (lolliL (.there .here) .triv₁ id' id')
  | .bang _ => bangL .here (bangR (validL .here id'))

@[simp]
def Seq.sizeOf : (D : Seq Γ Δ A) → Nat
  | id | oneR | zeroL _ | topR => 0
  | validL _ D | oneL _ D | tensorL _ D | plusR₁ D | plusR₂ D | withL₁ _ D | withL₂ _ D | lolliR D | bangR D | bangL _ D => D.sizeOf + 1
  | tensorR _ D₁ D₂ | plusL _ D₁ D₂ | withR D₁ D₂ | lolliL _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_substS (γ : SSubst SHyp Γ Γ') (D : Seq Γ Δ A) : (D.substS γ).sizeOf = D.sizeOf :=
  by induction D generalizing Γ' <;> simp! only [*]

@[simp]
theorem Seq.sizeOf_subst (δ : LSubst LHyp Δ Δ') (D : Seq Γ Δ A) : (D.subst δ).sizeOf = D.sizeOf := by
  induction D generalizing Δ' <;> simp! only [*]
  case id => let .cons s .mk .nil := δ; let .refl _ := s.eq_triv₁; rfl
  case oneR => let .nil := δ; rfl
  case bangR => let .nil := δ; rfl

mutual

set_option maxHeartbeats 300000

def Seq.cut (s : Split Δ Δ₁ Δ₂) : (D : Seq Γ Δ₁ A) → (E : Seq Γ (Δ₂.cons A) C) → Seq Γ Δ C
  | id, id => let .refl _ := s.eq_triv₁; id

  | oneR, oneL .here E => let .refl _ := s.eq_triv₂; E
  | tensorR s' D₁ D₂, tensorL .here E => let ⟨s, s'⟩ := s.shift s'; cut s D₁ (cut s'.cons₂ D₂ E)
  | plusR₁ D, plusL .here E₁ _ => cut s D E₁
  | plusR₂ D, plusL .here _ E₂ => cut s D E₂
  | withR D₁ _, withL₁ .here E => cut s D₁ E
  | withR _ D₂, withL₂ .here E => cut s D₂ E
  | lolliR D, lolliL .here s' E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift s'.flip; cut s.flip (cut s' E₁ D) E₂
  | bangR D, bangL .here E => let .refl _ := s.eq_triv₂; cut! D E

  | validL u D, E => validL u (cut s.cons₁ D E)
  | oneL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; oneL s (cut s' D E)
  | zeroL s', _ => let ⟨s, _⟩ := s.shift₁ s'; zeroL s
  | tensorL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; tensorL s (cut s'.cons₁.cons₁ D E)
  | plusL s' D₁ D₂, E => let ⟨s, s'⟩ := s.shift₁ s'; plusL s (cut s'.cons₁ D₁ E) (cut s'.cons₁ D₂ E)
  | withL₁ s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; withL₁ s (cut s'.cons₁ D E)
  | withL₂ s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; withL₂ s (cut s'.cons₁ D E)
  | lolliL s' s'' D₁ D₂, E => let ⟨s, s'⟩ := s.shift₁ s'; let ⟨s', s''⟩ := s'.shift s''; lolliL s s' D₁ (cut s''.cons₁ D₂ E)
  | bangL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; bangL s (cut s' D (E.substS .weakening))

  | D, validL u E => validL u (cut s.cons₂ D (E.subst .exchange))
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
  | D, bangL (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; bangL s (cut s'.flip (D.substS .weakening) E)

  termination_by D E => (A, 0, D.sizeOf, E.sizeOf)

def Seq.cut! : (D : Seq Γ .nil A) → (E : Seq (Γ.cons A) Δ C) → Seq Γ Δ C
  | D, validL .here E => cut .triv₂ D (cut! D E)

  | _, id => id
  | D, validL (.there u) E => validL u (cut! D E)
  | _, oneR => oneR
  | D, oneL s E => oneL s (cut! D E)
  | _, zeroL s => zeroL s
  | _, topR => topR
  | D, tensorR s E₁ E₂ => tensorR s (cut! D E₁) (cut! D E₂)
  | D, tensorL s E => tensorL s (cut! D E)
  | D, plusR₁ E => plusR₁ (cut! D E)
  | D, plusR₂ E => plusR₂ (cut! D E)
  | D, plusL s E₁ E₂ => plusL s (cut! D E₁) (cut! D E₂)
  | D, withR E₁ E₂ => withR (cut! D E₁) (cut! D E₂)
  | D, withL₁ s E => withL₁ s (cut! D E)
  | D, withL₂ s E => withL₂ s (cut! D E)
  | D, lolliR E => lolliR (cut! D E)
  | D, lolliL s s' E₁ E₂ => lolliL s s' (cut! D E₁) (cut! D E₂)
  | D, bangR E => bangR (cut! D E)
  | D, bangL s E => bangL s (cut! (D.substS .weakening) (E.substS .exchange))

  termination_by D E => (A, 1, D.sizeOf, E.sizeOf)

end

instance Seq.seqJudge : SeqJudge Seq where
  judge.hyp := id'
  cut s D' D := cut s D' (D .here)
  weaken := substS .weakening

def Seq.toVerif : (D : Seq Γ Δ A) → VU.Verif Γ Δ A
  | id => .uv .hyp
  | validL u D => D.toVerif.subst (.cons .triv₂ (.validHyp u) .id)
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
  | withL₁ s D => D.toVerif.subst (.cons s.toSplit (.withE₁ .hyp) .id)
  | withL₂ s D => D.toVerif.subst (.cons s.toSplit (.withE₂ .hyp) .id)
  | lolliR D => .lolliI D.toVerif
  | lolliL s s' D₁ D₂ => let ⟨s, s'⟩ := s.toSplit.flip.shift s'.flip; D₂.toVerif.subst (.cons s.flip (.lolliE s'.flip .hyp D₁.toVerif) .id)
  | bangR D => .bangI D.toVerif
  | bangL s D => .bangE s.toSplit .hyp D.toVerif

end SC

def ND.True.toSeq : (D : True Γ Δ A) → SC.Seq Γ Δ A
  | hyp => .id'
  | validHyp u => .validL u .id'
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
  | bangI D => .bangR D.toSeq
  | bangE s D D₁ => .cut s D.toSeq (.bangL .here D₁.toSeq)

def VU.Verif.subst' (δ : LSubst (Verif Γ) Δ Δ') (D : Verif Γ Δ A) : Verif Γ Δ' A :=
  (D.toTrue.toSeq.subst (δ.map fun D => D.toTrue.toSeq)).toVerif
