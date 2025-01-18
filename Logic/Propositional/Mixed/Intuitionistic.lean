import Logic.Propositional.Structural
import Logic.Propositional.Linear

namespace Logic.Propositional.Mixed.Intuitionistic

mutual

inductive SPropn
  | base (P : Structural.BasePropn)
  | true
  | false
  | and (A B : SPropn)
  | or (A B : SPropn)
  | imp (A B : SPropn)
  | up (A : LPropn)

inductive LPropn
  | base (P : Linear.BasePropn)
  | one
  | zero
  | top
  | tensor (A B : LPropn)
  | plus (A B : LPropn)
  | with (A B : LPropn)
  | lolli (A B : LPropn)
  | down (A : SPropn)

end

local notation "SCtx" => Structural.Ctx (Propn := SPropn)
local notation "LCtx" => Linear.Ctx (Propn := LPropn)
local notation "SHyp" => Structural.Hyp (Propn := SPropn)
local notation "LHyp" => Linear.Hyp (Propn := LPropn)
local notation "Split" => Linear.Split (Propn := LPropn)
local notation "Split₁" => Linear.Split₁ (Propn := LPropn)
local notation "SSubst" => Structural.Subst (Propn := SPropn)
local notation "LSubst" => Linear.Subst (Propn := LPropn)
local notation "SJudge" => Structural.Judge (Propn := SPropn)
local notation "LJudge" => Linear.Judge (Propn := LPropn)
local notation "SJudgeTrans" => Structural.JudgeTrans (Propn := SPropn)

/-! Natural Deduction -/

namespace ND

mutual

inductive STrue : (Γ : SCtx) → (A : SPropn) → Type
  | hyp (u : SHyp Γ A) : STrue Γ A
  | trueI : STrue Γ .true
  | falseE (D : STrue Γ .false) : STrue Γ C
  | andI (D₁ : STrue Γ A) (D₂ : STrue Γ B) : STrue Γ (A.and B)
  | andE₁ (D : STrue Γ (A.and B)) : STrue Γ A
  | andE₂ (D : STrue Γ (.and A B)) : STrue Γ B
  | orI₁ (D : STrue Γ A) : STrue Γ (A.or B)
  | orI₂ (D : STrue Γ B) : STrue Γ (.or A B)
  | orE (D : STrue Γ (A.or B)) (D₁ : STrue (Γ.cons A) C) (D₂ : STrue (Γ.cons B) C) : STrue Γ C
  | impI (D : STrue (Γ.cons A) B) : STrue Γ (A.imp B)
  | impE (D : STrue Γ (A.imp B)) (D₁ : STrue Γ A) : STrue Γ B
  | upI (D : LTrue Γ .nil A) : STrue Γ (.up A)

inductive LTrue : (Γ : SCtx) → (Δ : LCtx) → (A : LPropn) → Type
  | hyp : LTrue Γ (.cons .nil A) A
  | oneI : LTrue Γ .nil .one
  | oneE (s : Split Δ Δ₁ Δ₂) (D : LTrue Γ Δ₁ .one) (D₁ : LTrue Γ Δ₂ C) : LTrue Γ Δ C
  | zeroE (s : Split Δ Δ₁ Δ₂) (D : LTrue Γ Δ₁ .zero) : LTrue Γ Δ C
  | topI : LTrue Γ Δ .top
  | tensorI (s : Split Δ Δ₁ Δ₂) (D₁ : LTrue Γ Δ₁ A) (D₂ : LTrue Γ Δ₂ B) : LTrue Γ Δ (A.tensor B)
  | tensorE (s : Split Δ Δ₁ Δ₂) (D : LTrue Γ Δ₁ (A.tensor B)) (D₁ : LTrue Γ (Δ₂.cons A |>.cons B) C) : LTrue Γ Δ C
  | plusI₁ (D : LTrue Γ Δ A) : LTrue Γ Δ (A.plus B)
  | plusI₂ (D : LTrue Γ Δ B) : LTrue Γ Δ (.plus A B)
  | plusE (s : Split Δ Δ₁ Δ₂) (D : LTrue Γ Δ₁ (A.plus B)) (D₁ : LTrue Γ (Δ₂.cons A) C) (D₂ : LTrue Γ (Δ₂.cons B) C) : LTrue Γ Δ C
  | withI (D₁ : LTrue Γ Δ A) (D₂ : LTrue Γ Δ B) : LTrue Γ Δ (A.with B)
  | withE₁ (D : LTrue Γ Δ (A.with B)) : LTrue Γ Δ A
  | withE₂ (D : LTrue Γ Δ (.with A B)) : LTrue Γ Δ B
  | lolliI (D : LTrue Γ (Δ.cons A) B) : LTrue Γ Δ (A.lolli B)
  | lolliE (s : Split Δ Δ₁ Δ₂) (D : LTrue Γ Δ₁ (A.lolli B)) (D₁ : LTrue Γ Δ₂ A) : LTrue Γ Δ B
  | downI (D : STrue Γ A) : LTrue Γ .nil (.down A)
  | downE (s : Split Δ Δ₁ Δ₂) (D : LTrue Γ Δ₁ (.down A)) (D₁ : LTrue (Γ.cons A) Δ₂ C) : LTrue Γ Δ C
  | falseE (D : STrue Γ .false) : LTrue Γ Δ C
  | orE (D : STrue Γ (A.or B)) (D₁ : LTrue (Γ.cons A) Δ C) (D₂ : LTrue (Γ.cons B) Δ C) : LTrue Γ Δ C
  | upE (D : STrue Γ (.up A)) : LTrue Γ .nil A

end

instance STrue.judgeTransHyp : SJudgeTrans SHyp STrue where
  transform := hyp

instance LTrue.judge : LJudge (LTrue Γ) where
  hyp := hyp

mutual

def STrue.substS [j : SJudge J] [jt : SJudgeTrans J STrue] (γ : SSubst J Γ Γ') {A} : (D : STrue Γ A) → STrue Γ' A
  | .hyp u => jt.transform (γ u)
  | .trueI => .trueI
  | .falseE D => .falseE (D.substS γ)
  | .andI D₁ D₂ => .andI (D₁.substS γ) (D₂.substS γ)
  | .andE₁ D => .andE₁ (D.substS γ)
  | .andE₂ D => .andE₂ (D.substS γ)
  | .orI₁ D => .orI₁ (D.substS γ)
  | .orI₂ D => .orI₂ (D.substS γ)
  | .orE D D₁ D₂ => .orE (D.substS γ) (D₁.substS γ.lift) (D₂.substS γ.lift)
  | .impI D => .impI (D.substS γ.lift)
  | .impE D D₁ => .impE (D.substS γ) (D₁.substS γ)
  | .upI D => .upI (D.substS γ)

def LTrue.substS [j : SJudge J] [jt : SJudgeTrans J STrue] (γ : SSubst J Γ Γ') : (D : LTrue Γ Δ A) → LTrue Γ' Δ A
  | .hyp => .hyp
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
  | .withE₁ D => .withE₁ (D.substS γ)
  | .withE₂ D => .withE₂ (D.substS γ)
  | .lolliI D => .lolliI (D.substS γ)
  | .lolliE s D D₁ => .lolliE s (D.substS γ) (D₁.substS γ)
  | .downI D => .downI (D.substS γ)
  | .downE s D D₁ => .downE s (D.substS γ) (D₁.substS γ.lift)
  | .falseE D => .falseE (D.substS γ)
  | .orE D D₁ D₂ => .orE (D.substS γ) (D₁.substS γ.lift) (D₂.substS γ.lift)
  | .upE D => .upE (D.substS γ)

end

instance STrue.judge : SJudge STrue where
  rename := substS

def LTrue.substL (δ : LSubst (LTrue Γ) Δ Δ') : (D : LTrue Γ Δ A) → LTrue Γ Δ' A
  | hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | oneI => let .nil := δ; oneI
  | oneE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; oneE s (D.substL δ₁) (D₁.substL δ₂)
  | zeroE s D => let ⟨s, δ₁, _⟩ := δ.split s; zeroE s (D.substL δ₁)
  | topI => topI
  | tensorI s D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; tensorI s (D₁.substL δ₁) (D₂.substL δ₂)
  | tensorE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; tensorE s (D.substL δ₁) (D₁.substL δ₂.lift.lift)
  | plusI₁ D => plusI₁ (D.substL δ)
  | plusI₂ D => plusI₂ (D.substL δ)
  | plusE s D D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; plusE s (D.substL δ₁) (D₁.substL δ₂.lift) (D₂.substL δ₂.lift)
  | withI D₁ D₂ => withI (D₁.substL δ) (D₂.substL δ)
  | withE₁ D => withE₁ (D.substL δ)
  | withE₂ D => withE₂ (D.substL δ)
  | lolliI D => lolliI (D.substL δ.lift)
  | lolliE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; lolliE s (D.substL δ₁) (D₁.substL δ₂)
  | downI D => let .nil := δ; downI D
  | downE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; downE s (D.substL δ₁) (D₁.substL (δ₂.map (substS .weakening)))
  | falseE D => falseE D
  | orE D D₁ D₂ => orE D (D₁.substL (δ.map (substS .weakening))) (D₂.substL (δ.map (substS .weakening)))
  | upE D => let .nil := δ; upE D

end ND

/-! Verifications and Uses -/

namespace VU

mutual

inductive SVerif : (Γ : SCtx) → (A : SPropn) → Type
  | uv (D : SUse Γ (.base P)) : SVerif Γ (.base P)
  | trueI : SVerif Γ .true
  | falseE (D : SUse Γ .false) : SVerif Γ C
  | andI (D₁ : SVerif Γ A) (D₂ : SVerif Γ B) : SVerif Γ (A.and B)
  | orI₁ (D : SVerif Γ A) : SVerif Γ (A.or B)
  | orI₂ (D : SVerif Γ B) : SVerif Γ (.or A B)
  | orE (D : SUse Γ (A.or B)) (D₁ : SVerif (Γ.cons A) C) (D₂ : SVerif (Γ.cons B) C) : SVerif Γ C
  | impI (D : SVerif (Γ.cons A) B) : SVerif Γ (A.imp B)
  | upI (D : LVerif Γ .nil A) : SVerif Γ (.up A)

inductive SUse : (Γ : SCtx) → (A : SPropn) → Type
  | hyp (u : SHyp Γ A) : SUse Γ A
  | andE₁ (D : SUse Γ (A.and B)) : SUse Γ A
  | andE₂ (D : SUse Γ (.and A B)) : SUse Γ B
  | impE (D : SUse Γ (A.imp B)) (D₁ : SVerif Γ A) : SUse Γ B

inductive LVerif : (Γ : SCtx) → (Δ : LCtx) → (A : LPropn) → Type
  | uv (D : LUse Γ Δ (.base P)) : LVerif Γ Δ (.base P)
  | oneI : LVerif Γ .nil .one
  | oneE (s : Split Δ Δ₁ Δ₂) (D : LUse Γ Δ₁ .one) (D₁ : LVerif Γ Δ₂ C) : LVerif Γ Δ C
  | zeroE (s : Split Δ Δ₁ Δ₂) (D : LUse Γ Δ₁ .zero) : LVerif Γ Δ C
  | topI : LVerif Γ Δ .top
  | tensorI (s : Split Δ Δ₁ Δ₂) (D₁ : LVerif Γ Δ₁ A) (D₂ : LVerif Γ Δ₂ B) : LVerif Γ Δ (A.tensor B)
  | tensorE (s : Split Δ Δ₁ Δ₂) (D : LUse Γ Δ₁ (A.tensor B)) (D₁ : LVerif Γ (Δ₂.cons A |>.cons B) C) : LVerif Γ Δ C
  | plusI₁ (D : LVerif Γ Δ A) : LVerif Γ Δ (A.plus B)
  | plusI₂ (D : LVerif Γ Δ B) : LVerif Γ Δ (.plus A B)
  | plusE (s : Split Δ Δ₁ Δ₂) (D : LUse Γ Δ₁ (A.plus B)) (D₁ : LVerif Γ (Δ₂.cons A) C) (D₂ : LVerif Γ (Δ₂.cons B) C) : LVerif Γ Δ C
  | withI (D₁ : LVerif Γ Δ A) (D₂ : LVerif Γ Δ B) : LVerif Γ Δ (A.with B)
  | lolliI (D : LVerif Γ (Δ.cons A) B) : LVerif Γ Δ (A.lolli B)
  | downI (D : SVerif Γ A) : LVerif Γ .nil (.down A)
  | downE (s : Split Δ Δ₁ Δ₂) (D : LUse Γ Δ₁ (.down A)) (D₁ : LVerif (Γ.cons A) Δ₂ C) : LVerif Γ Δ C
  | falseE (D : SUse Γ .false) : LVerif Γ Δ C
  | orE (D : SUse Γ (A.or B)) (D₁ : LVerif (Γ.cons A) Δ C) (D₂ : LVerif (Γ.cons B) Δ C) : LVerif Γ Δ C

inductive LUse : (Γ : SCtx) → (Δ : LCtx) → (A : LPropn) → Type
  | hyp : LUse Γ (.cons .nil A) A
  | withE₁ (D : LUse Γ Δ (A.with B)) : LUse Γ Δ A
  | withE₂ (D : LUse Γ Δ (.with A B)) : LUse Γ Δ B
  | lolliE (s : Split Δ Δ₁ Δ₂) (D : LUse Γ Δ₁ (A.lolli B)) (D₁ : LVerif Γ Δ₂ A) : LUse Γ Δ B
  | upE (D : SUse Γ (.up A)) : LUse Γ .nil A

end

instance SUse.judgeTransHyp : SJudgeTrans SHyp SUse where
  transform := hyp

instance LUse.judge : LJudge (LUse Γ) where
  hyp := hyp

mutual

def SVerif.substS [j : SJudge J] [jt : SJudgeTrans J SUse] (γ : SSubst J Γ Γ') {A} : (D : SVerif Γ A) → SVerif Γ' A
  | .uv D => .uv (D.substS γ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.substS γ)
  | .andI D₁ D₂ => .andI (D₁.substS γ) (D₂.substS γ)
  | .orI₁ D => .orI₁ (D.substS γ)
  | .orI₂ D => .orI₂ (D.substS γ)
  | .orE D D₁ D₂ => .orE (D.substS γ) (D₁.substS γ.lift) (D₂.substS γ.lift)
  | .impI D => .impI (D.substS γ.lift)
  | .upI D => .upI (D.substS γ)

def SUse.substS [j : SJudge J] [jt : SJudgeTrans J SUse] (γ : SSubst J Γ Γ') {A} : (D : SUse Γ A) → SUse Γ' A
  | .hyp u => jt.transform (γ u)
  | .andE₁ D => .andE₁ (D.substS γ)
  | .andE₂ D => .andE₂ (D.substS γ)
  | .impE D D₁ => .impE (D.substS γ) (D₁.substS γ)

def LVerif.substS [j : SJudge J] [jt : SJudgeTrans J SUse] (γ : SSubst J Γ Γ') : (D : LVerif Γ Δ A) → LVerif Γ' Δ A
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
  | .downI D => .downI (D.substS γ)
  | .downE s D D₁ => .downE s (D.substS γ) (D₁.substS γ.lift)
  | .falseE D => .falseE (D.substS γ)
  | .orE D D₁ D₂ => .orE (D.substS γ) (D₁.substS γ.lift) (D₂.substS γ.lift)

def LUse.substS [j : SJudge J] [jt : SJudgeTrans J SUse] (γ : SSubst J Γ Γ') : (D : LUse Γ Δ A) → LUse Γ' Δ A
  | .hyp => .hyp
  | .withE₁ D => .withE₁ (D.substS γ)
  | .withE₂ D => .withE₂ (D.substS γ)
  | .lolliE s D D₁ => .lolliE s (D.substS γ) (D₁.substS γ)
  | .upE D => .upE (D.substS γ)

end

instance SUse.judge : SJudge SUse where
  rename := substS

mutual

def LVerif.substL (δ : LSubst (LUse Γ) Δ Δ') : (D : LVerif Γ Δ A) → LVerif Γ Δ' A
  | .uv D => .uv (D.substL δ)
  | .oneI => let .nil := δ; .oneI
  | .oneE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .oneE s (D.substL δ₁) (D₁.substL δ₂)
  | .zeroE s D => let ⟨s, δ₁, _⟩ := δ.split s; .zeroE s (D.substL δ₁)
  | .topI => .topI
  | .tensorI s D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .tensorI s (D₁.substL δ₁) (D₂.substL δ₂)
  | .tensorE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .tensorE s (D.substL δ₁) (D₁.substL δ₂.lift.lift)
  | .plusI₁ D => .plusI₁ (D.substL δ)
  | .plusI₂ D => .plusI₂ (D.substL δ)
  | .plusE s D D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .plusE s (D.substL δ₁) (D₁.substL δ₂.lift) (D₂.substL δ₂.lift)
  | .withI D₁ D₂ => .withI (D₁.substL δ) (D₂.substL δ)
  | .lolliI D => .lolliI (D.substL δ.lift)
  | .downI D => let .nil := δ; .downI D
  | .downE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .downE s (D.substL δ₁) (D₁.substL (δ₂.map (.substS .weakening)))
  | .falseE D => .falseE D
  | .orE D D₁ D₂ => .orE D (D₁.substL (δ.map (.substS .weakening))) (D₂.substL (δ.map (.substS .weakening)))

def LUse.substL (δ : LSubst (LUse Γ) Δ Δ') : (D : LUse Γ Δ A) → LUse Γ Δ' A
  | .hyp => let .cons s D .nil := δ; let .refl _ := s.eq_triv₁; D
  | .withE₁ D => .withE₁ (D.substL δ)
  | .withE₂ D => .withE₂ (D.substL δ)
  | .lolliE s D D₁ => let ⟨s, δ₁, δ₂⟩ := δ.split s; .lolliE s (D.substL δ₁) (D₁.substL δ₂)
  | .upE D => let .nil := δ; .upE D

end

mutual

def SVerif.uv' (D : SUse Γ A) : SVerif Γ A :=
  match A with
  | .base _ => .uv D
  | .true => .trueI
  | .false => .falseE D
  | .and .. => .andI (SVerif.uv' (.andE₁ D)) (SVerif.uv' (.andE₂ D))
  | .or .. => .orE D (.orI₁ (SVerif.uv' (.hyp .here))) (.orI₂ (SVerif.uv' (.hyp .here)))
  | .imp .. => .impI (SVerif.uv' (.impE (D.substS .weakening) (SVerif.uv' (.hyp .here))))
  | .up _ => .upI (LVerif.uv' (.upE D))

def LVerif.uv' (D : LUse Γ Δ A) : LVerif Γ Δ A :=
  match A with
  | .base _ => .uv D
  | .one => .oneE .triv₁ D .oneI
  | .zero => .zeroE .triv₁ D
  | .top => .topI
  | .tensor .. => .tensorE .triv₁ D (.tensorI (.cons₂ .triv₁) (LVerif.uv' .hyp) (LVerif.uv' .hyp))
  | .plus .. => .plusE .triv₁ D (.plusI₁ (LVerif.uv' .hyp)) (.plusI₂ (LVerif.uv' .hyp))
  | .with .. => .withI (LVerif.uv' (.withE₁ D)) (LVerif.uv' (.withE₂ D))
  | .lolli .. => .lolliI (LVerif.uv' (.lolliE (.cons₂ .triv₁) D (LVerif.uv' .hyp)))
  | .down _ => .downE .triv₁ D (.downI (SVerif.uv' (.hyp .here)))

end

instance SVerif.judge : SJudge SVerif where
  transform u := uv' (.hyp u)
  rename := substS

instance LVerif.judge : LJudge (LVerif Γ) where
  hyp := uv' .hyp

mutual

def SVerif.toTrue : (D : SVerif Γ A) → ND.STrue Γ A
  | .uv D => D.toTrue
  | .trueI => .trueI
  | .falseE D => .falseE D.toTrue
  | .andI D₁ D₂ => .andI D₁.toTrue D₂.toTrue
  | .orI₁ D => .orI₁ D.toTrue
  | .orI₂ D => .orI₂ D.toTrue
  | .orE D D₁ D₂ => .orE D.toTrue D₁.toTrue D₂.toTrue
  | .impI D => .impI D.toTrue
  | .upI D => .upI D.toTrue

def SUse.toTrue : (D : SUse Γ A) → ND.STrue Γ A
  | .hyp u => .hyp u
  | .andE₁ D => .andE₁ D.toTrue
  | .andE₂ D => .andE₂ D.toTrue
  | .impE D D₁ => .impE D.toTrue D₁.toTrue

def LVerif.toTrue : (D : LVerif Γ Δ A) → ND.LTrue Γ Δ A
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
  | .downI D => .downI D.toTrue
  | .downE s D D₁ => .downE s D.toTrue D₁.toTrue
  | .falseE D => .falseE D.toTrue
  | .orE D D₁ D₂ => .orE D.toTrue D₁.toTrue D₂.toTrue

def LUse.toTrue : (D : LUse Γ Δ A) → ND.LTrue Γ Δ A
  | .hyp => .hyp
  | .withE₁ D => .withE₁ D.toTrue
  | .withE₂ D => .withE₂ D.toTrue
  | .lolliE s D D₁ => .lolliE s D.toTrue D₁.toTrue
  | .upE D => .upE D.toTrue

end

end VU

/-! Sequent Calculus -/

namespace SC

mutual

inductive SSeq : (Γ : SCtx) → (A : SPropn) → Type
  | id (u : SHyp Γ (.base P)) : SSeq Γ (.base P)
  | trueR : SSeq Γ .true
  | falseL (u : SHyp Γ .false) : SSeq Γ C
  | andR (D₁ : SSeq Γ A) (D₂ : SSeq Γ B) : SSeq Γ (A.and B)
  | andL₁ (u : SHyp Γ (A.and B)) (D : SSeq (Γ.cons A) C) : SSeq Γ C
  | andL₂ (u : SHyp Γ (.and A B)) (D : SSeq (Γ.cons B) C) : SSeq Γ C
  | orR₁ (D : SSeq Γ A) : SSeq Γ (A.or B)
  | orR₂ (D : SSeq Γ B) : SSeq Γ (.or A B)
  | orL (u : SHyp Γ (A.or B)) (D₁ : SSeq (Γ.cons A) C) (D₂ : SSeq (Γ.cons B) C) : SSeq Γ C
  | impR (D : SSeq (Γ.cons A) B) : SSeq Γ (A.imp B)
  | impL (u : SHyp Γ (A.imp B)) (D₁ : SSeq Γ A) (D₂ : SSeq (Γ.cons B) C) : SSeq Γ C
  | upR (D : LSeq Γ .nil A) : SSeq Γ (.up A)

inductive LSeq : (Γ : SCtx) → (Δ : LCtx) → (A : LPropn) → Type
  | id : LSeq Γ (.cons .nil (.base P)) (.base P)
  | oneR : LSeq Γ .nil .one
  | oneL (s : Split₁ Δ .one Δ') (D : LSeq Γ Δ' C) : LSeq Γ Δ C
  | zeroL (s : Split₁ Δ .zero Δ') : LSeq Γ Δ C
  | topR : LSeq Γ Δ .top
  | tensorR (s : Split Δ Δ₁ Δ₂) (D₁ : LSeq Γ Δ₁ A) (D₂ : LSeq Γ Δ₂ B) : LSeq Γ Δ (A.tensor B)
  | tensorL (s : Split₁ Δ (A.tensor B) Δ') (D : LSeq Γ (Δ'.cons A |>.cons B) C) : LSeq Γ Δ C
  | plusR₁ (D : LSeq Γ Δ A) : LSeq Γ Δ (A.plus B)
  | plusR₂ (D : LSeq Γ Δ B) : LSeq Γ Δ (.plus A B)
  | plusL (s : Split₁ Δ (A.plus B) Δ') (D₁ : LSeq Γ (Δ'.cons A) C) (D₂ : LSeq Γ (Δ'.cons B) C) : LSeq Γ Δ C
  | withR (D₁ : LSeq Γ Δ A) (D₂ : LSeq Γ Δ B) : LSeq Γ Δ (A.with B)
  | withL₁ (s : Split₁ Δ (A.with B) Δ') (D : LSeq Γ (Δ'.cons A) C) : LSeq Γ Δ C
  | withL₂ (s : Split₁ Δ (.with A B) Δ') (D : LSeq Γ (Δ'.cons B) C) : LSeq Γ Δ C
  | lolliR (D : LSeq Γ (Δ.cons A) B) : LSeq Γ Δ (A.lolli B)
  | lolliL (s : Split₁ Δ (A.lolli B) Δ') (s' : Split Δ' Δ₁ Δ₂) (D₁ : LSeq Γ Δ₁ A) (D₂ : LSeq Γ (Δ₂.cons B) C) : LSeq Γ Δ C
  | downR (D : SSeq Γ A) : LSeq Γ .nil (.down A)
  | downL (s : Split₁ Δ (.down A) Δ') (D : LSeq (Γ.cons A) Δ' C) : LSeq Γ Δ C
  | falseL (u : SHyp Γ .false) : LSeq Γ Δ C
  | andL₁ (u : SHyp Γ (A.and B)) (D : LSeq (Γ.cons A) Δ C) : LSeq Γ Δ C
  | andL₂ (u : SHyp Γ (.and A B)) (D : LSeq (Γ.cons B) Δ C) : LSeq Γ Δ C
  | orL (u : SHyp Γ (A.or B)) (D₁ : LSeq (Γ.cons A) Δ C) (D₂ : LSeq (Γ.cons B) Δ C) : LSeq Γ Δ C
  | impL (u : SHyp Γ (A.imp B)) (D₁ : SSeq Γ A) (D₂ : LSeq (Γ.cons B) Δ C) : LSeq Γ Δ C
  | upL (u : SHyp Γ (.up A)) (D : LSeq Γ (Δ.cons A) C) : LSeq Γ Δ C

end

class SeqSJudge (J) extends SJudge J where
  cutSS (γ : SSubst J Γ Γ') (u : SHyp Γ A) (D : ∀ {Γ'}, (γ : SSubst J Γ Γ') → (u : SHyp Γ' A) → SSeq Γ' C) : SSeq Γ' C
  cutSL (γ : SSubst J Γ Γ') (u : SHyp Γ A) (D : ∀ {Γ'}, (γ : SSubst J Γ Γ') → (u : SHyp Γ' A) → LSeq Γ' Δ C) : LSeq Γ' Δ C

instance seqJudgeSHyp : SeqSJudge SHyp where
  cutSS γ u D := D γ (γ u)
  cutSL γ u D := D γ (γ u)

class SeqLJudge (J : (Γ : SCtx) → (Δ : LCtx) → (A : LPropn) → Type) where
  [judge : LJudge (J Γ)]
  cutL (s : Split Δ Δ₁ Δ₂) (D' : J Γ Δ₁ A) (D : ∀ {Δ}, (s : Split₁ Δ A Δ₂) → LSeq Γ Δ C) : LSeq Γ Δ C
  weaken (D : J Γ Δ A) : J (Γ.cons B) Δ A

attribute [instance] SeqLJudge.judge

instance seqJudgeLHyp : SeqLJudge fun _ => LHyp where
  cutL s D' D := D (let .mk := D'; .ofSplit s)
  weaken D := D

mutual

def SSeq.substS [j : SeqSJudge J] [jt : SJudgeTrans J SSeq] (γ : SSubst J Γ Γ') {A} : (D : SSeq Γ A) → SSeq Γ' A
  | .id u => jt.transform (γ u)
  | .trueR => .trueR
  | .falseL u => j.cutSS γ u fun _ => .falseL
  | .andR D₁ D₂ => .andR (D₁.substS γ) (D₂.substS γ)
  | .andL₁ u D => j.cutSS γ u fun γ u => .andL₁ u (D.substS γ.lift)
  | .andL₂ u D => j.cutSS γ u fun γ u => .andL₂ u (D.substS γ.lift)
  | .orR₁ D => .orR₁ (D.substS γ)
  | .orR₂ D => .orR₂ (D.substS γ)
  | .orL u D₁ D₂ => j.cutSS γ u fun γ u => .orL u (D₁.substS γ.lift) (D₂.substS γ.lift)
  | .impR D => .impR (D.substS γ.lift)
  | .impL u D₁ D₂ => j.cutSS γ u fun γ u => .impL u (D₁.substS γ) (D₂.substS γ.lift)
  | .upR D => .upR (D.substS γ)

def LSeq.substS [j : SeqSJudge J] [jt : SJudgeTrans J SSeq] (γ : SSubst J Γ Γ') : (D : LSeq Γ Δ A) → LSeq Γ' Δ A
  | .id => .id
  | .oneR => .oneR
  | .oneL s D => .oneL s (D.substS γ)
  | .zeroL s => .zeroL s
  | .topR => .topR
  | .tensorR s D₁ D₂ => .tensorR s (D₁.substS γ) (D₂.substS γ)
  | .tensorL s D => .tensorL s (D.substS γ)
  | .plusR₁ D => .plusR₁ (D.substS γ)
  | .plusR₂ D => .plusR₂ (D.substS γ)
  | .plusL s D₁ D₂ => .plusL s (D₁.substS γ) (D₂.substS γ)
  | .withR D₁ D₂ => .withR (D₁.substS γ) (D₂.substS γ)
  | .withL₁ s D => .withL₁ s (D.substS γ)
  | .withL₂ s D => .withL₂ s (D.substS γ)
  | .lolliR D => .lolliR (D.substS γ)
  | .lolliL s s' D₁ D₂ => .lolliL s s' (D₁.substS γ) (D₂.substS γ)
  | .downR D => .downR (D.substS γ)
  | .downL s D => .downL s (D.substS γ.lift)
  | .falseL u => j.cutSL γ u fun _ => .falseL
  | .andL₁ u D => j.cutSL γ u fun γ u => .andL₁ u (D.substS γ.lift)
  | .andL₂ u D => j.cutSL γ u fun γ u => .andL₂ u (D.substS γ.lift)
  | .orL u D₁ D₂ => j.cutSL γ u fun γ u => .orL u (D₁.substS γ.lift) (D₂.substS γ.lift)
  | .impL u D₁ D₂ => j.cutSL γ u fun γ u => .impL u (D₁.substS γ) (D₂.substS γ.lift)
  | .upL u D => j.cutSL γ u fun γ u => .upL u (D.substS γ)

end

def LSeq.substL [j : SeqLJudge J] (δ : LSubst (J Γ) Δ Δ') : (D : LSeq Γ Δ A) → LSeq Γ Δ' A
  | id => let .cons s D' .nil := δ; j.cutL s D' fun | .here => id
  | oneR => let .nil := δ; oneR
  | oneL s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cutL s D' fun s => oneL s (D.substL δ)
  | zeroL s => let ⟨s, D', _⟩ := δ.split₁ s; j.cutL s D' fun s => zeroL s
  | topR => topR
  | tensorR s D₁ D₂ => let ⟨s, δ₁, δ₂⟩ := δ.split s; tensorR s (D₁.substL δ₁) (D₂.substL δ₂)
  | tensorL s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cutL s D' fun s => tensorL s (D.substL δ.lift.lift)
  | plusR₁ D => plusR₁ (D.substL δ)
  | plusR₂ D => plusR₂ (D.substL δ)
  | plusL s D₁ D₂ => let ⟨s, D', δ⟩ := δ.split₁ s; j.cutL s D' fun s => plusL s (D₁.substL δ.lift) (D₂.substL δ.lift)
  | withR D₁ D₂ => withR (D₁.substL δ) (D₂.substL δ)
  | withL₁ s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cutL s D' fun s => withL₁ s (D.substL δ.lift)
  | withL₂ s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cutL s D' fun s => withL₂ s (D.substL δ.lift)
  | lolliR D => lolliR (D.substL δ.lift)
  | lolliL s s' D₁ D₂ => let ⟨s, D', δ⟩ := δ.split₁ s; let ⟨s', δ₁, δ₂⟩ := δ.split s'; j.cutL s D' fun s => lolliL s s' (D₁.substL δ₁) (D₂.substL δ₂.lift)
  | downR D => let .nil := δ; downR D
  | downL s D => let ⟨s, D', δ⟩ := δ.split₁ s; j.cutL s D' fun s => downL s (D.substL (δ.map j.weaken))
  | falseL u => falseL u
  | andL₁ u D => andL₁ u (D.substL (δ.map j.weaken))
  | andL₂ u D => andL₂ u (D.substL (δ.map j.weaken))
  | orL u D₁ D₂ => orL u (D₁.substL (δ.map j.weaken)) (D₂.substL (δ.map j.weaken))
  | impL u D₁ D₂ => impL u D₁ (D₂.substL (δ.map j.weaken))
  | upL u D => upL u (D.substL δ.lift)

mutual

def SSeq.id' (u : SHyp Γ A) : SSeq Γ A :=
  match A with
  | .base _ => .id u
  | .true => .trueR
  | .false => .falseL u
  | .and .. => .andR (.andL₁ u (SSeq.id' .here)) (.andL₂ u (SSeq.id' .here))
  | .or .. => .orL u (.orR₁ (SSeq.id' .here)) (.orR₂ (SSeq.id' .here))
  | .imp .. => .impR (.impL u.there (SSeq.id' .here) (SSeq.id' .here))
  | .up .. => .upR (.upL u LSeq.id')

def LSeq.id' : ∀ {A}, LSeq Γ (.cons .nil A) A
  | .base _ => .id
  | .one => .oneL .here .oneR
  | .zero => .zeroL .here
  | .top => .topR
  | .tensor .. => .tensorL .here (.tensorR (.cons₂ .triv₁) LSeq.id' LSeq.id')
  | .plus .. => .plusL .here (.plusR₁ LSeq.id') (.plusR₂ LSeq.id')
  | .with .. => .withR (.withL₁ .here LSeq.id') (.withL₂ .here LSeq.id')
  | .lolli .. => .lolliR (.lolliL (.there .here) .triv₁ LSeq.id' LSeq.id')
  | .down _ => .downL .here (.downR (SSeq.id' .here))

end

instance SSeq.judgeTransHyp : SJudgeTrans SHyp SSeq where
  transform := id'

instance SSeq.judge : SJudge SSeq where
  rename := substS

mutual

@[simp]
def SSeq.sizeOf : (D : SSeq Γ A) → Nat
  | .id _ | .trueR | .falseL _ => 0
  | .andL₁ _ D | .andL₂ _ D | .orR₁ D | .orR₂ D | .impR D | .upR D => D.sizeOf + 1
  | .andR D₁ D₂ | .orL _ D₁ D₂ | .impL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
def LSeq.sizeOf : (D : LSeq Γ Δ A) → Nat
  | .id | .oneR | .zeroL _ | .topR | .falseL _ => 0
  | .oneL _ D | .tensorL _ D | .plusR₁ D | .plusR₂ D | .withL₁ _ D | .withL₂ _ D | .lolliR D | .downR D | .downL _ D | .andL₁ _ D | .andL₂ _ D | .upL _ D => D.sizeOf + 1
  | .tensorR _ D₁ D₂ | .plusL _ D₁ D₂ | .withR D₁ D₂ | .lolliL _ _ D₁ D₂ | .orL _ D₁ D₂ | .impL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

end

mutual

@[simp]
theorem SSeq.sizeOf_substS (γ : SSubst SHyp Γ Γ') : (D : SSeq Γ A) → (D.substS γ).sizeOf = D.sizeOf
  | .id _ | .trueR | .falseL _ | .andR .. | .andL₁ .. | .andL₂ .. | .orR₁ _ | .orR₂ _ | .orL .. | .impR _ | .impL .. | .upR _ => by simp! only [SSeq.sizeOf_substS, LSeq.sizeOf_substS, SSeq.judgeTransHyp]

@[simp]
theorem LSeq.sizeOf_substS (γ : SSubst SHyp Γ Γ') : (D : LSeq Γ Δ A) → (D.substS γ).sizeOf = D.sizeOf
  | .id | .oneR | .oneL .. | .zeroL _ | .topR | .tensorR .. | .tensorL .. | .plusR₁ _ | .plusR₂ _ | .plusL .. | .withR .. | .withL₁ .. | .withL₂ .. | .lolliR _ | .lolliL .. | .downR _ | .downL .. | .falseL _ | .andL₁ .. | .andL₂ .. | .orL .. | .impL .. | .upL .. => by simp! only [SSeq.sizeOf_substS, LSeq.sizeOf_substS]

end

@[simp]
theorem LSeq.sizeOf_substL (δ : LSubst LHyp Δ Δ') (D : LSeq Γ Δ A) : (D.substL δ).sizeOf = D.sizeOf :=
  match Δ, A, D with
  | _, _, oneL ..
  | _, _, zeroL _
  | _, _, topR
  | _, _, tensorR ..
  | _, _, tensorL ..
  | _, _, plusR₁ _
  | _, _, plusR₂ _
  | _, _, plusL ..
  | _, _, withR ..
  | _, _, withL₁ ..
  | _, _, withL₂ ..
  | _, _, lolliR _
  | _, _, lolliL ..
  | _, _, downL ..
  | _, _, falseL _
  | _, _, andL₁ ..
  | _, _, andL₂ ..
  | _, _, orL ..
  | _, _, impL ..
  | _, _, upL .. => by simp! only [sizeOf_substL]
  | _, _, id => let .cons s .mk .nil := δ; let .refl _ := s.eq_triv₁; rfl
  | _, _, oneR
  | _, _, downR _ => let .nil := δ; rfl

mutual

set_option maxHeartbeats 600000

def SSeq.cutS : (D : SSeq Γ A) → (E : SSeq (Γ.cons A) C) → SSeq Γ C
  | .id u, .id .here => .id u

  | D@(.andR D₁ _), .andL₁ .here E => SSeq.cutS D₁ (SSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D@(.andR _ D₂), .andL₂ .here E => SSeq.cutS D₂ (SSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D@(.orR₁ D₁), .orL .here E₁ _ => SSeq.cutS D₁ (SSeq.cutS (D.substS .weakening) (E₁.substS .exchange))
  | D@(.orR₂ D₂), .orL .here _ E₂ => SSeq.cutS D₂ (SSeq.cutS (D.substS .weakening) (E₂.substS .exchange))
  | D@(.impR D₂), .impL .here E₁ E₂ => SSeq.cutS (SSeq.cutS (SSeq.cutS D E₁) D₂) (SSeq.cutS (D.substS .weakening) (E₂.substS .exchange))

  | .falseL u, _ => .falseL u
  | .andL₁ u D, E => .andL₁ u (SSeq.cutS D (E.substS (.lift .weakening)))
  | .andL₂ u D, E => .andL₂ u (SSeq.cutS D (E.substS (.lift .weakening)))
  | .orL u D₁ D₂, E => .orL u (SSeq.cutS D₁ (E.substS (.lift .weakening))) (SSeq.cutS D₂ (E.substS (.lift .weakening)))
  | .impL u D₁ D₂, E => .impL u D₁ (SSeq.cutS D₂ (E.substS (.lift .weakening)))

  | _, .id (.there u) => .id u
  | _, .trueR => .trueR
  | _, .falseL (.there u) => .falseL u
  | D, .andR E₁ E₂ => .andR (SSeq.cutS D E₁) (SSeq.cutS D E₂)
  | D, .andL₁ (.there u) E => .andL₁ u (SSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D, .andL₂ (.there u) E => .andL₂ u (SSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D, .orR₁ E => .orR₁ (SSeq.cutS D E)
  | D, .orR₂ E => .orR₂ (SSeq.cutS D E)
  | D, .orL (.there u) E₁ E₂ => .orL u (SSeq.cutS (D.substS .weakening) (E₁.substS .exchange)) (SSeq.cutS (D.substS .weakening) (E₂.substS .exchange))
  | D, .impR E => .impR (SSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D, .impL (.there u) E₁ E₂ => .impL u (SSeq.cutS D E₁) (SSeq.cutS (D.substS .weakening) (E₂.substS .exchange))
  | D, .upR E => .upR (LSeq.cutS D E)

  termination_by D E => (sizeOf A, D.sizeOf, E.sizeOf)
  decreasing_by all_goals subst_vars; decreasing_tactic

def LSeq.cutS : (D : SSeq Γ A) → (E : LSeq (Γ.cons A) Δ C) → LSeq Γ Δ C
  | D@(.andR D₁ _), .andL₁ .here E => LSeq.cutS D₁ (LSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D@(.andR _ D₂), .andL₂ .here E => LSeq.cutS D₂ (LSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D@(.orR₁ D₁), .orL .here E₁ _ => LSeq.cutS D₁ (LSeq.cutS (D.substS .weakening) (E₁.substS .exchange))
  | D@(.orR₂ D₂), .orL .here _ E₂ => LSeq.cutS D₂ (LSeq.cutS (D.substS .weakening) (E₂.substS .exchange))
  | D@(.impR D₂), .impL .here E₁ E₂ => LSeq.cutS (SSeq.cutS (SSeq.cutS D E₁) D₂) (LSeq.cutS (D.substS .weakening) (E₂.substS .exchange))
  | D@(.upR D₁), .upL .here E => LSeq.cutL .triv₂ D₁ (LSeq.cutS D E)

  | .falseL u, _ => .falseL u
  | .andL₁ u D, E => .andL₁ u (LSeq.cutS D (E.substS (.lift .weakening)))
  | .andL₂ u D, E => .andL₂ u (LSeq.cutS D (E.substS (.lift .weakening)))
  | .orL u D₁ D₂, E => .orL u (LSeq.cutS D₁ (E.substS (.lift .weakening))) (LSeq.cutS D₂ (E.substS (.lift .weakening)))
  | .impL u D₁ D₂, E => .impL u D₁ (LSeq.cutS D₂ (E.substS (.lift .weakening)))

  | _, .id => .id
  | _, .oneR => .oneR
  | D, .oneL s E => .oneL s (LSeq.cutS D E)
  | _, .zeroL s => .zeroL s
  | _, .topR => .topR
  | D, .tensorR s E₁ E₂ => .tensorR s (LSeq.cutS D E₁) (LSeq.cutS D E₂)
  | D, .tensorL s E => .tensorL s (LSeq.cutS D E)
  | D, .plusR₁ E => .plusR₁ (LSeq.cutS D E)
  | D, .plusR₂ E => .plusR₂ (LSeq.cutS D E)
  | D, .plusL s E₁ E₂ => .plusL s (LSeq.cutS D E₁) (LSeq.cutS D E₂)
  | D, .withR E₁ E₂ => .withR (LSeq.cutS D E₁) (LSeq.cutS D E₂)
  | D, .withL₁ s E => .withL₁ s (LSeq.cutS D E)
  | D, .withL₂ s E => .withL₂ s (LSeq.cutS D E)
  | D, .lolliR E => .lolliR (LSeq.cutS D E)
  | D, .lolliL s s' E₁ E₂ => .lolliL s s' (LSeq.cutS D E₁) (LSeq.cutS D E₂)
  | D, .downR E => .downR (SSeq.cutS D E)
  | D, .downL s E => .downL s (LSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | _, .falseL (.there u) => .falseL u
  | D, .andL₁ (.there u) E => .andL₁ u (LSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D, .andL₂ (.there u) E => .andL₂ u (LSeq.cutS (D.substS .weakening) (E.substS .exchange))
  | D, .orL (.there u) E₁ E₂ => .orL u (LSeq.cutS (D.substS .weakening) (E₁.substS .exchange)) (LSeq.cutS (D.substS .weakening) (E₂.substS .exchange))
  | D, .impL (.there u) E₁ E₂ => .impL u (SSeq.cutS D E₁) (LSeq.cutS (D.substS .weakening) (E₂.substS .exchange))
  | D, .upL (.there u) E => .upL u (LSeq.cutS D E)

  termination_by D E => (sizeOf A, D.sizeOf, E.sizeOf)
  decreasing_by all_goals subst_vars; decreasing_tactic

def LSeq.cutL (s : Split Δ Δ₁ Δ₂) : (D : LSeq Γ Δ₁ A) → (E : LSeq Γ (Δ₂.cons A) C) → LSeq Γ Δ C
  | .id, .id => let .refl _ := s.eq_triv₁; .id

  | .oneR, .oneL .here E => let .refl _ := s.eq_triv₂; E
  | .tensorR s' D₁ D₂, .tensorL .here E => let ⟨s, s'⟩ := s.shift s'; LSeq.cutL s D₁ (LSeq.cutL s'.cons₂ D₂ E)
  | .plusR₁ D, .plusL .here E₁ _ => LSeq.cutL s D E₁
  | .plusR₂ D, .plusL .here _ E₂ => LSeq.cutL s D E₂
  | .withR D₁ _, .withL₁ .here E => LSeq.cutL s D₁ E
  | .withR _ D₂, .withL₂ .here E => LSeq.cutL s D₂ E
  | .lolliR D, .lolliL .here s' E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift s'.flip; LSeq.cutL s.flip (LSeq.cutL s' E₁ D) E₂
  | .downR D, .downL .here E => let .refl _ := s.eq_triv₂; LSeq.cutS D E

  | .oneL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; .oneL s (LSeq.cutL s' D E)
  | .zeroL s', _ => let ⟨s, _⟩ := s.shift₁ s'; .zeroL s
  | .tensorL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; .tensorL s (LSeq.cutL s'.cons₁.cons₁ D E)
  | .plusL s' D₁ D₂, E => let ⟨s, s'⟩ := s.shift₁ s'; .plusL s (LSeq.cutL s'.cons₁ D₁ E) (LSeq.cutL s'.cons₁ D₂ E)
  | .withL₁ s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; .withL₁ s (LSeq.cutL s'.cons₁ D E)
  | .withL₂ s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; .withL₂ s (LSeq.cutL s'.cons₁ D E)
  | .lolliL s' s'' D₁ D₂, E => let ⟨s, s'⟩ := s.shift₁ s'; let ⟨s', s''⟩ := s'.shift s''; .lolliL s s' D₁ (LSeq.cutL s''.cons₁ D₂ E)
  | .downL s' D, E => let ⟨s, s'⟩ := s.shift₁ s'; .downL s (LSeq.cutL s' D (E.substS .weakening))
  | .falseL u, _ => .falseL u
  | .andL₁ u D, E => .andL₁ u (LSeq.cutL s D (E.substS .weakening))
  | .andL₂ u D, E => .andL₂ u (LSeq.cutL s D (E.substS .weakening))
  | .orL u D₁ D₂, E => .orL u (LSeq.cutL s D₁ (E.substS .weakening)) (LSeq.cutL s D₂ (E.substS .weakening))
  | .impL u D₁ D₂, E => .impL u D₁ (LSeq.cutL s D₂ (E.substS .weakening))
  | .upL u D, E => .upL u (LSeq.cutL s.cons₁ D E)

  | D, LSeq.oneL (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; .oneL s (LSeq.cutL s'.flip D E)
  | _, .zeroL (.there s') => let ⟨s, _⟩ := s.flip.shift₁ s'; .zeroL s
  | _, .topR => .topR
  | D, .tensorR (.cons₁ s') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift s'.flip; .tensorR s.flip (LSeq.cutL s'.flip D E₁) E₂
  | D, .tensorR (.cons₂ s') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift s'; .tensorR s E₁ (LSeq.cutL s'.flip D E₂)
  | D, LSeq.tensorL (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; .tensorL s (LSeq.cutL s'.flip.cons₂.cons₂ D (E.substL .exchange₂))
  | D, .plusR₁ E => .plusR₁ (LSeq.cutL s D E)
  | D, .plusR₂ E => .plusR₂ (LSeq.cutL s D E)
  | D, LSeq.plusL (.there s') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift₁ s'; .plusL s (LSeq.cutL s'.flip.cons₂ D (E₁.substL .exchange)) (LSeq.cutL s'.flip.cons₂ D (E₂.substL .exchange))
  | D, .withR E₁ E₂ => .withR (LSeq.cutL s D E₁) (LSeq.cutL s D E₂)
  | D, LSeq.withL₁ (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; .withL₁ s (LSeq.cutL s'.flip.cons₂ D (E.substL .exchange))
  | D, LSeq.withL₂ (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; .withL₂ s (LSeq.cutL s'.flip.cons₂ D (E.substL .exchange))
  | D, .lolliR E => .lolliR (LSeq.cutL s.cons₂ D (E.substL .exchange))
  | D, LSeq.lolliL (.there s') (.cons₁ s'') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift₁ s'; let ⟨s', s''⟩ := s'.shift s''.flip; .lolliL s s'.flip (LSeq.cutL s''.flip D E₁) E₂
  | D, LSeq.lolliL (.there s') (.cons₂ s'') E₁ E₂ => let ⟨s, s'⟩ := s.flip.shift₁ s'; let ⟨s', s''⟩ := s'.shift s''; .lolliL s s' E₁ (LSeq.cutL s''.flip.cons₂ D (E₂.substL .exchange))
  | D, LSeq.downL (.there s') E => let ⟨s, s'⟩ := s.flip.shift₁ s'; .downL s (LSeq.cutL s'.flip (D.substS .weakening) E)
  | _, .falseL u => .falseL u
  | D, .andL₁ u E => .andL₁ u (LSeq.cutL s (D.substS .weakening) E)
  | D, .andL₂ u E => .andL₂ u (LSeq.cutL s (D.substS .weakening) E)
  | D, .orL u E₁ E₂ => .orL u (LSeq.cutL s (D.substS .weakening) E₁) (LSeq.cutL s (D.substS .weakening) E₂)
  | D, .impL u E₁ E₂ => .impL u E₁ (LSeq.cutL s (D.substS .weakening) E₂)
  | D, .upL u E => .upL u (LSeq.cutL s.cons₂ D (E.substL .exchange))

  termination_by D E => (sizeOf A, D.sizeOf, E.sizeOf)

end

instance SSeq.seqJudge : SeqSJudge SSeq where
  cutSS γ u D := cutS (γ u) (D γ.weaken .here)
  cutSL γ u D := .cutS (γ u) (D γ.weaken .here)

instance LSeq.seqJudge : SeqLJudge LSeq where
  judge.hyp := id'
  cutL s D' D := cutL s D' (D .here)
  weaken := substS .weakening

mutual

def SSeq.toVerif : (D : SSeq Γ A) → VU.SVerif Γ A
  | .id u => .uv (.hyp u)
  | .trueR => .trueI
  | .falseL u => .falseE (.hyp u)
  | .andR D₁ D₂ => .andI D₁.toVerif D₂.toVerif
  | .andL₁ u D => D.toVerif.substS (.mk (VU.SUse.andE₁ (.hyp u)))
  | .andL₂ u D => D.toVerif.substS (.mk (VU.SUse.andE₂ (.hyp u)))
  | .orR₁ D => .orI₁ D.toVerif
  | .orR₂ D => .orI₂ D.toVerif
  | .orL u D₁ D₂ => .orE (.hyp u) D₁.toVerif D₂.toVerif
  | .impR D => .impI D.toVerif
  | .impL u D₁ D₂ => D₂.toVerif.substS (.mk (VU.SUse.impE (.hyp u) D₁.toVerif))
  | .upR D => .upI D.toVerif

def LSeq.toVerif : (D : LSeq Γ Δ A) → VU.LVerif Γ Δ A
  | .id => .uv .hyp
  | .oneR => .oneI
  | .oneL s D => .oneE s.toSplit .hyp D.toVerif
  | .zeroL s => .zeroE s.toSplit .hyp
  | .topR => .topI
  | .tensorR s D₁ D₂ => .tensorI s D₁.toVerif D₂.toVerif
  | .tensorL s D => .tensorE s.toSplit .hyp D.toVerif
  | .plusR₁ D => .plusI₁ D.toVerif
  | .plusR₂ D => .plusI₂ D.toVerif
  | .plusL s D₁ D₂ => .plusE s.toSplit .hyp D₁.toVerif D₂.toVerif
  | .withR D₁ D₂ => .withI D₁.toVerif D₂.toVerif
  | .withL₁ s D => D.toVerif.substL (.cons s.toSplit (.withE₁ .hyp) .id)
  | .withL₂ s D => D.toVerif.substL (.cons s.toSplit (.withE₂ .hyp) .id)
  | .lolliR D => .lolliI D.toVerif
  | .lolliL s s' D₁ D₂ => let ⟨s, s'⟩ := s.toSplit.flip.shift s'.flip; D₂.toVerif.substL (.cons s.flip (.lolliE s'.flip .hyp D₁.toVerif) .id)
  | .downR D => .downI D.toVerif
  | .downL s D => .downE s.toSplit .hyp D.toVerif
  | .falseL u => .falseE (.hyp u)
  | .andL₁ u D => D.toVerif.substS (.mk (VU.SUse.andE₁ (.hyp u)))
  | .andL₂ u D => D.toVerif.substS (.mk (VU.SUse.andE₂ (.hyp u)))
  | .orL u D₁ D₂ => .orE (.hyp u) D₁.toVerif D₂.toVerif
  | .impL u D₁ D₂ => D₂.toVerif.substS (.mk (VU.SUse.impE (.hyp u) D₁.toVerif))
  | .upL u D => D.toVerif.substL (.cons .triv₂ (.upE (.hyp u)) .id)

end

end SC

mutual

def ND.STrue.toSeq : (D : STrue Γ A) → SC.SSeq Γ A
  | .hyp u => .id' u
  | .trueI => .trueR
  | .falseE D => .cutS D.toSeq (.falseL .here)
  | .andI D₁ D₂ => .andR D₁.toSeq D₂.toSeq
  | .andE₁ D => .cutS D.toSeq (.andL₁ .here (.id' .here))
  | .andE₂ D => .cutS D.toSeq (.andL₂ .here (.id' .here))
  | .orI₁ D => .orR₁ D.toSeq
  | .orI₂ D => .orR₂ D.toSeq
  | .orE D D₁ D₂ => .cutS D.toSeq (.orL .here (D₁.toSeq.substS (.lift .weakening)) (D₂.toSeq.substS (.lift .weakening)))
  | .impI D => .impR D.toSeq
  | .impE D D₁ => .cutS D.toSeq (.impL .here (D₁.toSeq.substS .weakening) (.id' .here))
  | .upI D => .upR D.toSeq

def ND.LTrue.toSeq : (D : LTrue Γ Δ A) → SC.LSeq Γ Δ A
  | .hyp => .id'
  | .oneI => .oneR
  | .oneE s D D₁ => .cutL s D.toSeq (.oneL .here D₁.toSeq)
  | .zeroE s D => .cutL s D.toSeq (.zeroL .here)
  | .topI => .topR
  | .tensorI s D₁ D₂ => .tensorR s D₁.toSeq D₂.toSeq
  | .tensorE s D D₁ => .cutL s D.toSeq (.tensorL .here D₁.toSeq)
  | .plusI₁ D => .plusR₁ D.toSeq
  | .plusI₂ D => .plusR₂ D.toSeq
  | .plusE s D D₁ D₂ => .cutL s D.toSeq (.plusL .here D₁.toSeq D₂.toSeq)
  | .withI D₁ D₂ => .withR D₁.toSeq D₂.toSeq
  | .withE₁ D => .cutL .triv₁ D.toSeq (.withL₁ .here .id')
  | .withE₂ D => .cutL .triv₁ D.toSeq (.withL₂ .here .id')
  | .lolliI D => .lolliR D.toSeq
  | .lolliE s D D₁ => .cutL s D.toSeq (.lolliL .here .triv₁ D₁.toSeq .id')
  | .downI D => .downR D.toSeq
  | .downE s D D₁ => .cutL s D.toSeq (.downL .here D₁.toSeq)
  | .falseE D => .cutS D.toSeq (.falseL .here)
  | .orE D D₁ D₂ => .cutS D.toSeq (.orL .here (D₁.toSeq.substS (.lift .weakening)) (D₂.toSeq.substS (.lift .weakening)))
  | .upE D => .cutS D.toSeq (.upL .here .id')

end

def VU.SVerif.substS' (γ : SSubst SVerif Γ Γ') (D : SVerif Γ A) : SVerif Γ' A :=
  (D.toTrue.toSeq.substS (γ.map ⟨fun D => D.toTrue.toSeq⟩)).toVerif

def VU.LVerif.substS' (γ : SSubst SVerif Γ Γ') (D : LVerif Γ Δ A) : LVerif Γ' Δ A :=
  (D.toTrue.toSeq.substS (γ.map ⟨fun D => D.toTrue.toSeq⟩)).toVerif

def VU.LVerif.substL' (δ : LSubst (LVerif Γ) Δ Δ') (D : LVerif Γ Δ A) : LVerif Γ Δ' A :=
  (D.toTrue.toSeq.substL (δ.map fun D => D.toTrue.toSeq)).toVerif
