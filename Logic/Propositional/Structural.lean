namespace Logic.Propositional.Structural

opaque BasePropn : Type

variable {Propn : Type}

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Propn)

local notation "Ctx" => Ctx (Propn := Propn)

inductive Hyp : (Γ : Ctx) → (A : Propn) → Type
  | here : Hyp (.cons Γ A) A
  | there (u : Hyp Γ A) : Hyp (Γ.cons B) A

local notation "Hyp" => Hyp (Propn := Propn)

def Subst (J : (Γ : Ctx) → (A : Propn) → Type) (Γ Γ' : Ctx) : Type :=
  ∀ ⦃A⦄, (u : Hyp Γ A) → J Γ' A

local notation "Subst" => Subst (Propn := Propn)

def Subst.id : Subst Hyp Γ Γ
  | _, u => u

def Subst.weakening : Subst Hyp Γ (Γ.cons A)
  | _ => .there

def Subst.exchange : Subst Hyp (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there u) => u.there.there

class JudgeTrans (J J' : (Γ : Ctx) → (A : Propn) → Type) where
  transform (D : J Γ A) : J' Γ A

local notation "JudgeTrans" => JudgeTrans (Propn := Propn)

instance JudgeTrans.id : JudgeTrans J J where
  transform D := D

def Subst.mk [jt : JudgeTrans Hyp J] (D : J Γ A) : Subst J (Γ.cons A) Γ
  | _, .here => D
  | _, .there u => jt.transform u

def Subst.map (jt : JudgeTrans J J') (γ : Subst J Γ Γ') : Subst J' Γ Γ'
  | _, u => jt.transform (γ u)

class Judge (J) extends JudgeTrans Hyp J where
  rename (γ : Subst Hyp Γ Γ') {A} (D : J Γ A) : J Γ' A

instance Hyp.judge : Judge Hyp where
  rename γ := @γ

def Subst.weaken [j : Judge J] (γ : Subst J Γ Γ') : Subst J Γ (Γ'.cons A)
  | _, u => j.rename .weakening (γ u)

def Subst.lift [j : Judge J] (γ : Subst J Γ Γ') : Subst J (Γ.cons A) (Γ'.cons A)
  | _, .here => j.transform .here
  | _, .there u => γ.weaken u
