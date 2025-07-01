import Lambda.Util

namespace Lambda.PSF.Basic

inductive Typ
  | zero
  | one
  | plus (A₁ A₂ : Typ)
  | times (A₁ A₂ : Typ)
  | arr (A₁ A₂ : Typ)

scoped notation "𝟬" => Typ.zero
scoped notation "𝟭" => Typ.one
scoped infix:65 " + " => Typ.plus
scoped infix:35 " × " => Typ.times
scoped infix:25 " ⟶ " => Typ.arr

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Typ)

scoped infixr:67 " ∷ " => Ctx.cons

using scoped infix:50 " ∋ " => Var
inductive Var : (Γ : Ctx) → (A : Typ) → Type
  | zero : Γ ∷ A ∋ A
  | succ (x : Γ ∋ A) : Γ ∷ A' ∋ A

using scoped infix:20 " ⊢ " => Term
inductive Term : (Γ : Ctx) → (A : Typ) → Type
  | var (x : Γ ∋ A) : Γ ⊢ A
  | absurd (M : Γ ⊢ 𝟬) : Γ ⊢ A
  | triv : Γ ⊢ 𝟭
  | inl (M : Γ ⊢ A₁) : Γ ⊢ A₁ + A₂
  | inr (M : Γ ⊢ A₂) : Γ ⊢ A₁ + A₂
  | case (M : Γ ⊢ A₁ + A₂) (M₁ : Γ ∷ A₁ ⊢ A) (M₂ : Γ ∷ A₂ ⊢ A) : Γ ⊢ A
  | pair (M₁ : Γ ⊢ A₁) (M₂ : Γ ⊢ A₂) : Γ ⊢ A₁ × A₂
  | fst (M : Γ ⊢ A₁ × A₂) : Γ ⊢ A₁
  | snd (M : Γ ⊢ A₁ × A₂) : Γ ⊢ A₂
  | lam (M : Γ ∷ A₁ ⊢ A₂) : Γ ⊢ A₁ ⟶ A₂
  | app (M : Γ ⊢ A₁ ⟶ A₂) (M₁ : Γ ⊢ A₁) : Γ ⊢ A₂

/-
section Function

def Subst (J : (Γ : Ctx) → (A : Typ) → Type) (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (M : Var Γ' A) → J Γ A

class JudgeTrans (J J' : (Γ : Ctx) → (A : Typ) → Type) where
  transform (M : J Γ A) : J' Γ A

instance JudgeTrans.id : JudgeTrans J J where
  transform M := M

instance Term.judgeTransVar : JudgeTrans Var Term where
  transform := var

class Judge (J) extends JudgeTrans Var J where
  weaken (M : J Γ A) : J (Γ ∷ A') A

instance Var.judge : Judge Var where
  weaken := succ

def Subst.lift [j : Judge J] (γ : Subst J Γ Γ') : Subst J (Γ ∷ A) (Γ' ∷ A)
  | _, .zero => j.transform .zero
  | _, .succ x => j.weaken (γ x)

def Term.subst [j : Judge J] [jt : JudgeTrans J Term] (γ : Subst J Γ Γ') : (M : Term Γ' A) → Term Γ A
  | var x => jt.transform (γ x)
  | absurd M => absurd (M.subst γ)
  | triv => triv
  | inl M => inl (M.subst γ)
  | inr M => inr (M.subst γ)
  | case M M₁ M₂ => case (M.subst γ) (M₁.subst γ.lift) (M₂.subst γ.lift)
  | pair M₁ M₂ => pair (M₁.subst γ) (M₂.subst γ)
  | fst M => fst (M.subst γ)
  | snd M => snd (M.subst γ)
  | lam M => lam (M.subst γ.lift)
  | app M M₁ => app (M.subst γ) (M₁.subst γ)

instance Term.judge : Judge Term where
  weaken := subst fun _ => Var.succ

theorem Term.subst_subst₁ [j : Judge J] [jt : JudgeTrans J Term] (γ₁ : Subst Var Γ' Γ'') (γ₂ : Subst J Γ Γ') (M : Term Γ'' A) : subst γ₂ (subst γ₁ M) = subst (fun _ x => γ₂ (γ₁ x)) M :=
  by induction M generalizing Γ Γ' <;> simp! only [*] <;> congr <;> funext _ x <;> cases x <;> rfl

theorem Term.subst_subst₂ (γ₁ : Subst Term Γ' Γ'') (γ₂ : Subst Var Γ Γ') (M : Term Γ'' A) : subst γ₂ (subst γ₁ M) = subst (fun _ x => (γ₁ x).subst γ₂) M :=
  by induction M generalizing Γ Γ' <;> simp! only [*] <;> congr <;> funext _ x <;> cases x <;> simp! only [JudgeTrans.id, Var.judge, judge, subst_subst₁]

theorem Term.subst_subst₃ (γ₁ : Subst Term Γ' Γ'') (γ₂ : Subst Term Γ Γ') (M : Term Γ'' A) : subst γ₂ (subst γ₁ M) = subst (fun _ x => (γ₁ x).subst γ₂) M :=
  by induction M generalizing Γ Γ' <;> simp! only [*] <;> congr <;> funext _ x <;> cases x <;> simp! only [JudgeTrans.id, judge, subst_subst₁, subst_subst₂₁]

end Function
--/

/-
section Inductive

inductive Subst (J : (Γ : Ctx) → (A : Typ) → Type) (Γ : Ctx) : (Γ' : Ctx) → Type
  | nil : Subst J Γ .nil
  | cons (γ : Subst J Γ Γ') (M : J Γ A) : Subst J Γ (Γ' ∷ A)

def Var.subst (γ : Subst J Γ Γ') : (x : Var Γ' A) → J Γ A
  | zero => let .cons _ M := γ; M
  | succ x => let .cons γ _ := γ; x.subst γ

class JudgeTrans (J J' : (Γ : Ctx) → (A : Typ) → Type) where
  transform (M : J Γ A) : J' Γ A

instance JudgeTrans.id : JudgeTrans J J where
  transform M := M

instance Term.judgeTransVar : JudgeTrans Var Term where
  transform := var

class Judge (J) extends JudgeTrans Var J where
  weaken (M : J Γ A) : J (Γ ∷ A') A

instance Var.judge : Judge Var where
  weaken := succ

def Subst.weaken [j : Judge J] : (γ : Subst J Γ Γ') → Subst J (Γ ∷ A) Γ'
  | nil => nil
  | cons γ x => γ.weaken.cons (j.weaken x)

def Subst.lift [j : Judge J] (γ : Subst J Γ Γ') : Subst J (Γ ∷ A) (Γ' ∷ A) :=
  γ.weaken.cons (j.transform .zero)

def Subst.id : ∀ {Γ}, Subst Var Γ Γ
  | .nil => nil
  | .cons .. => id.lift

def Term.subst [j : Judge J] [jt : JudgeTrans J Term] (γ : Subst J Γ Γ') : (M : Term Γ' A) → Term Γ A
  | var x => jt.transform (x.subst γ)
  | absurd M => absurd (M.subst γ)
  | triv => triv
  | inl M => inl (M.subst γ)
  | inr M => inr (M.subst γ)
  | case M M₁ M₂ => case (M.subst γ) (M₁.subst γ.lift) (M₂.subst γ.lift)
  | pair M₁ M₂ => pair (M₁.subst γ) (M₂.subst γ)
  | fst M => fst (M.subst γ)
  | snd M => snd (M.subst γ)
  | lam M => lam (M.subst γ.lift)
  | app M M₁ => app (M.subst γ) (M₁.subst γ)

instance Term.judge : Judge Term where
  weaken := subst (.weaken .id)

def Subst.comp (γ₂ : Subst J Γ Γ') : (γ₁ : Subst Var Γ' Γ'') → Subst J Γ Γ''
  | nil => nil
  | cons γ₁ x => (γ₂.comp γ₁).cons (x.subst γ₂)

def Subst.comp' [j : Judge J] [jt : JudgeTrans J Term] (γ₂ : Subst J Γ Γ') : (γ₁ : Subst Term Γ' Γ'') → Subst Term Γ Γ''
  | nil => nil
  | cons γ₁ x => (γ₂.comp' γ₁).cons (x.subst γ₂)

theorem Term.subst_subst₁ (γ₁ : Subst Var Γ' Γ'') (γ₂ : Subst Var Γ Γ') (M : Term Γ'' A) : subst γ₂ (subst γ₁ M) = subst (γ₂.comp γ₁) M :=
  by
    induction M generalizing Γ Γ' <;> simp! only [*]
    . sorry
    all_goals
      congr <;>
      sorry

theorem Term.subst_subst₂ (γ₁ : Subst Var Γ' Γ'') (γ₂ : Subst Term Γ Γ') (M : Term Γ'' A) : subst γ₂ (subst γ₁ M) = subst (γ₂.comp γ₁) M :=
  by
    sorry

theorem Term.subst_subst₃ (γ₁ : Subst Term Γ' Γ'') (γ₂ : Subst Var Γ Γ') (M : Term Γ'' A) : subst γ₂ (subst γ₁ M) = subst (γ₂.comp' γ₁) M :=
  by
    sorry

theorem Term.subst_subst₄ (γ₁ : Subst Term Γ' Γ'') (γ₂ : Subst Term Γ Γ') (M : Term Γ'' A) : subst γ₂ (subst γ₁ M) = subst (γ₂.comp' γ₁) M :=
  by
    sorry

end Inductive
--/
