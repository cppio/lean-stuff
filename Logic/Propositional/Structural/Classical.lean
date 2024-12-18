opaque BasePropn : Type

inductive Propn
  | base (P : BasePropn)
  | true
  | false
  | not (A : Propn)
  | and (A B : Propn)
  | or (A B : Propn)

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Propn)

inductive Hyp (A : Propn) : (Γ : Ctx) → Type
  | here : Hyp A (.cons Γ A)
  | there (u : Hyp A Γ) : Hyp A (Γ.cons B)

def Renaming (Γ Γ' : Ctx) : Type :=
  ∀ ⦃A⦄, (u : Hyp A Γ) → Hyp A Γ'

def Renaming.id : Renaming Γ Γ
  | _, u => u

def Renaming.weakening : Renaming Γ (Γ.cons A)
  | _ => .there

def Renaming.exchange : Renaming (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there u) => u.there.there

def Renaming.lift (γ : Renaming Γ Γ') {A} : Renaming (Γ.cons A) (Γ'.cons A)
  | _, .here => .here
  | _, .there u => (γ u).there

/-! Sequent Calculus -/

namespace SC

inductive Seq : (Γ₁ Γ₂ : Ctx) → Type
  | id (u : Hyp (.base P) Γ₁) (v : Hyp (.base P) Γ₂) : Seq Γ₁ Γ₂
  | trueR (v : Hyp .true Γ₂) : Seq Γ₁ Γ₂
  | falseL (u : Hyp .false Γ₁) : Seq Γ₁ Γ₂
  | notR (v : Hyp A.not Γ₂) (D : Seq (Γ₁.cons A) Γ₂) : Seq Γ₁ Γ₂
  | notL (u : Hyp A.not Γ₁) (D : Seq Γ₁ (Γ₂.cons A)) : Seq Γ₁ Γ₂
  | andR (v : Hyp (A.and B) Γ₂) (D₁ : Seq Γ₁ (Γ₂.cons A)) (D₂ : Seq Γ₁ (Γ₂.cons B)) : Seq Γ₁ Γ₂
  | andL₁ (u : Hyp (A.and B) Γ₁) (D : Seq (Γ₁.cons A) Γ₂) : Seq Γ₁ Γ₂
  | andL₂ (u : Hyp (.and A B) Γ₁) (D : Seq (Γ₁.cons B) Γ₂) : Seq Γ₁ Γ₂
  | orR₁ (v : Hyp (A.or B) Γ₂) (D : Seq Γ₁ (Γ₂.cons A)) : Seq Γ₁ Γ₂
  | orR₂ (v : Hyp (.or A B) Γ₂) (D : Seq Γ₁ (Γ₂.cons B)) : Seq Γ₁ Γ₂
  | orL (u : Hyp (A.or B) Γ₁) (D₁ : Seq (Γ₁.cons A) Γ₂) (D₂ : Seq (Γ₁.cons B) Γ₂) : Seq Γ₁ Γ₂

def Seq.rename (γ₁ : Renaming Γ₁ Γ₁') (γ₂ : Renaming Γ₂ Γ₂') : (D : Seq Γ₁ Γ₂) → Seq Γ₁' Γ₂'
  | id u v => id (γ₁ u) (γ₂ v)
  | trueR v => trueR (γ₂ v)
  | falseL u => falseL (γ₁ u)
  | notR v D => notR (γ₂ v) (D.rename γ₁.lift γ₂)
  | notL u D => notL (γ₁ u) (D.rename γ₁ γ₂.lift)
  | andR v D₁ D₂ => andR (γ₂ v) (D₁.rename γ₁ γ₂.lift) (D₂.rename γ₁ γ₂.lift)
  | andL₁ u D => andL₁ (γ₁ u) (D.rename γ₁.lift γ₂)
  | andL₂ u D => andL₂ (γ₁ u) (D.rename γ₁.lift γ₂)
  | orR₁ v D => orR₁ (γ₂ v) (D.rename γ₁ γ₂.lift)
  | orR₂ v D => orR₂ (γ₂ v) (D.rename γ₁ γ₂.lift)
  | orL u D₁ D₂ => orL (γ₁ u) (D₁.rename γ₁.lift γ₂) (D₂.rename γ₁.lift γ₂)

def Seq.id' (u : Hyp A Γ₁) (v : Hyp A Γ₂) : Seq Γ₁ Γ₂ :=
  match A with
  | .base _ => id u v
  | .true => trueR v
  | .false => falseL u
  | .not _ => notR v (notL u.there (id' .here .here))
  | .and .. => andR v (andL₁ u (id' .here .here)) (andL₂ u (id' .here .here))
  | .or .. => orL u (orR₁ v (id' .here .here)) (orR₂ v (id' .here .here))

@[simp]
def Seq.sizeOf : (D : Seq Γ₁ Γ₂) → Nat
  | id .. | trueR _ | falseL _ => 0
  | notR _ D | notL _ D | andL₁ _ D | andL₂ _ D | orR₁ _ D | orR₂ _ D => D.sizeOf + 1
  | andR _ D₁ D₂ | orL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename (γ₁ : Renaming Γ₁ Γ₁') (γ₂ : Renaming Γ₂ Γ₂') (D : Seq Γ₁ Γ₂) : (D.rename γ₁ γ₂).sizeOf = D.sizeOf :=
  by induction D generalizing Γ₁' Γ₂' <;> simp! only [*]

def Seq.cut : (D : Seq Γ₁ (Γ₂.cons A)) → (E : Seq (Γ₁.cons A) Γ₂) → Seq Γ₁ Γ₂
  | .id u .here, .id .here v => .id u v
  | .id u (.there v), _ => .id u v
  | _, .id (.there u) v => .id u v
  | D@(notR .here D₁), E@(notL .here E₁) => cut (cut (D.rename .id (.lift .weakening)) E₁) (cut D₁ (E.rename (.lift .weakening) .id))
  | D@(andR .here D₁ _), E@(andL₁ .here E₁) => cut (cut (D₁.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₁.rename .exchange .id))
  | D@(andR .here _ D₂), E@(andL₂ .here E₂) => cut (cut (D₂.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₂.rename .exchange .id))
  | D@(orR₁ .here D₁), E@(orL .here E₁ _) => cut (cut (D₁.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₁.rename .exchange .id))
  | D@(orR₂ .here D₂), E@(orL .here _ E₂) => cut (cut (D₂.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₂.rename .exchange .id))
  | trueR (.there v), _ => trueR v
  | falseL u, _ => falseL u
  | notR (.there v) D, E => notR v (cut D (E.rename (.lift .weakening) .id))
  | notL u D, E => notL u (cut (D.rename .id .exchange) (E.rename .id .weakening))
  | andR (.there v) D₁ D₂, E => andR v (cut (D₁.rename .id .exchange) (E.rename .id .weakening)) (cut (D₂.rename .id .exchange) (E.rename .id .weakening))
  | andL₁ u D, E => andL₁ u (cut D (E.rename (.lift .weakening) .id))
  | andL₂ u D, E => andL₂ u (cut D (E.rename (.lift .weakening) .id))
  | orR₁ (.there v) D, E => orR₁ v (cut (D.rename .id .exchange) (E.rename .id .weakening))
  | orR₂ (.there v) D, E => orR₂ v (cut (D.rename .id .exchange) (E.rename .id .weakening))
  | orL u D₁ D₂, E => orL u (cut D₁ (E.rename (.lift .weakening) .id)) (cut D₂ (E.rename (.lift .weakening) .id))
  | _, trueR v => trueR v
  | _, falseL (.there u) => falseL u
  | D, notR v E => notR v (cut (D.rename .weakening .id) (E.rename .exchange .id))
  | D, notL (.there u) E => notL u (cut (D.rename .id (.lift .weakening)) E)
  | D, andR v E₁ E₂ => andR v (cut (D.rename .id (.lift .weakening)) E₁) (cut (D.rename .id (.lift .weakening)) E₂)
  | D, andL₁ (.there u) E => andL₁ u (cut (D.rename .weakening .id) (E.rename .exchange .id))
  | D, andL₂ (.there u) E => andL₂ u (cut (D.rename .weakening .id) (E.rename .exchange .id))
  | D, orR₁ v E => orR₁ v (cut (D.rename .id (.lift .weakening)) E)
  | D, orR₂ v E => orR₂ v (cut (D.rename .id (.lift .weakening)) E)
  | D, orL (.there u) E₁ E₂ => orL u (cut (D.rename .weakening .id) (E₁.rename .exchange .id)) (cut (D.rename .weakening .id) (E₂.rename .exchange .id))
  termination_by D E => (A, D.sizeOf, E.sizeOf)
  decreasing_by all_goals subst_vars; decreasing_tactic

end SC
