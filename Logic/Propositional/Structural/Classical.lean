import Logic.Propositional.Structural

namespace Logic.Propositional.Structural.Classical

opaque BasePropn : Type

inductive Propn
  | base (P : BasePropn)
  | true
  | false
  | not (A : Propn)
  | and (A B : Propn)
  | or (A B : Propn)

local notation "Ctx" => Ctx (Propn := Propn)

/-! Sequent Calculus -/

namespace SC

inductive Seq : (Γ₁ Γ₂ : Ctx) → Type
  | id (u : Hyp Γ₁ (.base P)) (v : Hyp Γ₂ (.base P)) : Seq Γ₁ Γ₂
  | trueR (v : Hyp Γ₂ .true) : Seq Γ₁ Γ₂
  | falseL (u : Hyp Γ₁ .false) : Seq Γ₁ Γ₂
  | notR (v : Hyp Γ₂ A.not) (D : Seq (Γ₁.cons A) Γ₂) : Seq Γ₁ Γ₂
  | notL (u : Hyp Γ₁ A.not) (D : Seq Γ₁ (Γ₂.cons A)) : Seq Γ₁ Γ₂
  | andR (v : Hyp Γ₂ (A.and B)) (D₁ : Seq Γ₁ (Γ₂.cons A)) (D₂ : Seq Γ₁ (Γ₂.cons B)) : Seq Γ₁ Γ₂
  | andL₁ (u : Hyp Γ₁ (A.and B)) (D : Seq (Γ₁.cons A) Γ₂) : Seq Γ₁ Γ₂
  | andL₂ (u : Hyp Γ₁ (.and A B)) (D : Seq (Γ₁.cons B) Γ₂) : Seq Γ₁ Γ₂
  | orR₁ (v : Hyp Γ₂ (A.or B)) (D : Seq Γ₁ (Γ₂.cons A)) : Seq Γ₁ Γ₂
  | orR₂ (v : Hyp Γ₂ (.or A B)) (D : Seq Γ₁ (Γ₂.cons B)) : Seq Γ₁ Γ₂
  | orL (u : Hyp Γ₁ (A.or B)) (D₁ : Seq (Γ₁.cons A) Γ₂) (D₂ : Seq (Γ₁.cons B) Γ₂) : Seq Γ₁ Γ₂

def Seq.subst (γ₁ : Subst Hyp Γ₁ Γ₁') (γ₂ : Subst Hyp Γ₂ Γ₂') : (D : Seq Γ₁ Γ₂) → Seq Γ₁' Γ₂'
  | id u v => id (γ₁ u) (γ₂ v)
  | trueR v => trueR (γ₂ v)
  | falseL u => falseL (γ₁ u)
  | notR v D => notR (γ₂ v) (D.subst γ₁.lift γ₂)
  | notL u D => notL (γ₁ u) (D.subst γ₁ γ₂.lift)
  | andR v D₁ D₂ => andR (γ₂ v) (D₁.subst γ₁ γ₂.lift) (D₂.subst γ₁ γ₂.lift)
  | andL₁ u D => andL₁ (γ₁ u) (D.subst γ₁.lift γ₂)
  | andL₂ u D => andL₂ (γ₁ u) (D.subst γ₁.lift γ₂)
  | orR₁ v D => orR₁ (γ₂ v) (D.subst γ₁ γ₂.lift)
  | orR₂ v D => orR₂ (γ₂ v) (D.subst γ₁ γ₂.lift)
  | orL u D₁ D₂ => orL (γ₁ u) (D₁.subst γ₁.lift γ₂) (D₂.subst γ₁.lift γ₂)

def Seq.id' (u : Hyp Γ₁ A) (v : Hyp Γ₂ A) : Seq Γ₁ Γ₂ :=
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
theorem Seq.sizeOf_subst (γ₁ : Subst Hyp Γ₁ Γ₁') (γ₂ : Subst Hyp Γ₂ Γ₂') (D : Seq Γ₁ Γ₂) : (D.subst γ₁ γ₂).sizeOf = D.sizeOf :=
  by induction D generalizing Γ₁' Γ₂' <;> simp! only [*]

def Seq.cut : (D : Seq Γ₁ (Γ₂.cons A)) → (E : Seq (Γ₁.cons A) Γ₂) → Seq Γ₁ Γ₂
  | .id u .here, .id .here v => .id u v
  | .id u (.there v), _ => .id u v
  | _, .id (.there u) v => .id u v
  | D@(notR .here D₁), E@(notL .here E₁) => cut (cut (D.subst .id (.lift .weakening)) E₁) (cut D₁ (E.subst (.lift .weakening) .id))
  | D@(andR .here D₁ _), E@(andL₁ .here E₁) => cut (cut (D₁.subst .id .exchange) (E.subst .id .weakening)) (cut (D.subst .weakening .id) (E₁.subst .exchange .id))
  | D@(andR .here _ D₂), E@(andL₂ .here E₂) => cut (cut (D₂.subst .id .exchange) (E.subst .id .weakening)) (cut (D.subst .weakening .id) (E₂.subst .exchange .id))
  | D@(orR₁ .here D₁), E@(orL .here E₁ _) => cut (cut (D₁.subst .id .exchange) (E.subst .id .weakening)) (cut (D.subst .weakening .id) (E₁.subst .exchange .id))
  | D@(orR₂ .here D₂), E@(orL .here _ E₂) => cut (cut (D₂.subst .id .exchange) (E.subst .id .weakening)) (cut (D.subst .weakening .id) (E₂.subst .exchange .id))
  | trueR (.there v), _ => trueR v
  | falseL u, _ => falseL u
  | notR (.there v) D, E => notR v (cut D (E.subst (.lift .weakening) .id))
  | notL u D, E => notL u (cut (D.subst .id .exchange) (E.subst .id .weakening))
  | andR (.there v) D₁ D₂, E => andR v (cut (D₁.subst .id .exchange) (E.subst .id .weakening)) (cut (D₂.subst .id .exchange) (E.subst .id .weakening))
  | andL₁ u D, E => andL₁ u (cut D (E.subst (.lift .weakening) .id))
  | andL₂ u D, E => andL₂ u (cut D (E.subst (.lift .weakening) .id))
  | orR₁ (.there v) D, E => orR₁ v (cut (D.subst .id .exchange) (E.subst .id .weakening))
  | orR₂ (.there v) D, E => orR₂ v (cut (D.subst .id .exchange) (E.subst .id .weakening))
  | orL u D₁ D₂, E => orL u (cut D₁ (E.subst (.lift .weakening) .id)) (cut D₂ (E.subst (.lift .weakening) .id))
  | _, trueR v => trueR v
  | _, falseL (.there u) => falseL u
  | D, notR v E => notR v (cut (D.subst .weakening .id) (E.subst .exchange .id))
  | D, notL (.there u) E => notL u (cut (D.subst .id (.lift .weakening)) E)
  | D, andR v E₁ E₂ => andR v (cut (D.subst .id (.lift .weakening)) E₁) (cut (D.subst .id (.lift .weakening)) E₂)
  | D, andL₁ (.there u) E => andL₁ u (cut (D.subst .weakening .id) (E.subst .exchange .id))
  | D, andL₂ (.there u) E => andL₂ u (cut (D.subst .weakening .id) (E.subst .exchange .id))
  | D, orR₁ v E => orR₁ v (cut (D.subst .id (.lift .weakening)) E)
  | D, orR₂ v E => orR₂ v (cut (D.subst .id (.lift .weakening)) E)
  | D, orL (.there u) E₁ E₂ => orL u (cut (D.subst .weakening .id) (E₁.subst .exchange .id)) (cut (D.subst .weakening .id) (E₂.subst .exchange .id))
  termination_by D E => (A, D.sizeOf, E.sizeOf)
  decreasing_by all_goals subst_vars; decreasing_tactic

end SC
