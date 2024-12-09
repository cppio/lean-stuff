namespace Logic.Propositional.Structural.Classical

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

def Rename (Γ Γ' : Ctx) : Type :=
  ∀ ⦃A⦄, (u : Hyp A Γ) → Hyp A Γ'

def Rename.id : Rename Γ Γ
  | _, u => u

def Rename.weakening : Rename Γ (Γ.cons A)
  | _ => .there

def Rename.contraction (u : Hyp A Γ) : Rename (Γ.cons A) Γ
  | _, .here => u
  | _, .there u => u

def Rename.exchange : Rename (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there u) => u.there.there

def Rename.lift (γ : Rename Γ Γ') {A} : Rename (Γ.cons A) (Γ'.cons A)
  | _, .here => .here
  | _, .there u => (γ u).there

-- Sequent Calculus
namespace SC

inductive Seq : (Γ : Ctx) → (Δ : Ctx) → Type
  | id (u : Hyp (.base P) Γ) (v : Hyp (.base P) Δ) : Seq Γ Δ
  | trueR (v : Hyp .true Δ) : Seq Γ Δ
  | falseL (u : Hyp .false Γ) : Seq Γ Δ
  | notR (v : Hyp A.not Δ) (D : Seq (Γ.cons A) Δ) : Seq Γ Δ
  | notL (u : Hyp A.not Γ) (D : Seq Γ (Δ.cons A)) : Seq Γ Δ
  | andR (v : Hyp (A.and B) Δ) (D₁ : Seq Γ (Δ.cons A)) (D₂ : Seq Γ (Δ.cons B)) : Seq Γ Δ
  | andL₁ (u : Hyp (A.and B) Γ) (D : Seq (Γ.cons A) Δ) : Seq Γ Δ
  | andL₂ (u : Hyp (.and A B) Γ) (D : Seq (Γ.cons B) Δ) : Seq Γ Δ
  | orR₁ (v : Hyp (A.or B) Δ) (D : Seq Γ (Δ.cons A)) : Seq Γ Δ
  | orR₂ (v : Hyp (.or A B) Δ) (D : Seq Γ (Δ.cons B)) : Seq Γ Δ
  | orL (u : Hyp (A.or B) Γ) (D₁ : Seq (Γ.cons A) Δ) (D₂ : Seq (Γ.cons B) Δ) : Seq Γ Δ

def Seq.rename (γ : Rename Γ Γ') (δ : Rename Δ Δ') : (D : Seq Γ Δ) → Seq Γ' Δ'
  | id u v => id (γ u) (δ v)
  | trueR v => trueR (δ v)
  | falseL u => falseL (γ u)
  | notR v D => notR (δ v) (D.rename γ.lift δ)
  | notL u D => notL (γ u) (D.rename γ δ.lift)
  | andR v D₁ D₂ => andR (δ v) (D₁.rename γ δ.lift) (D₂.rename γ δ.lift)
  | andL₁ u D => andL₁ (γ u) (D.rename γ.lift δ)
  | andL₂ u D => andL₂ (γ u) (D.rename γ.lift δ)
  | orR₁ v D => orR₁ (δ v) (D.rename γ δ.lift)
  | orR₂ v D => orR₂ (δ v) (D.rename γ δ.lift)
  | orL u D₁ D₂ => orL (γ u) (D₁.rename γ.lift δ) (D₂.rename γ.lift δ)

def Seq.id' (u : Hyp A Γ) (v : Hyp A Δ) : Seq Γ Δ :=
  match A with
  | .base _ => id u v
  | .true => trueR v
  | .false => falseL u
  | .not _ => notR v (notL u.there (id' .here .here))
  | .and .. => andR v (andL₁ u (id' .here .here)) (andL₂ u (id' .here .here))
  | .or .. => orL u (orR₁ v (id' .here .here)) (orR₂ v (id' .here .here))

@[simp]
def Seq.sizeOf : (D : Seq Γ A) → Nat
  | id .. | trueR _ | falseL _ => 0
  | notR _ D | notL _ D | andL₁ _ D | andL₂ _ D | orR₁ _ D | orR₂ _ D => D.sizeOf + 1
  | andR _ D₁ D₂ | orL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename (γ : Rename Γ Γ') (δ : Rename Δ Δ') (D : Seq Γ Δ) : (D.rename γ δ).sizeOf = D.sizeOf :=
  by induction D generalizing Γ' Δ' <;> simp! only [*]

def Seq.cut : (D : Seq Γ (Δ.cons A)) → (E : Seq (Γ.cons A) Δ) → Seq Γ Δ
  | .id u .here, E => E.rename (.contraction u) .id
  | .id u (.there v), _ => .id u v
  | D, .id .here v => D.rename .id (.contraction v)
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
