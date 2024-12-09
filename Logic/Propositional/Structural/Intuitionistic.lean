namespace Logic.Propositional.Structural.Intuitionistic

opaque BasePropn : Type

inductive Propn
  | base (P : BasePropn)
  | true
  | false
  | and (A B : Propn)
  | or (A B : Propn)
  | imp (A B : Propn)

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Propn)

def Ctx.append (Γ : Ctx) : (Γ' : Ctx) → Ctx
  | nil => Γ
  | cons Γ' A => (Γ.append Γ').cons A

inductive Hyp : (Γ : Ctx) → (A : Propn) → Type
  | here : Hyp (.cons Γ A) A
  | there (u : Hyp Γ A) : Hyp (Γ.cons B) A

def Subst (J : (Γ : Ctx) → (A : Propn) → Type) (Γ Γ' : Ctx) : Type :=
  ∀ ⦃A⦄, (u : Hyp Γ A) → J Γ' A

def Subst.weakening : Subst Hyp Γ (Γ.cons A)
  | _ => .there

def Subst.contraction (u : Hyp Γ A) : Subst Hyp (Γ.cons A) Γ
  | _, .here => u
  | _, .there u => u

def Subst.exchange : Subst Hyp (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there u) => u.there.there

def Subst.append₁ : ∀ {Γ'}, Subst Hyp Γ (Γ.append Γ')
  | .nil, _, u => u
  | .cons .., _, u => (append₁ u).there

def Subst.append₂ : Subst Hyp Γ (.append Γ' Γ)
  | _, .here => .here
  | _, .there u => (append₂ u).there

class JudgeTrans (J J' : (Γ : Ctx) → (A : Propn) → Type) where
  transform (D : J Γ A) : J' Γ A

instance JudgeTrans.id : JudgeTrans J J where
  transform D := D

def Subst.mk [j : JudgeTrans Hyp J] {Γ A} (D : J Γ A) : Subst J (Γ.cons A) Γ
  | _, .here => D
  | _, .there u => j.transform u

def Subst.map (jt : JudgeTrans J J') {Γ Γ'} (γ : Subst J Γ Γ') : Subst J' Γ Γ'
  | _, u => jt.transform (γ u)

class Judge (J) extends JudgeTrans Hyp J where
  rename (γ : Subst Hyp Γ Γ') {A} (D : J Γ A) : J Γ' A

instance Hyp.judge : Judge Hyp where
  rename γ := @γ

def Subst.lift [j : Judge J] {Γ Γ'} (γ : Subst J Γ Γ') {A} : Subst J (Γ.cons A) (Γ'.cons A)
  | _, .here => j.transform .here
  | _, .there u => j.rename .weakening (γ u)

-- Natural Deduction
namespace ND

inductive True : (Γ : Ctx) → (A : Propn) → Type
  | hyp (u : Hyp Γ A) : True Γ A
  | trueI : True Γ .true
  | falseE (D : True Γ .false) : True Γ C
  | andI (D₁ : True Γ A) (D₂ : True Γ B) : True Γ (A.and B)
  | andE₁ (D : True Γ (A.and B)) : True Γ A
  | andE₂ (D : True Γ (.and A B)) : True Γ B
  | orI₁ (D : True Γ A) : True Γ (A.or B)
  | orI₂ (D : True Γ B) : True Γ (.or A B)
  | orE (D : True Γ (A.or B)) (D₁ : True (Γ.cons A) C) (D₂ : True (Γ.cons B) C) : True Γ C
  | impI (D : True (Γ.cons A) B) : True Γ (A.imp B)
  | impE (D : True Γ (A.imp B)) (D₁ : True Γ A) : True Γ B

instance True.judgeTransHyp : JudgeTrans Hyp True where
  transform := hyp

def True.subst [j : Judge J] [jt : JudgeTrans J True] {Γ Γ'} (γ : Subst J Γ Γ') {A} : (D : True Γ A) → True Γ' A
  | hyp u => jt.transform (γ u)
  | trueI => trueI
  | falseE D => falseE (D.subst γ)
  | andI D₁ D₂ => andI (D₁.subst γ) (D₂.subst γ)
  | andE₁ D => andE₁ (D.subst γ)
  | andE₂ D => andE₂ (D.subst γ)
  | orI₁ D => orI₁ (D.subst γ)
  | orI₂ D => orI₂ (D.subst γ)
  | orE D D₁ D₂ => orE (D.subst γ) (D₁.subst γ.lift) (D₂.subst γ.lift)
  | impI D => impI (D.subst γ.lift)
  | impE D D₁ => impE (D.subst γ) (D₁.subst γ)

instance True.judge : Judge True where
  rename := subst

end ND

-- Verifications and Uses
namespace VU

mutual

inductive Verif : (Γ : Ctx) → (A : Propn) → Type
  | uv (D : Use Γ (.base P)) : Verif Γ (.base P)
  | trueI : Verif Γ .true
  | falseE (D : Use Γ .false) : Verif Γ C
  | andI (D₁ : Verif Γ A) (D₂ : Verif Γ B) : Verif Γ (A.and B)
  | orI₁ (D : Verif Γ A) : Verif Γ (A.or B)
  | orI₂ (D : Verif Γ B) : Verif Γ (.or A B)
  | orE (D : Use Γ (A.or B)) (D₁ : Verif (Γ.cons A) C) (D₂ : Verif (Γ.cons B) C) : Verif Γ C
  | impI (D : Verif (Γ.cons A) B) : Verif Γ (A.imp B)

inductive Use : (Γ : Ctx) → (A : Propn) → Type
  | hyp (u : Hyp Γ A) : Use Γ A
  | andE₁ (D : Use Γ (A.and B)) : Use Γ A
  | andE₂ (D : Use Γ (.and A B)) : Use Γ B
  | impE (D : Use Γ (A.imp B)) (D₁ : Verif Γ A) : Use Γ B

end

instance Use.judgeTransHyp : JudgeTrans Hyp Use where
  transform := hyp

mutual

def Verif.subst [j : Judge J] [jt : JudgeTrans J Use] {Γ Γ'} (γ : Subst J Γ Γ') {A} : (D : Verif Γ A) → Verif Γ' A
  | .uv D => .uv (D.subst γ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.subst γ)
  | .andI D₁ D₂ => .andI (D₁.subst γ) (D₂.subst γ)
  | .orI₁ D => .orI₁ (D.subst γ)
  | .orI₂ D => .orI₂ (D.subst γ)
  | .orE D D₁ D₂ => .orE (D.subst γ) (D₁.subst γ.lift) (D₂.subst γ.lift)
  | .impI D => .impI (D.subst γ.lift)

def Use.subst [j : Judge J] [jt : JudgeTrans J Use] {Γ Γ'} (γ : Subst J Γ Γ') {A} : (D : Use Γ A) → Use Γ' A
  | .hyp u => jt.transform (γ u)
  | .andE₁ D => .andE₁ (D.subst γ)
  | .andE₂ D => .andE₂ (D.subst γ)
  | .impE D D₁ => .impE (D.subst γ) (D₁.subst γ)

end

instance Use.judge : Judge Use where
  rename := subst

def Verif.uv' (D : Use Γ A) : Verif Γ A :=
  match A with
  | .base _ => uv D
  | .true => trueI
  | .false => falseE D
  | .and .. => andI (uv' (.andE₁ D)) (uv' (.andE₂ D))
  | .or .. => orE D (orI₁ (uv' (.hyp .here))) (orI₂ (uv' (.hyp .here)))
  | .imp .. => impI (uv' (.impE (D.subst .weakening) (uv' (.hyp .here))))

instance Verif.judge : Judge Verif where
  transform u := uv' (.hyp u)
  rename := subst

mutual

def Verif.toTrue : (D : Verif Γ A) → ND.True Γ A
  | .uv D => D.toTrue
  | .trueI => .trueI
  | .falseE D => .falseE D.toTrue
  | .andI D₁ D₂ => .andI D₁.toTrue D₂.toTrue
  | .orI₁ D => .orI₁ D.toTrue
  | .orI₂ D => .orI₂ D.toTrue
  | .orE D D₁ D₂ => .orE D.toTrue D₁.toTrue D₂.toTrue
  | .impI D => .impI D.toTrue

def Use.toTrue : (D : Use Γ A) → ND.True Γ A
  | .hyp u => .hyp u
  | .andE₁ D => .andE₁ D.toTrue
  | .andE₂ D => .andE₂ D.toTrue
  | .impE D D₁ => .impE D.toTrue D₁.toTrue

end

end VU

-- Sequent Calculus
namespace SC

inductive Seq : (Γ : Ctx) → (A : Propn) → Type
  | id (u : Hyp Γ (.base P)) : Seq Γ (.base P)
  | trueR : Seq Γ .true
  | falseL (u : Hyp Γ .false) : Seq Γ C
  | andR (D₁ : Seq Γ A) (D₂ : Seq Γ B) : Seq Γ (A.and B)
  | andL₁ (u : Hyp Γ (A.and B)) (D : Seq (Γ.cons A) C) : Seq Γ C
  | andL₂ (u : Hyp Γ (.and A B)) (D : Seq (Γ.cons B) C) : Seq Γ C
  | orR₁ (D : Seq Γ A) : Seq Γ (A.or B)
  | orR₂ (D : Seq Γ B) : Seq Γ (.or A B)
  | orL (u : Hyp Γ (A.or B)) (D₁ : Seq (Γ.cons A) C) (D₂ : Seq (Γ.cons B) C) : Seq Γ C
  | impR (D : Seq (Γ.cons A) B) : Seq Γ (A.imp B)
  | impL (u : Hyp Γ (A.imp B)) (D₁ : Seq Γ A) (D₂ : Seq (Γ.cons B) C) : Seq Γ C

def Seq.rename (γ : Subst Hyp Γ Γ') {A} : (D : Seq Γ A) → Seq Γ' A
  | id u => id (γ u)
  | trueR => trueR
  | falseL u => falseL (γ u)
  | andR D₁ D₂ => andR (D₁.rename γ) (D₂.rename γ)
  | andL₁ u D => andL₁ (γ u) (D.rename γ.lift)
  | andL₂ u D => andL₂ (γ u) (D.rename γ.lift)
  | orR₁ D => orR₁ (D.rename γ)
  | orR₂ D => orR₂ (D.rename γ)
  | orL u D₁ D₂ => orL (γ u) (D₁.rename γ.lift) (D₂.rename γ.lift)
  | impR D => impR (D.rename γ.lift)
  | impL u D₁ D₂ => impL (γ u) (D₁.rename γ) (D₂.rename γ.lift)

def Seq.id' (u : Hyp Γ A) : Seq Γ A :=
  match A with
  | .base _ => id u
  | .true => trueR
  | .false => falseL u
  | .and .. => andR (andL₁ u (id' .here)) (andL₂ u (id' .here))
  | .or .. => orL u (orR₁ (id' .here)) (orR₂ (id' .here))
  | .imp .. => impR (impL u.there (id' .here) (id' .here))

instance Seq.judge : Judge Seq where
  transform := id'
  rename := rename

@[simp]
def Seq.sizeOf : (D : Seq Γ A) → Nat
  | id _ | trueR | falseL _ => 0
  | andL₁ _ D | andL₂ _ D | orR₁ D | orR₂ D | impR D => D.sizeOf + 1
  | andR D₁ D₂ | orL _ D₁ D₂ | impL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename (γ : Subst Hyp Γ Γ') {A} (D : Seq Γ A) : (D.rename γ).sizeOf = D.sizeOf :=
  by induction D generalizing Γ' <;> simp! only [*]

def Seq.cut : (D : Seq Γ A) → (E : Seq (Γ.cons A) C) → Seq Γ C
  | id u, E => E.rename (.contraction u)
  | D, id .here => D
  | _, id (.there u) => id u
  | D@(andR D₁ _), andL₁ .here E => cut D₁ (cut (D.rename .weakening) (E.rename .exchange))
  | D@(andR _ D₂), andL₂ .here E => cut D₂ (cut (D.rename .weakening) (E.rename .exchange))
  | D@(orR₁ D₁), orL .here E₁ _ => cut D₁ (cut (D.rename .weakening) (E₁.rename .exchange))
  | D@(orR₂ D₂), orL .here _ E₂ => cut D₂ (cut (D.rename .weakening) (E₂.rename .exchange))
  | D@(impR D₂), impL .here E₁ E₂ => cut (cut (cut D E₁) D₂) (cut (D.rename .weakening) (E₂.rename .exchange))
  | falseL u, _ => falseL u
  | andL₁ u D, E => andL₁ u (cut D (E.rename (.lift .weakening)))
  | andL₂ u D, E => andL₂ u (cut D (E.rename (.lift .weakening)))
  | orL u D₁ D₂, E => orL u (cut D₁ (E.rename (.lift .weakening))) (cut D₂ (E.rename (.lift .weakening)))
  | impL u D₁ D₂, E => impL u D₁ (cut D₂ (E.rename (.lift .weakening)))
  | _, trueR => trueR
  | _, falseL (.there u) => falseL u
  | D, andR E₁ E₂ => andR (cut D E₁) (cut D E₂)
  | D, andL₁ (.there u) E => andL₁ u (cut (D.rename .weakening) (E.rename .exchange))
  | D, andL₂ (.there u) E => andL₂ u (cut (D.rename .weakening) (E.rename .exchange))
  | D, orR₁ E => orR₁ (cut D E)
  | D, orR₂ E => orR₂ (cut D E)
  | D, orL (.there u) E₁ E₂ => orL u (cut (D.rename .weakening) (E₁.rename .exchange)) (cut (D.rename .weakening) (E₂.rename .exchange))
  | D, impR E => impR (cut (D.rename .weakening) (E.rename .exchange))
  | D, impL (.there u) E₁ E₂ => impL u (cut D E₁) (cut (D.rename .weakening) (E₂.rename .exchange))
  termination_by D E => (A, D.sizeOf, E.sizeOf)
  decreasing_by all_goals subst_vars; decreasing_tactic

def Seq.multicut (γ : Subst Seq Γ Γ') {A} (D : Seq (Γ'.append Γ) A) : Seq Γ' A :=
  match Γ with
  | .nil => D
  | .cons .. => multicut (fun _ u => γ u.there) (cut ((γ .here).rename .append₁) D)

def Seq.subst (γ : Subst Seq Γ Γ') {A} (D : Seq Γ A) : Seq Γ' A :=
  multicut γ (D.rename .append₂)

def Seq.toVerif : (D : Seq Γ A) → VU.Verif Γ A
  | id u => .uv (.hyp u)
  | trueR => .trueI
  | falseL u => .falseE (.hyp u)
  | andR D₁ D₂ => .andI D₁.toVerif D₂.toVerif
  | andL₁ u D => D.toVerif.subst (.mk (VU.Use.andE₁ (.hyp u)))
  | andL₂ u D => D.toVerif.subst (.mk (VU.Use.andE₂ (.hyp u)))
  | orR₁ D => .orI₁ D.toVerif
  | orR₂ D => .orI₂ D.toVerif
  | orL u D₁ D₂ => .orE (.hyp u) D₁.toVerif D₂.toVerif
  | impR D => .impI D.toVerif
  | impL u D₁ D₂ => D₂.toVerif.subst (.mk (VU.Use.impE (.hyp u) D₁.toVerif))

end SC

def ND.True.toSeq : (D : True Γ A) → SC.Seq Γ A
  | hyp u => .id' u
  | trueI => .trueR
  | falseE D => .cut D.toSeq (.falseL .here)
  | andI D₁ D₂ => .andR D₁.toSeq D₂.toSeq
  | andE₁ D => .cut D.toSeq (.andL₁ .here (.id' .here))
  | andE₂ D => .cut D.toSeq (.andL₂ .here (.id' .here))
  | orI₁ D => .orR₁ D.toSeq
  | orI₂ D => .orR₂ D.toSeq
  | orE D D₁ D₂ => .cut D.toSeq (.orL .here (D₁.toSeq.rename (.lift .weakening)) (D₂.toSeq.rename (.lift .weakening)))
  | impI D => .impR D.toSeq
  | impE D D₁ => .cut D.toSeq (.impL .here (D₁.toSeq.rename .weakening) (.id' .here))

def VU.Verif.subst' (γ : Subst Verif Γ Γ') {A} (D : Verif Γ A) : Verif Γ' A :=
  (D.toTrue.toSeq.subst (γ.map ⟨fun D => D.toTrue.toSeq⟩)).toVerif
