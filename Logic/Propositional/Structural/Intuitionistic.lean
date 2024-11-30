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

inductive Mem (A : Propn) : (Γ : Ctx) → Type
  | here : Mem A (.cons Γ A)
  | there (u : Mem A Γ) : Mem A (Γ.cons B)

class Judge (J : (Γ : Ctx) → (A : Propn) → Type) where
  hyp (u : Mem A Γ) : J Γ A
  weaken (D : J Γ A) : J (Γ.cons B) A

instance Mem.instJudge : Judge (fun Γ A => Mem A Γ) where
  hyp u := u
  weaken := there

def Subst (J : (Γ : Ctx) → (A : Propn) → Type) (Γ Γ' : Ctx) : Type :=
  ∀ ⦃A⦄, (u : Mem A Γ) → J Γ' A

def Subst.cons [Judge J] (γ : Subst J Γ Γ') {A} : Subst J (Γ.cons A) (Γ'.cons A)
  | _, .here => Judge.hyp .here
  | _, .there u => Judge.weaken (γ u)

def Subst.mk [Judge J] (D : J Γ A) : Subst J (Γ.cons A) Γ
  | _, .here => D
  | _, .there u => Judge.hyp u

def Subst.map (f : ∀ {Γ A}, J Γ A → J' Γ A) {Γ Γ'} (γ : Subst J Γ Γ') : Subst J' Γ Γ'
  | _, u => f (γ u)

def Rename : (Γ Γ' : Ctx) → Type :=
  Subst fun Γ A => Mem A Γ

def Rename.id : Rename Γ Γ
  | _, u => u

def Rename.weakening : Rename Γ (Γ.cons A)
  | _ => .there

def Rename.contraction (u : Mem A Γ) : Rename (Γ.cons A) Γ
  | _, .here => u
  | _, .there u => u

def Rename.exchange : Rename (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there u) => u.there.there

def Rename.append₁ : ∀ {Γ'}, Rename Γ (Γ.append Γ')
  | .nil, _, u => u
  | .cons .., _, u => (append₁ u).there

def Rename.append₂ : Rename Γ' (.append Γ Γ')
  | _, .here => .here
  | _, .there u => (append₂ u).there

-- Natural Deduction
namespace ND

inductive True : (Γ : Ctx) → (A : Propn) → Type
  | hyp (u : Mem A Γ) : True Γ A
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

def True.rename (γ : Rename Γ Γ') {A} : (D : True Γ A) → True Γ' A
  | hyp u => hyp (γ u)
  | trueI => trueI
  | falseE D => falseE (D.rename γ)
  | andI D₁ D₂ => andI (D₁.rename γ) (D₂.rename γ)
  | andE₁ D => andE₁ (D.rename γ)
  | andE₂ D => andE₂ (D.rename γ)
  | orI₁ D => orI₁ (D.rename γ)
  | orI₂ D => orI₂ (D.rename γ)
  | orE D D₁ D₂ => orE (D.rename γ) (D₁.rename γ.cons) (D₂.rename γ.cons)
  | impI D => impI (D.rename γ.cons)
  | impE D D₁ => impE (D.rename γ) (D₁.rename γ)

instance True.instJudge : Judge True where
  hyp := hyp
  weaken := rename .weakening

def True.subst (γ : Subst True Γ Γ') {A} : (D : True Γ A) → True Γ' A
  | hyp u => γ u
  | trueI => trueI
  | falseE D => falseE (D.subst γ)
  | andI D₁ D₂ => andI (D₁.subst γ) (D₂.subst γ)
  | andE₁ D => andE₁ (D.subst γ)
  | andE₂ D => andE₂ (D.subst γ)
  | orI₁ D => orI₁ (D.subst γ)
  | orI₂ D => orI₂ (D.subst γ)
  | orE D D₁ D₂ => orE (D.subst γ) (D₁.subst γ.cons) (D₂.subst γ.cons)
  | impI D => impI (D.subst γ.cons)
  | impE D D₁ => impE (D.subst γ) (D₁.subst γ)

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
  | hyp (u : Mem A Γ) : Use Γ A
  | andE₁ (D : Use Γ (A.and B)) : Use Γ A
  | andE₂ (D : Use Γ (.and A B)) : Use Γ B
  | impE (D : Use Γ (A.imp B)) (D₁ : Verif Γ A) : Use Γ B

end

mutual

def Verif.rename (γ : Rename Γ Γ') {A} : (D : Verif Γ A) → Verif Γ' A
  | .uv D => .uv (D.rename γ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.rename γ)
  | .andI D₁ D₂ => .andI (D₁.rename γ) (D₂.rename γ)
  | .orI₁ D => .orI₁ (D.rename γ)
  | .orI₂ D => .orI₂ (D.rename γ)
  | .orE D D₁ D₂ => .orE (D.rename γ) (D₁.rename γ.cons) (D₂.rename γ.cons)
  | .impI D => .impI (D.rename γ.cons)

def Use.rename (γ : Rename Γ Γ') {A} : (D : Use Γ A) → Use Γ' A
  | .hyp u => .hyp (γ u)
  | .andE₁ D => .andE₁ (D.rename γ)
  | .andE₂ D => .andE₂ (D.rename γ)
  | .impE D D₁ => .impE (D.rename γ) (D₁.rename γ)

end

instance Use.instJudge : Judge Use where
  hyp := hyp
  weaken := rename .weakening

mutual

def Verif.subst (γ : Subst Use Γ Γ') {A} : (D : Verif Γ A) → Verif Γ' A
  | .uv D => .uv (D.subst γ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.subst γ)
  | .andI D₁ D₂ => .andI (D₁.subst γ) (D₂.subst γ)
  | .orI₁ D => .orI₁ (D.subst γ)
  | .orI₂ D => .orI₂ (D.subst γ)
  | .orE D D₁ D₂ => .orE (D.subst γ) (D₁.subst γ.cons) (D₂.subst γ.cons)
  | .impI D => .impI (D.subst γ.cons)

def Use.subst (γ : Subst Use Γ Γ') {A} : (D : Use Γ A) → Use Γ' A
  | .hyp u => γ u
  | .andE₁ D => .andE₁ (D.subst γ)
  | .andE₂ D => .andE₂ (D.subst γ)
  | .impE D D₁ => .impE (D.subst γ) (D₁.subst γ)

end

def Verif.uv' (D : Use Γ A) : Verif Γ A :=
  match A with
  | .base _ => uv D
  | .true => trueI
  | .false => falseE D
  | .and .. => andI (uv' (.andE₁ D)) (uv' (.andE₂ D))
  | .or .. => orE D (orI₁ (uv' (.hyp .here))) (orI₂ (uv' (.hyp .here)))
  | .imp .. => impI (uv' (.impE (D.rename .weakening) (uv' (.hyp .here))))

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
  | id (u : Mem (.base P) Γ) : Seq Γ (.base P)
  | trueR : Seq Γ .true
  | falseL (u : Mem .false Γ) : Seq Γ C
  | andR (D₁ : Seq Γ A) (D₂ : Seq Γ B) : Seq Γ (A.and B)
  | andL₁ (u : Mem (A.and B) Γ) (D : Seq (Γ.cons A) C) : Seq Γ C
  | andL₂ (u : Mem (.and A B) Γ) (D : Seq (Γ.cons B) C) : Seq Γ C
  | orR₁ (D : Seq Γ A) : Seq Γ (A.or B)
  | orR₂ (D : Seq Γ B) : Seq Γ (.or A B)
  | orL (u : Mem (A.or B) Γ) (D₁ : Seq (Γ.cons A) C) (D₂ : Seq (Γ.cons B) C) : Seq Γ C
  | impR (D : Seq (Γ.cons A) B) : Seq Γ (A.imp B)
  | impL (u : Mem (A.imp B) Γ) (D₁ : Seq Γ A) (D₂ : Seq (Γ.cons B) C) : Seq Γ C

def Seq.rename (γ : Rename Γ Γ') {A} : (D : Seq Γ A) → Seq Γ' A
  | id u => id (γ u)
  | trueR => trueR
  | falseL u => falseL (γ u)
  | andR D₁ D₂ => andR (D₁.rename γ) (D₂.rename γ)
  | andL₁ u D => andL₁ (γ u) (D.rename γ.cons)
  | andL₂ u D => andL₂ (γ u) (D.rename γ.cons)
  | orR₁ D => orR₁ (D.rename γ)
  | orR₂ D => orR₂ (D.rename γ)
  | orL u D₁ D₂ => orL (γ u) (D₁.rename γ.cons) (D₂.rename γ.cons)
  | impR D => impR (D.rename γ.cons)
  | impL u D₁ D₂ => impL (γ u) (D₁.rename γ) (D₂.rename γ.cons)

def Seq.id' (u : Mem A Γ) : Seq Γ A :=
  match A with
  | .base _ => id u
  | .true => trueR
  | .false => falseL u
  | .and .. => andR (andL₁ u (id' .here)) (andL₂ u (id' .here))
  | .or .. => orL u (orR₁ (id' .here)) (orR₂ (id' .here))
  | .imp .. => impR (impL u.there (id' .here) (id' .here))

@[simp]
def Seq.sizeOf : (D : Seq Γ A) → Nat
  | id _ | trueR | falseL _ => 0
  | andL₁ _ D | andL₂ _ D | orR₁ D | orR₂ D | impR D => D.sizeOf + 1
  | andR D₁ D₂ | orL _ D₁ D₂ | impL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename {γ : Rename Γ Γ'} (D : Seq Γ A) : (D.rename γ).sizeOf = D.sizeOf :=
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
  | andL₁ u D, E => andL₁ u (cut D (E.rename Rename.weakening.cons))
  | andL₂ u D, E => andL₂ u (cut D (E.rename Rename.weakening.cons))
  | orL u D₁ D₂, E => orL u (cut D₁ (E.rename Rename.weakening.cons)) (cut D₂ (E.rename Rename.weakening.cons))
  | impL u D₁ D₂, E => impL u D₁ (cut D₂ (E.rename Rename.weakening.cons))
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
  | andL₁ u D => D.toVerif.subst (.mk (.andE₁ (.hyp u)))
  | andL₂ u D => D.toVerif.subst (.mk (.andE₂ (.hyp u)))
  | orR₁ D => .orI₁ D.toVerif
  | orR₂ D => .orI₂ D.toVerif
  | orL u D₁ D₂ => .orE (.hyp u) D₁.toVerif D₂.toVerif
  | impR D => .impI D.toVerif
  | impL u D₁ D₂ => D₂.toVerif.subst (.mk (.impE (.hyp u) D₁.toVerif))

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
  | orE D D₁ D₂ => .cut D.toSeq (.orL .here (D₁.toSeq.rename Rename.weakening.cons) (D₂.toSeq.rename Rename.weakening.cons))
  | impI D => .impR D.toSeq
  | impE D D₁ => .cut D.toSeq (.impL .here (D₁.toSeq.rename .weakening) (.id' .here))

def VU.Verif.subst' (γ : Subst Verif Γ Γ') {A} (D : Verif Γ A) : Verif Γ' A :=
  (D.toTrue.toSeq.subst (γ.map fun D => D.toTrue.toSeq)).toVerif
