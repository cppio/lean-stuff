inductive Propn
  | base (P : Nat)
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
  | cons Γ' A => cons (Γ.append Γ') A

inductive Mem (A : Propn) : (Γ : Ctx) → Type
  | here : Mem A (.cons Γ A)
  | there (u : Mem A Γ) : Mem A (Γ.cons B)

def Rename (Γ Γ' : Ctx) : Type :=
  ∀ A, (u : Mem A Γ) → Mem A Γ'

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

def Rename.cons (γ : Rename Γ Γ') {A} : Rename (Γ.cons A) (Γ'.cons A)
  | _, .here => .here
  | A, .there u => (γ A u).there

def Rename.append₁ : ∀ {Γ'}, Rename Γ (Γ.append Γ')
  | .nil, _, u => u
  | .cons .., A, u => (append₁ A u).there

def Rename.append₂ : Rename Γ' (.append Γ Γ')
  | _, .here => .here
  | A, .there u => (append₂ A u).there

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
  | hyp u => hyp (γ A u)
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

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ A, (u : Mem A Γ) → True Γ' A

def Subst.cons (γ : Subst Γ Γ') {A} : Subst (Γ.cons A) (Γ'.cons A)
  | _, .here => .hyp .here
  | A, .there u => (γ A u).rename .weakening

def True.subst (γ : Subst Γ Γ') {A} : (D : True Γ A) → True Γ' A
  | hyp u => γ A u
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
  | .hyp u => .hyp (γ A u)
  | .andE₁ D => .andE₁ (D.rename γ)
  | .andE₂ D => .andE₂ (D.rename γ)
  | .impE D D₁ => .impE (D.rename γ) (D₁.rename γ)

end

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ A, (u : Mem A Γ) → Use Γ' A

def Subst.mk (D : Use Γ A) : Subst (Γ.cons A) Γ
  | _, .here => D
  | _, .there u => .hyp u

def Subst.cons (γ : Subst Γ Γ') {A} : Subst (Γ.cons A) (Γ'.cons A)
  | _, .here => .hyp .here
  | A, .there u => (γ A u).rename .weakening

mutual

def Verif.subst (γ : Subst Γ Γ') {A} : (D : Verif Γ A) → Verif Γ' A
  | .uv D => .uv (D.subst γ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.subst γ)
  | .andI D₁ D₂ => .andI (D₁.subst γ) (D₂.subst γ)
  | .orI₁ D => .orI₁ (D.subst γ)
  | .orI₂ D => .orI₂ (D.subst γ)
  | .orE D D₁ D₂ => .orE (D.subst γ) (D₁.subst γ.cons) (D₂.subst γ.cons)
  | .impI D => .impI (D.subst γ.cons)

def Use.subst (γ : Subst Γ Γ') {A} : (D : Use Γ A) → Use Γ' A
  | .hyp u => γ A u
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

def Subst' (Γ Γ' : Ctx) : Type :=
  ∀ A, (u : Mem A Γ) → Verif Γ' A

def Subst'.cons (γ : Subst' Γ Γ') {A} : Subst' (Γ.cons A) (Γ'.cons A)
  | _, .here => .uv' (.hyp .here)
  | A, .there u => (γ A u).rename .weakening

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

def Subst.toTrue (γ : Subst Γ Γ') : ND.Subst Γ Γ'
  | A, u => (γ A u).toTrue

def Subst'.toTrue (γ : Subst' Γ Γ') : ND.Subst Γ Γ'
  | A, u => (γ A u).toTrue

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
  | id u => id (γ _ u)
  | trueR => trueR
  | falseL u => falseL (γ _ u)
  | andR D₁ D₂ => andR (D₁.rename γ) (D₂.rename γ)
  | andL₁ u D => andL₁ (γ _ u) (D.rename γ.cons)
  | andL₂ u D => andL₂ (γ _ u) (D.rename γ.cons)
  | orR₁ D => orR₁ (D.rename γ)
  | orR₂ D => orR₂ (D.rename γ)
  | orL u D₁ D₂ => orL (γ _ u) (D₁.rename γ.cons) (D₂.rename γ.cons)
  | impR D => impR (D.rename γ.cons)
  | impL u D₁ D₂ => impL (γ _ u) (D₁.rename γ) (D₂.rename γ.cons)

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
  | id _ => 0
  | trueR => 0
  | falseL _ => 0
  | andR D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1
  | andL₁ _ D => D.sizeOf + 1
  | andL₂ _ D => D.sizeOf + 1
  | orR₁ D => D.sizeOf + 1
  | orR₂ D => D.sizeOf + 1
  | orL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1
  | impR D => D.sizeOf + 1
  | impL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename {γ : Rename Γ Γ'} (D : Seq Γ A) : (D.rename γ).sizeOf = D.sizeOf :=
  by induction D generalizing Γ' <;> simp [*]

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
  | andL₁ u D, E => andL₁ u (cut D (E.rename (.cons .weakening)))
  | andL₂ u D, E => andL₂ u (cut D (E.rename (.cons .weakening)))
  | orL u D₁ D₂, E => orL u (cut D₁ (E.rename (.cons .weakening))) (cut D₂ (E.rename (.cons .weakening)))
  | impL u D₁ D₂, E => impL u D₁ (cut D₂ (E.rename (.cons .weakening)))
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

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ A, (u : Mem A Γ) → Seq Γ' A

def Seq.multicut (γ : Subst Γ Γ') {A} (D : Seq (Γ'.append Γ) A) : Seq Γ' A :=
  match Γ with
  | .nil => D
  | .cons _ A => multicut (fun A u => γ A u.there) (cut ((γ A .here).rename .append₁) D)

def Seq.subst (γ : Subst Γ Γ') {A} (D : Seq Γ A) : Seq Γ' A :=
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

def Subst.toVerif (γ : Subst Γ Γ') : VU.Subst' Γ Γ'
  | A, u => (γ A u).toVerif

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
  | orE D D₁ D₂ => .cut D.toSeq (.orL .here (D₁.toSeq.rename (.cons .weakening)) (D₂.toSeq.rename (.cons .weakening)))
  | impI D => .impR D.toSeq
  | impE D D₁ => .cut D.toSeq (.impL .here (D₁.toSeq.rename .weakening) (.id' .here))

def ND.Subst.toSeq (γ : Subst Γ Γ') : SC.Subst Γ Γ'
  | A, u => (γ A u).toSeq

def VU.Verif.subst' (γ : Subst' Γ Γ') {A} (D : Verif Γ A) : Verif Γ' A :=
  (D.toTrue.toSeq.subst γ.toTrue.toSeq).toVerif

-- Classical Sequent Calculus
namespace CSC

inductive Seq : (Γ : Ctx) → (Δ : Ctx) → Type
  | id (u : Mem (.base P) Γ) (v : Mem (.base P) Δ) : Seq Γ Δ
  | trueR (v : Mem .true Δ) : Seq Γ Δ
  | falseL (u : Mem .false Γ) : Seq Γ Δ
  | andR (v : Mem (A.and B) Δ) (D₁ : Seq Γ (Δ.cons A)) (D₂ : Seq Γ (Δ.cons B)) : Seq Γ Δ
  | andL₁ (u : Mem (A.and B) Γ) (D : Seq (Γ.cons A) Δ) : Seq Γ Δ
  | andL₂ (u : Mem (.and A B) Γ) (D : Seq (Γ.cons B) Δ) : Seq Γ Δ
  | orR₁ (v : Mem (A.or B) Δ) (D : Seq Γ (Δ.cons A)) : Seq Γ Δ
  | orR₂ (v : Mem (.or A B) Δ) (D : Seq Γ (Δ.cons B)) : Seq Γ Δ
  | orL (u : Mem (A.or B) Γ) (D₁ : Seq (Γ.cons A) Δ) (D₂ : Seq (Γ.cons B) Δ) : Seq Γ Δ
  | impR (v : Mem (A.imp B) Δ) (D : Seq (Γ.cons A) (Δ.cons B)) : Seq Γ Δ
  | impL (u : Mem (A.imp B) Γ) (D₁ : Seq Γ (Δ.cons A)) (D₂ : Seq (Γ.cons B) Δ) : Seq Γ Δ

def Seq.rename (γ : Rename Γ Γ') (δ : Rename Δ Δ') : (D : Seq Γ Δ) → Seq Γ' Δ'
  | id u v => id (γ _ u) (δ _ v)
  | trueR v => trueR (δ _ v)
  | falseL u => falseL (γ _ u)
  | andR v D₁ D₂ => andR (δ _ v) (D₁.rename γ δ.cons) (D₂.rename γ δ.cons)
  | andL₁ u D => andL₁ (γ _ u) (D.rename γ.cons δ)
  | andL₂ u D => andL₂ (γ _ u) (D.rename γ.cons δ)
  | orR₁ v D => orR₁ (δ _ v) (D.rename γ δ.cons)
  | orR₂ v D => orR₂ (δ _ v) (D.rename γ δ.cons)
  | orL u D₁ D₂ => orL (γ _ u) (D₁.rename γ.cons δ) (D₂.rename γ.cons δ)
  | impR v D => impR (δ _ v) (D.rename γ.cons δ.cons)
  | impL u D₁ D₂ => impL (γ _ u) (D₁.rename γ δ.cons) (D₂.rename γ.cons δ)

def Seq.id' (u : Mem A Γ) (v : Mem A Δ) : Seq Γ Δ :=
  match A with
  | .base _ => id u v
  | .true => trueR v
  | .false => falseL u
  | .and .. => andR v (andL₁ u (id' .here .here)) (andL₂ u (id' .here .here))
  | .or .. => orL u (orR₁ v (id' .here .here)) (orR₂ v (id' .here .here))
  | .imp .. => impR v (impL u.there (id' .here .here) (id' .here .here))

@[simp]
def Seq.sizeOf : (D : Seq Γ A) → Nat
  | id .. => 0
  | trueR _ => 0
  | falseL _ => 0
  | andR _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1
  | andL₁ _ D => D.sizeOf + 1
  | andL₂ _ D => D.sizeOf + 1
  | orR₁ _ D => D.sizeOf + 1
  | orR₂ _ D => D.sizeOf + 1
  | orL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1
  | impR _ D => D.sizeOf + 1
  | impL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename {γ : Rename Γ Γ'} {δ : Rename Δ Δ'} (D : Seq Γ Δ) : (D.rename γ δ).sizeOf = D.sizeOf :=
  by induction D generalizing Γ' Δ' <;> simp [*]

def Seq.cut : (D : Seq Γ (Δ.cons A)) → (E : Seq (Γ.cons A) Δ) → Seq Γ Δ
  | .id u .here, E => E.rename (.contraction u) .id
  | .id u (.there v), _ => .id u v
  | D, .id .here v => D.rename .id (.contraction v)
  | _, .id (.there u) v => .id u v
  | D@(andR .here D₁ _), E@(andL₁ .here E₁) => cut (cut (D₁.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₁.rename .exchange .id))
  | D@(andR .here _ D₂), E@(andL₂ .here E₂) => cut (cut (D₂.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₂.rename .exchange .id))
  | D@(orR₁ .here D₁), E@(orL .here E₁ _) => cut (cut (D₁.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₁.rename .exchange .id))
  | D@(orR₂ .here D₂), E@(orL .here _ E₂) => cut (cut (D₂.rename .id .exchange) (E.rename .id .weakening)) (cut (D.rename .weakening .id) (E₂.rename .exchange .id))
  | D@(impR .here D₁), E@(impL .here E₁ E₂) => cut (cut (D.rename .id (.cons .weakening)) (E₁.rename .id .id)) (cut (cut (D₁.rename .id .exchange) (E.rename (.cons .weakening) .weakening)) ((cut (D.rename .weakening .id) (E₂.rename .exchange .id)).rename (.cons .weakening) .id))
  | trueR (.there v), _ => trueR v
  | falseL u, _ => falseL u
  | andR (.there v) D₁ D₂, E => andR v (cut (D₁.rename .id .exchange) (E.rename .id .weakening)) (cut (D₂.rename .id .exchange) (E.rename .id .weakening))
  | andL₁ u D, E => andL₁ u (cut D (E.rename (.cons .weakening) .id))
  | andL₂ u D, E => andL₂ u (cut D (E.rename (.cons .weakening) .id))
  | orR₁ (.there v) D, E => orR₁ v (cut (D.rename .id .exchange) (E.rename .id .weakening))
  | orR₂ (.there v) D, E => orR₂ v (cut (D.rename .id .exchange) (E.rename .id .weakening))
  | orL u D₁ D₂, E => orL u (cut D₁ (E.rename (.cons .weakening) .id)) (cut D₂ (E.rename (.cons .weakening) .id))
  | impR (.there v) D, E => impR v (cut (D.rename .id .exchange) (E.rename (.cons .weakening) .weakening))
  | impL u D₁ D₂, E => impL u (cut (D₁.rename .id .exchange) (E.rename .id .weakening)) (cut D₂ (E.rename (.cons .weakening) .id))
  | _, trueR v => trueR v
  | _, falseL (.there u) => falseL u
  | D, andR v E₁ E₂ => andR v (cut (D.rename .id (.cons .weakening)) E₁) (cut (D.rename .id (.cons .weakening)) E₂)
  | D, andL₁ (.there u) E => andL₁ u (cut (D.rename .weakening .id) (E.rename .exchange .id))
  | D, andL₂ (.there u) E => andL₂ u (cut (D.rename .weakening .id) (E.rename .exchange .id))
  | D, orR₁ v E => orR₁ v (cut (D.rename .id (.cons .weakening)) E)
  | D, orR₂ v E => orR₂ v (cut (D.rename .id (.cons .weakening)) E)
  | D, orL (.there u) E₁ E₂ => orL u (cut (D.rename .weakening .id) (E₁.rename .exchange .id)) (cut (D.rename .weakening .id) (E₂.rename .exchange .id))
  | D, impR v E => impR v (cut (D.rename .weakening (.cons .weakening)) (E.rename .exchange .id))
  | D, impL (.there u) E₁ E₂ => impL u (cut (D.rename .id (.cons .weakening)) E₁) (cut (D.rename .weakening .id) (E₂.rename .exchange .id))
  termination_by D E => (A, D.sizeOf, E.sizeOf)
  decreasing_by all_goals subst_vars; decreasing_tactic

end CSC
