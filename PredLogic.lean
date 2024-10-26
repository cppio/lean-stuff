inductive ElemCtx
  | nil
  | cons (Φ : ElemCtx)

inductive ElemMem : (Φ : ElemCtx) → Type
  | here : ElemMem (.cons Φ)
  | there (a : ElemMem Φ) : ElemMem Φ.cons

def ElemRename (Φ Φ' : ElemCtx) : Type :=
  (a : ElemMem Φ) → ElemMem Φ'

def ElemRename.mk (t : ElemMem Φ) : ElemRename Φ.cons Φ
  | .here => t
  | .there a => a

def ElemRename.cons (φ : ElemRename Φ Φ') : ElemRename Φ.cons Φ'.cons
  | .here => .here
  | .there a => (φ a).there

@[simp]
theorem ElemRename.mk_cons : mk (φ t) (cons φ a) = φ (mk t a) :=
  by cases a <;> rfl

@[simp]
theorem ElemRename.mk_cons' : mk .here (cons .there a) = a :=
  by cases a <;> rfl

@[simp]
theorem ElemRename.cons_cons : cons φ₂ (cons φ₁ a) = cons (fun a => φ₂ (φ₁ a)) a :=
  by cases a <;> rfl

@[simp]
theorem ElemRename.cons_id : cons (fun a => a) a = a :=
  by cases a <;> rfl

inductive Propn : (Φ : ElemCtx) → Type
  | base (P : Nat) (xs : List (ElemMem Φ)) : Propn Φ
  | true : Propn Φ
  | false : Propn Φ
  | and (A B : Propn Φ) : Propn Φ
  | or (A B : Propn Φ) : Propn Φ
  | imp (A B : Propn Φ) : Propn Φ
  | forall (A : Propn Φ.cons) : Propn Φ
  | exists (A : Propn Φ.cons) : Propn Φ

def Propn.rename (φ : ElemRename Φ Φ') : (A : Propn Φ) → Propn Φ'
  | base P xs => base P (xs.map φ)
  | true => true
  | false => false
  | and A B => and (A.rename φ) (B.rename φ)
  | or A B => or (A.rename φ) (B.rename φ)
  | imp A B => imp (A.rename φ) (B.rename φ)
  | .forall A => .forall (A.rename φ.cons)
  | .exists A => .exists (A.rename φ.cons)

@[simp]
def Propn.sizeOf : (A : Propn Φ) → Nat
  | base .. => 0
  | true => 0
  | false => 0
  | and A B => A.sizeOf + B.sizeOf + 1
  | or A B => A.sizeOf + B.sizeOf + 1
  | imp A B => A.sizeOf + B.sizeOf + 1
  | .forall A => A.sizeOf + 1
  | .exists A => A.sizeOf + 1

@[simp]
theorem Propn.sizeOf_rename {φ : ElemRename Φ Φ'} (A : Propn Φ) : (A.rename φ).sizeOf = A.sizeOf :=
  by induction A generalizing Φ' <;> simp [*]

@[simp]
theorem Propn.rename_id : rename (fun a => a) A = A :=
  by induction A <;> simp [rename, *] <;> refine .trans ?_ ‹_› <;> congr <;> funext a <;> cases a <;> rfl

@[simp]
theorem Propn.rename_rename {φ₁ : ElemRename Φ Φ'} {φ₂ : ElemRename Φ' Φ''} : rename φ₂ (rename φ₁ A) = rename (fun a => φ₂ (φ₁ a)) A :=
  by induction A generalizing Φ' Φ'' <;> simp [rename, *]

inductive Ctx (Φ : ElemCtx)
  | nil
  | cons (Γ : Ctx Φ) (A : Propn Φ)

def Ctx.rename (φ : ElemRename Φ Φ') : (Γ : Ctx Φ) → Ctx Φ'
  | nil => nil
  | cons Γ A => cons (Γ.rename φ) (A.rename φ)

@[simp]
theorem Ctx.rename_id : rename (fun a => a) Γ = Γ :=
  by induction Γ <;> simp [rename, *]

@[simp]
theorem Ctx.rename_rename {φ₁ : ElemRename Φ Φ'} {φ₂ : ElemRename Φ' Φ''} : rename φ₂ (rename φ₁ Γ) = rename (fun a => φ₂ (φ₁ a)) Γ :=
  by induction Γ <;> simp [rename, *]

def Ctx.append (Γ : Ctx Φ) : (Γ' : Ctx Φ) → Ctx Φ
  | nil => Γ
  | cons Γ' A => cons (Γ.append Γ') A

inductive Mem Φ (A : Propn Φ) : (Γ : Ctx Φ) → Type
  | here : Mem Φ A (.cons Γ A)
  | there (u : Mem Φ A Γ) : Mem Φ A (Γ.cons B)

def Mem.rename (φ : ElemRename Φ Φ') {A Γ} : (u : Mem Φ A Γ) → Mem Φ' (A.rename φ) (Γ.rename φ)
  | here => here
  | there u => there (u.rename φ)

def Rename Φ (Γ Γ' : Ctx Φ) : Type :=
  ∀ A, (u : Mem Φ A Γ) → Mem Φ A Γ'

def Rename.rename (φ : ElemRename Φ Φ') (γ : Rename Φ Γ Γ') : Rename Φ' (Γ.rename φ) (Γ'.rename φ)
  | A, u =>
  match Γ, A, u with
  | .cons .., _, .here => (γ _ .here).rename φ
  | .cons .., _, .there u => rename φ (fun A u => γ A u.there) _ u

def Rename.id : Rename Φ Γ Γ
  | _, u => u

def Rename.weakening : Rename Φ Γ (Γ.cons A)
  | _ => .there

def Rename.contraction (u : Mem Φ A Γ) : Rename Φ (Γ.cons A) Γ
  | _, .here => u
  | _, .there u => u

def Rename.exchange : Rename Φ (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there u) => u.there.there

def Rename.cons (γ : Rename Φ Γ Γ') {A} : Rename Φ (Γ.cons A) (Γ'.cons A)
  | _, .here => .here
  | A, .there u => (γ A u).there

def Rename.append₁ : ∀ {Γ'}, Rename Φ Γ (Γ.append Γ')
  | .nil, _, u => u
  | .cons .., A, u => (append₁ A u).there

def Rename.append₂ : Rename Φ Γ' (.append Γ Γ')
  | _, .here => .here
  | A, .there u => (append₂ A u).there

-- Natural Deduction
namespace ND

inductive True : ∀ Φ, (Γ : Ctx Φ) → (A : Propn Φ) → Type
  | hyp (u : Mem Φ A Γ) : True Φ Γ A
  | trueI : True Φ Γ .true
  | falseE (D : True Φ Γ .false) : True Φ Γ C
  | andI (D₁ : True Φ Γ A) (D₂ : True Φ Γ B) : True Φ Γ (A.and B)
  | andE₁ (D : True Φ Γ (A.and B)) : True Φ Γ A
  | andE₂ (D : True Φ Γ (.and A B)) : True Φ Γ B
  | orI₁ (D : True Φ Γ A) : True Φ Γ (A.or B)
  | orI₂ (D : True Φ Γ B) : True Φ Γ (.or A B)
  | orE (D : True Φ Γ (A.or B)) (D₁ : True Φ (Γ.cons A) C) (D₂ : True Φ (Γ.cons B) C) : True Φ Γ C
  | impI (D : True Φ (Γ.cons A) B) : True Φ Γ (A.imp B)
  | impE (D : True Φ Γ (A.imp B)) (D₁ : True Φ Γ A) : True Φ Γ B
  | forallI (D : True (.cons Φ) (Γ.rename .there) A) : True Φ Γ (.forall A)
  | forallE (D : True Φ Γ (.forall A)) (t : ElemMem Φ) : True Φ Γ (A.rename (.mk t))
  | existsI (t : ElemMem Φ) (D : True Φ Γ (A.rename (.mk t))) : True Φ Γ (.exists A)
  | existsE (D : True Φ Γ (.exists A)) (D₁ : True Φ.cons (Γ.rename .there |>.cons A) (C.rename .there)) : True Φ Γ C

def True.renameElem (φ : ElemRename Φ Φ') {Γ A} : (D : True Φ Γ A) → True Φ' (Γ.rename φ) (A.rename φ)
  | hyp u => hyp (u.rename φ)
  | trueI => trueI
  | falseE D => falseE (D.renameElem φ)
  | andI D₁ D₂ => andI (D₁.renameElem φ) (D₂.renameElem φ)
  | andE₁ D => andE₁ (D.renameElem φ)
  | andE₂ D => andE₂ (D.renameElem φ)
  | orI₁ D => orI₁ (D.renameElem φ)
  | orI₂ D => orI₂ (D.renameElem φ)
  | orE D D₁ D₂ => orE (D.renameElem φ) (D₁.renameElem φ) (D₂.renameElem φ)
  | impI D => impI (D.renameElem φ)
  | impE D D₁ => impE (D.renameElem φ) (D₁.renameElem φ)
  | forallI D => forallI (have := D.renameElem φ.cons; by simp at this ⊢; exact this)
  | forallE D t => have := forallE (D.renameElem φ) (φ t); by simp at this ⊢; exact this
  | existsI t D => existsI (φ t) (have := D.renameElem φ; by simp at this ⊢; exact this)
  | existsE D D₁ => existsE (D.renameElem φ) (have := D₁.renameElem φ.cons; by simp! at this ⊢; exact this)

def True.rename (γ : Rename Φ Γ Γ') {A} : (D : True Φ Γ A) → True Φ Γ' A
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
  | forallI D => forallI (D.rename (γ.rename .there))
  | forallE D t => forallE (D.rename γ) t
  | existsI t D => existsI t (D.rename γ)
  | existsE D D₁ => existsE (D.rename γ) (D₁.rename (γ.rename .there |>.cons))

def Subst Φ (Γ Γ' : Ctx Φ) : Type :=
  ∀ A, (u : Mem Φ A Γ) → True Φ Γ' A

def Subst.rename (φ : ElemRename Φ Φ') (γ : Subst Φ Γ Γ') : Subst Φ' (Γ.rename φ) (Γ'.rename φ)
  | A, u =>
  match Γ, A, u with
  | .cons .., _, .here => (γ _ .here).renameElem φ
  | .cons .., _, .there u => rename φ (fun A u => γ A u.there) _ u

def Subst.cons (γ : Subst Φ Γ Γ') {A} : Subst Φ (Γ.cons A) (Γ'.cons A)
  | _, .here => .hyp .here
  | A, .there u => (γ A u).rename .weakening

def True.subst (γ : Subst Φ Γ Γ') {A} : (D : True Φ Γ A) → True Φ Γ' A
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
  | forallI D => forallI (D.subst (γ.rename .there))
  | forallE D t => forallE (D.subst γ) t
  | existsI t D => existsI t (D.subst γ)
  | existsE D D₁ => existsE (D.subst γ) (D₁.subst (γ.rename .there |>.cons))

end ND

-- Verifications and Uses
namespace VU

mutual

inductive Verif : ∀ Φ, (Γ : Ctx Φ) → (A : Propn Φ) → Type
  | uv (D : Use Φ Γ (.base P xs)) : Verif Φ Γ (.base P xs)
  | trueI : Verif Φ Γ .true
  | falseE (D : Use Φ Γ .false) : Verif Φ Γ C
  | andI (D₁ : Verif Φ Γ A) (D₂ : Verif Φ Γ B) : Verif Φ Γ (A.and B)
  | orI₁ (D : Verif Φ Γ A) : Verif Φ Γ (A.or B)
  | orI₂ (D : Verif Φ Γ B) : Verif Φ Γ (.or A B)
  | orE (D : Use Φ Γ (A.or B)) (D₁ : Verif Φ (Γ.cons A) C) (D₂ : Verif Φ (Γ.cons B) C) : Verif Φ Γ C
  | impI (D : Verif Φ (Γ.cons A) B) : Verif Φ Γ (A.imp B)
  | forallI (D : Verif (.cons Φ) (Γ.rename .there) A) : Verif Φ Γ (.forall A)
  | existsI (t : ElemMem Φ) (D : Verif Φ Γ (A.rename (.mk t))) : Verif Φ Γ (.exists A)
  | existsE (D : Use Φ Γ (.exists A)) (D₁ : Verif Φ.cons (Γ.rename .there |>.cons A) (C.rename .there)) : Verif Φ Γ C

inductive Use : ∀ Φ, (Γ : Ctx Φ) → (A : Propn Φ) → Type
  | hyp (u : Mem Φ A Γ) : Use Φ Γ A
  | andE₁ (D : Use Φ Γ (A.and B)) : Use Φ Γ A
  | andE₂ (D : Use Φ Γ (.and A B)) : Use Φ Γ B
  | impE (D : Use Φ Γ (A.imp B)) (D₁ : Verif Φ Γ A) : Use Φ Γ B
  | forallE (D : Use Φ Γ (.forall A)) (t : ElemMem Φ) : Use Φ Γ (A.rename (.mk t))

end

mutual

def Verif.renameElem (φ : ElemRename Φ Φ') {Γ A} : (D : Verif Φ Γ A) → Verif Φ' (Γ.rename φ) (A.rename φ)
  | .uv D => .uv (D.renameElem φ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.renameElem φ)
  | .andI D₁ D₂ => .andI (D₁.renameElem φ) (D₂.renameElem φ)
  | .orI₁ D => .orI₁ (D.renameElem φ)
  | .orI₂ D => .orI₂ (D.renameElem φ)
  | .orE D D₁ D₂ => .orE (D.renameElem φ) (D₁.renameElem φ) (D₂.renameElem φ)
  | .impI D => .impI (D.renameElem φ)
  | .forallI D => .forallI (have := D.renameElem φ.cons; by simp at this ⊢; exact this)
  | .existsI t D => .existsI (φ t) (have := D.renameElem φ; by simp at this ⊢; exact this)
  | .existsE D D₁ => .existsE (D.renameElem φ) (have := D₁.renameElem φ.cons; by simp! at this ⊢; exact this)

def Use.renameElem (φ : ElemRename Φ Φ') {Γ A} : (D : Use Φ Γ A) → Use Φ' (Γ.rename φ) (A.rename φ)
  | .hyp u => .hyp (u.rename φ)
  | .andE₁ D => .andE₁ (D.renameElem φ)
  | .andE₂ D => .andE₂ (D.renameElem φ)
  | .impE D D₁ => .impE (D.renameElem φ) (D₁.renameElem φ)
  | .forallE D t => have := Use.forallE (D.renameElem φ) (φ t); by simp at this ⊢; exact this

end

mutual

def Verif.rename (γ : Rename Φ Γ Γ') {A} : (D : Verif Φ Γ A) → Verif Φ Γ' A
  | .uv D => .uv (D.rename γ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.rename γ)
  | .andI D₁ D₂ => .andI (D₁.rename γ) (D₂.rename γ)
  | .orI₁ D => .orI₁ (D.rename γ)
  | .orI₂ D => .orI₂ (D.rename γ)
  | .orE D D₁ D₂ => .orE (D.rename γ) (D₁.rename γ.cons) (D₂.rename γ.cons)
  | .impI D => .impI (D.rename γ.cons)
  | .forallI D => .forallI (D.rename (γ.rename .there))
  | .existsI t D => .existsI t (D.rename γ)
  | .existsE D D₁ => .existsE (D.rename γ) (D₁.rename (γ.rename .there |>.cons))

def Use.rename (γ : Rename Φ Γ Γ') {A} : (D : Use Φ Γ A) → Use Φ Γ' A
  | .hyp u => .hyp (γ A u)
  | .andE₁ D => .andE₁ (D.rename γ)
  | .andE₂ D => .andE₂ (D.rename γ)
  | .impE D D₁ => .impE (D.rename γ) (D₁.rename γ)
  | .forallE D t => .forallE (D.rename γ) t

end

def Subst Φ (Γ Γ' : Ctx Φ) : Type :=
  ∀ A, (u : Mem Φ A Γ) → Use Φ Γ' A

def Subst.rename (φ : ElemRename Φ Φ') (γ : Subst Φ Γ Γ') : Subst Φ' (Γ.rename φ) (Γ'.rename φ)
  | A, u =>
  match Γ, A, u with
  | .cons .., _, .here => (γ _ .here).renameElem φ
  | .cons .., _, .there u => rename φ (fun A u => γ A u.there) _ u

def Subst.mk (D : Use Φ Γ A) : Subst Φ (Γ.cons A) Γ
  | _, .here => D
  | _, .there u => .hyp u

def Subst.cons (γ : Subst Φ Γ Γ') {A} : Subst Φ (Γ.cons A) (Γ'.cons A)
  | _, .here => .hyp .here
  | A, .there u => (γ A u).rename .weakening

mutual

def Verif.subst (γ : Subst Φ Γ Γ') {A} : (D : Verif Φ Γ A) → Verif Φ Γ' A
  | .uv D => .uv (D.subst γ)
  | .trueI => .trueI
  | .falseE D => .falseE (D.subst γ)
  | .andI D₁ D₂ => .andI (D₁.subst γ) (D₂.subst γ)
  | .orI₁ D => .orI₁ (D.subst γ)
  | .orI₂ D => .orI₂ (D.subst γ)
  | .orE D D₁ D₂ => .orE (D.subst γ) (D₁.subst γ.cons) (D₂.subst γ.cons)
  | .impI D => .impI (D.subst γ.cons)
  | .forallI D => .forallI (D.subst (γ.rename .there))
  | .existsI t D => .existsI t (D.subst γ)
  | .existsE D D₁ => .existsE (D.subst γ) (D₁.subst (γ.rename .there |>.cons))

def Use.subst (γ : Subst Φ Γ Γ') {A} : (D : Use Φ Γ A) → Use Φ Γ' A
  | .hyp u => γ A u
  | .andE₁ D => .andE₁ (D.subst γ)
  | .andE₂ D => .andE₂ (D.subst γ)
  | .impE D D₁ => .impE (D.subst γ) (D₁.subst γ)
  | .forallE D t => .forallE (D.subst γ) t

end

def Verif.uv' (D : Use Φ Γ A) : Verif Φ Γ A :=
  match A with
  | .base .. => uv D
  | .true => trueI
  | .false => falseE D
  | .and .. => andI (uv' (.andE₁ D)) (uv' (.andE₂ D))
  | .or .. => orE D (orI₁ (uv' (.hyp .here))) (orI₂ (uv' (.hyp .here)))
  | .imp .. => impI (uv' (.impE (D.rename .weakening) (uv' (.hyp .here))))
  | .forall _ => forallI (uv' (have := Use.forallE (D.renameElem .there) .here; by simp at this; exact this))
  | .exists _ => existsE D (existsI .here (by simp; exact uv' (.hyp .here)))

def Subst' Φ (Γ Γ' : Ctx Φ) : Type :=
  ∀ A, (u : Mem Φ A Γ) → Verif Φ Γ' A

def Subst'.cons (γ : Subst' Φ Γ Γ') {A} : Subst' Φ (Γ.cons A) (Γ'.cons A)
  | _, .here => .uv' (.hyp .here)
  | A, .there u => (γ A u).rename .weakening

mutual

def Verif.toTrue : (D : Verif Φ Γ A) → ND.True Φ Γ A
  | .uv D => D.toTrue
  | .trueI => .trueI
  | .falseE D => .falseE D.toTrue
  | .andI D₁ D₂ => .andI D₁.toTrue D₂.toTrue
  | .orI₁ D => .orI₁ D.toTrue
  | .orI₂ D => .orI₂ D.toTrue
  | .orE D D₁ D₂ => .orE D.toTrue D₁.toTrue D₂.toTrue
  | .impI D => .impI D.toTrue
  | .forallI D => .forallI D.toTrue
  | .existsI t D => .existsI t D.toTrue
  | .existsE D D₁ => .existsE D.toTrue D₁.toTrue

def Use.toTrue : (D : Use Φ Γ A) → ND.True Φ Γ A
  | .hyp u => .hyp u
  | .andE₁ D => .andE₁ D.toTrue
  | .andE₂ D => .andE₂ D.toTrue
  | .impE D D₁ => .impE D.toTrue D₁.toTrue
  | .forallE D t => .forallE D.toTrue t

end

def Subst.toTrue (γ : Subst Φ Γ Γ') : ND.Subst Φ Γ Γ'
  | A, u => (γ A u).toTrue

def Subst'.toTrue (γ : Subst' Φ Γ Γ') : ND.Subst Φ Γ Γ'
  | A, u => (γ A u).toTrue

end VU

-- Sequent Calculus
namespace SC

inductive Seq : ∀ Φ, (Γ : Ctx Φ) → (A : Propn Φ) → Type
  | id (u : Mem Φ (.base P xs) Γ) : Seq Φ Γ (.base P xs)
  | trueR : Seq Φ Γ .true
  | falseL (u : Mem Φ .false Γ) : Seq Φ Γ C
  | andR (D₁ : Seq Φ Γ A) (D₂ : Seq Φ Γ B) : Seq Φ Γ (A.and B)
  | andL₁ (u : Mem Φ (A.and B) Γ) (D : Seq Φ (Γ.cons A) C) : Seq Φ Γ C
  | andL₂ (u : Mem Φ (.and A B) Γ) (D : Seq Φ (Γ.cons B) C) : Seq Φ Γ C
  | orR₁ (D : Seq Φ Γ A) : Seq Φ Γ (A.or B)
  | orR₂ (D : Seq Φ Γ B) : Seq Φ Γ (.or A B)
  | orL (u : Mem Φ (A.or B) Γ) (D₁ : Seq Φ (Γ.cons A) C) (D₂ : Seq Φ (Γ.cons B) C) : Seq Φ Γ C
  | impR (D : Seq Φ (Γ.cons A) B) : Seq Φ Γ (A.imp B)
  | impL (u : Mem Φ (A.imp B) Γ) (D₁ : Seq Φ Γ A) (D₂ : Seq Φ (Γ.cons B) C) : Seq Φ Γ C
  | forallR (D : Seq (.cons Φ) (Γ.rename .there) A) : Seq Φ Γ (.forall A)
  | forallL (u : Mem Φ (.forall A) Γ) (t : ElemMem Φ) (D : Seq Φ (Γ.cons (A.rename (.mk t))) C) : Seq Φ Γ C
  | existsR (t : ElemMem Φ) (D : Seq Φ Γ (A.rename (.mk t))) : Seq Φ Γ (.exists A)
  | existsL (u : Mem Φ (.exists A) Γ) (D : Seq Φ.cons (Γ.rename .there |>.cons A) (C.rename .there)) : Seq Φ Γ C

def Seq.renameElem (φ : ElemRename Φ Φ') {Γ A} : (D : Seq Φ Γ A) → Seq Φ' (Γ.rename φ) (A.rename φ)
  | id u => id (u.rename φ)
  | trueR => trueR
  | falseL u => falseL (u.rename φ)
  | andR D₁ D₂ => andR (D₁.renameElem φ) (D₂.renameElem φ)
  | andL₁ u D => andL₁ (u.rename φ) (D.renameElem φ)
  | andL₂ u D => andL₂ (u.rename φ) (D.renameElem φ)
  | orR₁ D => orR₁ (D.renameElem φ)
  | orR₂ D => orR₂ (D.renameElem φ)
  | orL u D₁ D₂ => orL (u.rename φ) (D₁.renameElem φ) (D₂.renameElem φ)
  | impR D => impR (D.renameElem φ)
  | impL u D₁ D₂ => impL (u.rename φ) (D₁.renameElem φ) (D₂.renameElem φ)
  | forallR D => forallR (have := D.renameElem φ.cons; by simp at this ⊢; exact this)
  | forallL u t D => forallL (u.rename φ) (φ t) (have := D.renameElem φ; by simp! at this ⊢; exact this)
  | existsR t D => existsR (φ t) (have := D.renameElem φ; by simp at this ⊢; exact this)
  | existsL u D => existsL (u.rename φ) (have := D.renameElem φ.cons; by simp! at this ⊢; exact this)

def Seq.rename (γ : Rename Φ Γ Γ') {A} : (D : Seq Φ Γ A) → Seq Φ Γ' A
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
  | forallR D => forallR (D.rename (γ.rename .there))
  | forallL u t D => forallL (γ _ u) t (D.rename γ.cons)
  | existsR t D => existsR t (D.rename γ)
  | existsL u D => existsL (γ _ u) (D.rename (γ.rename .there |>.cons))

def Seq.id' (u : Mem Φ A Γ) : Seq Φ Γ A :=
  match A with
  | .base .. => id u
  | .true => trueR
  | .false => falseL u
  | .and .. => andR (andL₁ u (id' .here)) (andL₂ u (id' .here))
  | .or .. => orL u (orR₁ (id' .here)) (orR₂ (id' .here))
  | .imp .. => impR (impL u.there (id' .here) (id' .here))
  | .forall _ => forallR (forallL (u.rename .there) .here (id' (by simp; exact .here)))
  | .exists _ => existsL u (existsR .here (by simp; exact id' .here))

@[simp]
def Seq.sizeOf : (D : Seq Φ Γ A) → Nat
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
  | forallR D => D.sizeOf + 1
  | forallL _ _ D => D.sizeOf + 1
  | existsR _ D => D.sizeOf + 1
  | existsL _ D => D.sizeOf + 1

theorem Seq.sizeOf_cast {D : Seq Φ Γ A} (hΓ : Γ = Γ' := by simp!) (hA : A = A' := by simp!) : sizeOf (cast (congr (congrArg (Seq Φ) hΓ) hA) D) = sizeOf D :=
  by cases hΓ; cases hA; rfl

@[simp]
theorem Seq.sizeOf_renameElem {φ : ElemRename Φ Φ'} (D : Seq Φ Γ A) : (D.renameElem φ).sizeOf = D.sizeOf :=
  by induction D generalizing Φ' <;> simp [*] <;> rw [sizeOf_cast] <;> simp [*]

@[simp]
theorem Seq.sizeOf_rename {γ : Rename Φ Γ Γ'} (D : Seq Φ Γ A) : (D.rename γ).sizeOf = D.sizeOf :=
  by induction D <;> simp [*]

def Seq.cut : (D : Seq Φ Γ A) → (E : Seq Φ (Γ.cons A) C) → Seq Φ Γ C
  | id u, E => E.rename (.contraction u)
  | D, id .here => D
  | _, id (.there u) => id u
  | D@(andR D₁ _), andL₁ .here E => cut D₁ (cut (D.rename .weakening) (E.rename .exchange))
  | D@(andR _ D₂), andL₂ .here E => cut D₂ (cut (D.rename .weakening) (E.rename .exchange))
  | D@(orR₁ D₁), orL .here E₁ _ => cut D₁ (cut (D.rename .weakening) (E₁.rename .exchange))
  | D@(orR₂ D₂), orL .here _ E₂ => cut D₂ (cut (D.rename .weakening) (E₂.rename .exchange))
  | D@(impR D₂), impL .here E₁ E₂ => cut (cut (cut D E₁) D₂) (cut (D.rename .weakening) (E₂.rename .exchange))
  | D@(forallR D₁), forallL .here t E => cut (have := D₁.renameElem (.mk t); by simp! at this; exact this) (cut (D.rename .weakening) (E.rename .exchange))
  | D@(existsR t D₁), existsL .here E => cut D₁ (cut (D.rename .weakening) (have := E.renameElem (.mk t) |>.rename .exchange; by simp! at this; exact this))
  | falseL u, _ => falseL u
  | andL₁ u D, E => andL₁ u (cut D (E.rename (.cons .weakening)))
  | andL₂ u D, E => andL₂ u (cut D (E.rename (.cons .weakening)))
  | orL u D₁ D₂, E => orL u (cut D₁ (E.rename (.cons .weakening))) (cut D₂ (E.rename (.cons .weakening)))
  | impL u D₁ D₂, E => impL u D₁ (cut D₂ (E.rename (.cons .weakening)))
  | forallL u t D, E => forallL u t (cut D (E.rename (.cons .weakening)))
  | existsL u D, E => existsL u (cut D (E.renameElem .there |>.rename (.cons .weakening)))
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
  | D, forallR E => forallR (cut (D.renameElem .there) E)
  | D, forallL (.there u) t E => forallL u t (cut (D.rename .weakening) (E.rename .exchange))
  | D, existsR t E => existsR t (cut D E)
  | D, existsL (.there u) E => existsL u (cut (D.renameElem .there |>.rename .weakening) (E.rename .exchange))
  termination_by D E => (A.sizeOf, D.sizeOf, E.sizeOf)
  decreasing_by all_goals subst_vars; decreasing_with first | decreasing_trivial | rw [sizeOf_cast]; simp

def Subst Φ (Γ Γ' : Ctx Φ) : Type :=
  ∀ A, (u : Mem Φ A Γ) → Seq Φ Γ' A

def Seq.multicut (γ : Subst Φ Γ Γ') {A} (D : Seq Φ (Γ'.append Γ) A) : Seq Φ Γ' A :=
  match Γ with
  | .nil => D
  | .cons _ A => multicut (fun A u => γ A u.there) (cut ((γ A .here).rename .append₁) D)

def Seq.subst (γ : Subst Φ Γ Γ') {A} (D : Seq Φ Γ A) : Seq Φ Γ' A :=
  multicut γ (D.rename .append₂)

def Seq.toVerif : (D : Seq Φ Γ A) → VU.Verif Φ Γ A
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
  | forallR D => .forallI D.toVerif
  | forallL u t D => D.toVerif.subst (.mk (.forallE (.hyp u) t))
  | existsR t D => .existsI t D.toVerif
  | existsL u D => .existsE (.hyp u) D.toVerif

def Subst.toVerif (γ : Subst Φ Γ Γ') : VU.Subst' Φ Γ Γ'
  | A, u => (γ A u).toVerif

end SC

def ND.True.toSeq : (D : True Φ Γ A) → SC.Seq Φ Γ A
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
  | forallI D => .forallR D.toSeq
  | forallE D t => .cut D.toSeq (.forallL .here t (.id' .here))
  | existsI t D => .existsR t D.toSeq
  | existsE D D₁ => .cut D.toSeq (.existsL .here (D₁.toSeq.rename (.cons .weakening)))

def ND.Subst.toSeq (γ : Subst Φ Γ Γ') : SC.Subst Φ Γ Γ'
  | A, u => (γ A u).toSeq

def VU.Verif.subst' (γ : Subst' Φ Γ Γ') {A} (D : Verif Φ Γ A) : Verif Φ Γ' A :=
  (D.toTrue.toSeq.subst γ.toTrue.toSeq).toVerif
