namespace STLC

inductive Typ
  | void
  | unit
  | sum  (A₁ A₂ : Typ)
  | prod (A₁ A₂ : Typ)
  | arr  (A₁ A₂ : Typ)

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Typ)

inductive Var (A : Typ) : (Γ : Ctx) → Type
  | zero               : Var A (.cons Γ A)
  | succ (x : Var A Γ) : Var A (.cons Γ A')

inductive Exp : (Γ : Ctx) → (A : Typ) → Type
  | var   (x : Var A Γ)                                                              : Exp Γ A
  | abort (M : Exp Γ .void)                                                          : Exp Γ A
  | triv                                                                             : Exp Γ .unit
  | inl   (M : Exp Γ A₁)                                                             : Exp Γ (.sum A₁ A₂)
  | inr   (M : Exp Γ A₂)                                                             : Exp Γ (.sum A₁ A₂)
  | case  (M : Exp Γ (.sum A₁ A₂)) (M₁ : Exp (Γ.cons A₁) A) (M₂ : Exp (Γ.cons A₂) A) : Exp Γ A
  | pair  (M₁ : Exp Γ A₁) (M₂ : Exp Γ A₂)                                            : Exp Γ (.prod A₁ A₂)
  | prl   (M : Exp Γ (.prod A₁ A₂))                                                  : Exp Γ A₁
  | prr   (M : Exp Γ (.prod A₁ A₂))                                                  : Exp Γ A₂
  | lam   (M : Exp (Γ.cons A₁) A₂)                                                   : Exp Γ (.arr A₁ A₂)
  | ap    (M : Exp Γ (.arr A₁ A₂)) (M₁ : Exp Γ A₁)                                   : Exp Γ A₂

def Renaming (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Var A Γ

namespace Renaming

@[simp]
def cons (γ : Renaming Γ Γ') (y : Var A Γ) : Renaming Γ (Γ'.cons A)
  | _, .zero   => y
  | _, .succ x => γ x

@[simp]
def weaken (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A) :=
  cons (fun _ x => .succ (γ x)) .zero

@[simp]
def apply (γ : Renaming Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x        => .var (γ x)
  | .abort M      => .abort (γ.apply M)
  | .triv         => .triv
  | .inl M        => .inl (γ.apply M)
  | .inr M        => .inr (γ.apply M)
  | .case M M₁ M₂ => .case (γ.apply M) (γ.weaken.apply M₁) (γ.weaken.apply M₂)
  | .pair M₁ M₂   => .pair (γ.apply M₁) (γ.apply M₂)
  | .prl M        => .prl (γ.apply M)
  | .prr M        => .prr (γ.apply M)
  | .lam M        => .lam (γ.weaken.apply M)
  | .ap M M₁      => .ap (γ.apply M) (γ.apply M₁)

@[simp]
theorem weaken_id : cons (Γ := .cons Γ A) (fun _ => .succ) .zero = fun _ x => x := by
  funext _ x
  cases x
    <;> simp

@[simp]
theorem apply_id : apply (fun _ x => x) M = M := by
  induction M
    <;> simp [*]

end Renaming

@[simp]
def Exp.weaken : (M : Exp Γ A) → Exp (Γ.cons A') A :=
  Renaming.apply fun _ => .succ

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Exp Γ A

namespace Subst

@[simp]
def cons (γ : Subst Γ Γ') (M : Exp Γ A) : Subst Γ (Γ'.cons A)
  | _, .zero   => M
  | _, .succ x => γ x

@[simp]
def weaken (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A) :=
  cons (fun _ x => (γ x).weaken) (.var .zero)

@[simp]
def apply (γ : Subst Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x        => γ x
  | .abort M      => .abort (γ.apply M)
  | .triv         => .triv
  | .inl M        => .inl (γ.apply M)
  | .inr M        => .inr (γ.apply M)
  | .case M M₁ M₂ => .case (γ.apply M) (γ.weaken.apply M₁) (γ.weaken.apply M₂)
  | .pair M₁ M₂   => .pair (γ.apply M₁) (γ.apply M₂)
  | .prl M        => .prl (γ.apply M)
  | .prr M        => .prr (γ.apply M)
  | .lam M        => .lam (γ.weaken.apply M)
  | .ap M M₁      => .ap (γ.apply M) (γ.apply M₁)

@[simp]
theorem weaken_var : cons (Γ := .cons Γ A) (fun _ x => .var x.succ) (.var .zero) = fun _ => .var := by
  funext _ x
  cases x
    <;> simp

@[simp]
theorem apply_var : apply (fun _ => .var) M = M := by
  induction M
    <;> simp [*]

theorem cons_renaming (γ : Renaming Γ Γ') (y : Var A Γ) : cons (fun _ x => .var (γ x)) (.var y) = fun _ x => .var (Renaming.cons γ y x) := by
  funext _ x
  cases x
    <;> simp

@[simp]
theorem apply_renaming (γ : Renaming Γ Γ') : apply (fun _ x => .var (γ x)) M = γ.apply M := by
  induction M generalizing Γ
    <;> simp [cons_renaming, *]
    <;> constructor
    <;> rfl

end Subst

@[simp]
def Exp.subst (M : Exp (Γ.cons A') A) (M' : Exp Γ A') : Exp Γ A :=
  Subst.cons (fun _ => var) M' |>.apply M

@[simp]
def Exp.subst₁ (M : Exp (.cons Γ A') A) (M' : Exp (Γ.cons A'') A') : Exp (Γ.cons A'') A :=
  Subst.cons (fun _ x => var x.succ) M' |>.apply M

section

local macro "lemma" M:ident Γ:ident Γ':ident : tactic =>
  `(tactic|
    induction $M generalizing $Γ $Γ'
      <;> simp [*]
      <;> (try constructor)
      <;> congr
      <;> funext _ x
      <;> cases x
      <;> simp
  )

@[simp]
theorem Renaming.rename_rename (γ : Renaming Γ Γ') (γ' : Renaming Γ' Γ'') : γ.apply (γ'.apply M) = apply (fun A x => γ (γ' x)) M :=
  by lemma M Γ Γ'

@[simp]
theorem Subst.subst_rename (γ : Subst Γ Γ') (γ' : Renaming Γ' Γ'') : γ.apply (γ'.apply M) = apply (fun A x => γ (γ' x)) M :=
  by lemma M Γ Γ'

@[simp]
theorem Subst.rename_subst (γ : Renaming Γ Γ') (γ' : Subst Γ' Γ'') : γ.apply (γ'.apply M) = apply (fun A x => γ.apply (γ' x)) M :=
  by lemma M Γ Γ'

@[simp]
theorem Subst.subst_subst (γ : Subst Γ Γ') (γ' : Subst Γ' Γ'') : γ.apply (γ'.apply M) = apply (fun A x => γ.apply (γ' x)) M :=
  by lemma M Γ Γ'

end

macro "lemma" : tactic =>
  `(tactic|
    simp
      <;> congr
      <;> funext _ x
      <;> cases x
      <;> simp
  )
