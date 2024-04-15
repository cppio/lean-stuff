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
def cons (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .zero
  | _, .succ x => .succ (γ x)

@[simp]
def rename (γ : Renaming Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x        => .var (γ x)
  | .abort M      => .abort (γ.rename M)
  | .triv         => .triv
  | .inl M        => .inl (γ.rename M)
  | .inr M        => .inr (γ.rename M)
  | .case M M₁ M₂ => .case (γ.rename M) (γ.cons.rename M₁) (γ.cons.rename M₂)
  | .pair M₁ M₂   => .pair (γ.rename M₁) (γ.rename M₂)
  | .prl M        => .prl (γ.rename M)
  | .prr M        => .prr (γ.rename M)
  | .lam M        => .lam (γ.cons.rename M)
  | .ap M M₁      => .ap (γ.rename M) (γ.rename M₁)

end Renaming

@[simp]
def Exp.weaken : (M : Exp Γ A) → Exp (Γ.cons A') A :=
  Renaming.rename fun _ => .succ

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Exp Γ A

namespace Subst

@[simp]
def cons (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .var .zero
  | _, .succ x => .weaken (γ x)

@[simp]
def subst (γ : Subst Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x        => γ x
  | .abort M      => .abort (γ.subst M)
  | .triv         => .triv
  | .inl M        => .inl (γ.subst M)
  | .inr M        => .inr (γ.subst M)
  | .case M M₁ M₂ => .case (γ.subst M) (γ.cons.subst M₁) (γ.cons.subst M₂)
  | .pair M₁ M₂   => .pair (γ.subst M₁) (γ.subst M₂)
  | .prl M        => .prl (γ.subst M)
  | .prr M        => .prr (γ.subst M)
  | .lam M        => .lam (γ.cons.subst M)
  | .ap M M₁      => .ap (γ.subst M) (γ.subst M₁)

@[simp]
def extend (γ : Subst Γ Γ') (M : Exp Γ A) : Subst Γ (Γ'.cons A)
  | _, .zero   => M
  | _, .succ x => γ x

end Subst

@[simp]
def Exp.subst (M : Exp (Γ.cons A') A) (M' : Exp Γ A') : Exp Γ A :=
  Subst.extend (fun _ => .var) M' |>.subst M

@[simp]
def Exp.subst₁₁ (M : Exp (.cons Γ A') A) (M' : Exp (Γ.cons A₁) A') : Exp (Γ.cons A₁) A :=
  Subst.extend (fun _ x => .var x.succ) M' |>.subst M

section

local macro "lemma" M:ident Γ:ident Γ':ident : tactic =>
  `(tactic| (
    induction $M generalizing $Γ $Γ'
      <;> simp [*]
      <;> (try constructor)
      <;> congr
      <;> funext _ x
      <;> cases x
      <;> simp
  ))

@[simp]
theorem Renaming.rename_rename (γ : Renaming Γ Γ') (γ' : Renaming Γ' Γ'') : γ.rename (γ'.rename M) = rename (fun A x => γ (γ' x)) M :=
  by lemma M Γ Γ'

@[simp]
theorem Subst.subst_rename (γ : Subst Γ Γ') (γ' : Renaming Γ' Γ'') : γ.subst (γ'.rename M) = subst (fun A x => γ (γ' x)) M :=
  by lemma M Γ Γ'

@[simp]
theorem Subst.rename_subst (γ : Renaming Γ Γ') (γ' : Subst Γ' Γ'') : γ.rename (γ'.subst M) = subst (fun A x => γ.rename (γ' x)) M :=
  by lemma M Γ Γ'

@[simp]
theorem Subst.subst_subst (γ : Subst Γ Γ') (γ' : Subst Γ' Γ'') : γ.subst (γ'.subst M) = subst (fun A x => γ.subst (γ' x)) M :=
  by lemma M Γ Γ'

end

@[simp]
theorem Subst.cons_var : cons (Γ := Γ) (A := A) (fun _ => .var) = fun _ => .var := by
  funext _ x
  cases x
    <;> simp

@[simp]
theorem Subst.subst_var : subst (fun _ => .var) M = M := by
  induction M
    <;> simp [*]

macro "lemma" : tactic => `(tactic| simp <;> congr <;> funext _ x <;> cases x <;> simp)

inductive Steps : (M M' : Exp .nil A) → Type
  | abort (s : Steps M M') : Steps (.abort M)      (.abort M')
  | case  (s : Steps M M') : Steps (.case M M₁ M₂) (.case M' M₁ M₂)
  | prl   (s : Steps M M') : Steps (.prl M)        (.prl M')
  | prr   (s : Steps M M') : Steps (.prr M)        (.prr M')
  | ap    (s : Steps M M') : Steps (.ap M M₁)      (.ap M' M₁)

  | case_inl : Steps (.case (.inl M) M₁ M₂) (M₁.subst M)
  | case_inr : Steps (.case (.inr M) M₁ M₂) (M₂.subst M)
  | prl_pair : Steps (.prl (.pair M₁ M₂))   M₁
  | prr_pair : Steps (.prr (.pair M₁ M₂))   M₂
  | ap_lam   : Steps (.ap (.lam M) M₁)      (M.subst M₁)

theorem Steps.deterministic (s₁ : Steps M M₁) (s₂ : Steps M M₂) : M₁ = M₂ := by
  induction s₁
    <;> rename_i s₁ ih
    <;> cases s₂
    <;> (try cases s₁; done)
    <;> rename_i s₂
    <;> (try cases s₂; done)
    <;> congr
    <;> exact ih s₂

inductive Val : (M : Exp .nil A) → Type
  | triv : Val .triv
  | inl  : Val (.inl M)
  | inr  : Val (.inr M)
  | pair : Val (.pair M₁ M₂)
  | lam  : Val (.lam M)

inductive Reduces : (M M' : Exp .nil A) → Type
  | refl                                       : Reduces M M
  | step (s : Steps M M') (r : Reduces M' M'') : Reduces M M''

namespace Reduces

def trans : (r : Reduces M M') → (r' : Reduces M' M'') → Reduces M M''
  | refl,     r' => r'
  | step s r, r' => step s (r.trans r')

def comp {F : (M : Exp .nil A) → Exp .nil B} (f : ∀ {M M'}, (s : Steps M M') → Steps (F M) (F M')) : (r : Reduces M M') → Reduces (F M) (F M')
  | refl     => refl
  | step s r => step (f s) (r.comp f)

def abort : (r : Reduces M M') → Reduces (A := A) (.abort M)      (.abort M')      := comp .abort
def case  : (r : Reduces M M') → Reduces          (.case M M₁ M₂) (.case M' M₁ M₂) := comp .case
def prl   : (r : Reduces M M') → Reduces          (.prl M)        (.prl M')        := comp .prl
def prr   : (r : Reduces M M') → Reduces          (.prr M)        (.prr M')        := comp .prr
def ap    : (r : Reduces M M') → Reduces          (.ap M M₁)      (.ap M' M₁)      := comp .ap

def case_inl : Reduces (.case (.inl M) M₁ M₂) (M₁.subst M) := step .case_inl refl
def case_inr : Reduces (.case (.inr M) M₁ M₂) (M₂.subst M) := step .case_inr refl
def prl_pair : Reduces (.prl (.pair M₁ M₂))   M₁           := step .prl_pair refl
def prr_pair : Reduces (.prr (.pair M₁ M₂))   M₂           := step .prr_pair refl
def ap_lam   : Reduces (.ap (.lam M) M₁)      (M.subst M₁) := step .ap_lam   refl

theorem deterministic (r₁ : Reduces M M₁) (r₂ : Reduces M M₂) (v₁ : Val M₁) (v₂ : Val M₂) : M₁ = M₂ := by
  induction r₁ with
  | refl =>
    cases r₂ with
    | refl => rfl
    | step s₂ r₂ => nomatch (v₁, s₂)
  | step s₁ _ ih =>
    cases r₂ with
    | refl => nomatch (v₂, s₁)
    | step s₂ r₂ =>
      cases s₁.deterministic s₂
      exact ih r₂ v₁

end Reduces

def HT : ∀ A, (M : Exp .nil A) → Type
  | .void,       _ => Empty
  | .unit,       M => Reduces M .triv
  | .sum  A₁ A₂, M => (Σ M₁, HT A₁ M₁ × Reduces M (.inl M₁)) ⊕ (Σ M₂, HT A₂ M₂ × Reduces M (.inr M₂))
  | .prod A₁ A₂, M => Σ M₁, HT A₁ M₁ × Σ M₂, HT A₂ M₂ × Reduces M (.pair M₁ M₂)
  | .arr  A₁ A₂, M => Σ M₂, (∀ {M₁}, (ht₁ : HT A₁ M₁) → HT A₂ (M₂.subst M₁)) × Reduces M (.lam M₂)

def HT.expand : ∀ {A M₁ M₂}, (r₁ : Reduces M₁ M₂) → (ht₂ : HT A M₂) → HT A M₁
  | .unit,     _, _, r₁, r₂                   => r₁.trans r₂
  | .sum  _ _, _, _, r₁, .inl ⟨_, ht₁, r₂⟩    => .inl ⟨_, ht₁, r₁.trans r₂⟩
  | .sum  _ _, _, _, r₁, .inr ⟨_, ht₂, r₂⟩    => .inr ⟨_, ht₂, r₁.trans r₂⟩
  | .prod _ _, _, _, r₁, ⟨_, ht₁, _, ht₂, r₂⟩ => ⟨_, ht₁, _, ht₂, r₁.trans r₂⟩
  | .arr  _ _, _, _, r₁, ⟨_, ht₂, r₂⟩         => ⟨_, ht₂, r₁.trans r₂⟩

def HTSubst (γ : Subst .nil Γ) : Type :=
  ∀ {A} x, HT A (γ x)

def HTSubst.extend (ht_γ : HTSubst γ) (ht : HT A M) : HTSubst (γ.extend M)
  | _, .zero   => ht
  | _, .succ x => ht_γ x

def HT' Γ A (M : Exp Γ A) : Type :=
  ∀ {γ}, (ht_γ : HTSubst γ) → HT A (γ.subst M)

def ftlr : ∀ M, HT' Γ A M
  | .var x,        _, ht_γ => ht_γ x
  | .abort M,      γ, ht_γ => nomatch ftlr M ht_γ
  | .triv,         _, ht_γ => .refl
  | .inl M,        γ, ht_γ => .inl ⟨_, ftlr M ht_γ, .refl⟩
  | .inr M,        γ, ht_γ => .inr ⟨_, ftlr M ht_γ, .refl⟩
  | .case M M₁ M₂, γ, ht_γ => match ftlr M ht_γ with
                              | .inl ⟨_, ht₁, r⟩ => .expand (.trans (.case r) .case_inl) <| cast (by lemma) <| ftlr M₁ (ht_γ.extend ht₁)
                              | .inr ⟨_, ht₂, r⟩ => .expand (.trans (.case r) .case_inr) <| cast (by lemma) <| ftlr M₂ (ht_γ.extend ht₂)
  | .pair M₁ M₂,   γ, ht_γ => ⟨_, ftlr M₁ ht_γ, _, ftlr M₂ ht_γ, .refl⟩
  | .prl M,        γ, ht_γ => match ftlr M ht_γ with
                              | ⟨_, ht₁, _, _, r⟩ => .expand (.trans (.prl r) .prl_pair) ht₁
  | .prr M,        γ, ht_γ => match ftlr M ht_γ with
                              | ⟨_, _, _, ht₂, r⟩ => .expand (.trans (.prr r) .prr_pair) ht₂
  | .lam M,        γ, ht_γ => ⟨_, fun ht₁ => cast (by lemma) <| ftlr M (ht_γ.extend ht₁), .refl⟩
  | .ap M M₁,      γ, ht_γ => match ftlr M ht_γ with
                              | ⟨_, ht₂, r⟩ => .expand (.trans (.ap r) .ap_lam) <| ht₂ (ftlr M₁ ht_γ)

def ExactEq : ∀ A, (M M' : Exp .nil A) → Type
  | .void,       _, _  => Empty
  | .unit,       M, M' => Reduces M .triv × Reduces M' .triv
  | .sum  A₁ A₂, M, M' => (Σ M₁ M₁', ExactEq A₁ M₁ M₁' × Reduces M (.inl M₁) × Reduces M' (.inl M₁')) ⊕ (Σ M₂ M₂', ExactEq A₂ M₂ M₂' × Reduces M (.inr M₂) × Reduces M' (.inr M₂'))
  | .prod A₁ A₂, M, M' => Σ M₁ M₁', ExactEq A₁ M₁ M₁' × Σ M₂ M₂', ExactEq A₂ M₂ M₂' × Reduces M (.pair M₁ M₂) × Reduces M' (.pair M₁' M₂')
  | .arr  A₁ A₂, M, M' => Σ M₂ M₂', (∀ {M₁ M₁'}, (eq : ExactEq A₁ M₁ M₁') → ExactEq A₂ (M₂.subst M₁) (M₂'.subst M₁')) × Reduces M (.lam M₂) × Reduces M' (.lam M₂')

namespace ExactEq

def expand : ∀ {A M₁ M₁' M₂ M₂'}, (r₁ : Reduces M₁ M₂) → (r₁' : Reduces M₁' M₂') → (eq₂ : ExactEq A M₂ M₂') → ExactEq A M₁ M₁'
  | .unit,     _, _, _, _, r₁, r₁', (r₂, r₂')                       => (r₁.trans r₂, r₁'.trans r₂')
  | .sum  _ _, _, _, _, _, r₁, r₁', .inl ⟨_, _, eq₁, r₂, r₂'⟩       => .inl ⟨_, _, eq₁, r₁.trans r₂, r₁'.trans r₂'⟩
  | .sum  _ _, _, _, _, _, r₁, r₁', .inr ⟨_, _, eq₂, r₂, r₂'⟩       => .inr ⟨_, _, eq₂, r₁.trans r₂, r₁'.trans r₂'⟩
  | .prod _ _, _, _, _, _, r₁, r₁', ⟨_, _, eq₁, _, _, eq₂, r₂, r₂'⟩ => ⟨_, _, eq₁, _, _, eq₂, r₁.trans r₂, r₁'.trans r₂'⟩
  | .arr  _ _, _, _, _, _, r₁, r₁', ⟨_, _, eq₂, r₂, r₂'⟩            => ⟨_, _, eq₂, r₁.trans r₂, r₁'.trans r₂'⟩

def symm : ∀ {A M M'}, (eq : ExactEq A M M') → ExactEq A M' M
  | .unit,     _, _, (r, r')                       => (r', r)
  | .sum  _ _, _, _, .inl ⟨_, _, eq₁, r, r'⟩       => .inl ⟨_, _, eq₁.symm, r', r⟩
  | .sum  _ _, _, _, .inr ⟨_, _, eq₂, r, r'⟩       => .inr ⟨_, _, eq₂.symm, r', r⟩
  | .prod _ _, _, _, ⟨_, _, eq₁, _, _, eq₂, r, r'⟩ => ⟨_, _, eq₁.symm, _, _, eq₂.symm, r', r⟩
  | .arr  _ _, _, _, ⟨_, _, eq₂, r, r'⟩            => ⟨_, _, fun eq₁ => eq₂ eq₁.symm |>.symm, r', r⟩

def trans : ∀ {A M M' M''}, (eq : ExactEq A M M') → (eq' : ExactEq A M' M'') → ExactEq A M M''
  | .unit,     _, _, _, (r, _),                         (_, r') => (r, r')
  | .sum  _ _, _, _, _, .inl ⟨_, _, eq₁, r, r''⟩,       .inl ⟨_, _, eq₁', r''', r'⟩ => match r''.deterministic r''' .inl .inl with
                                                                                       | rfl => .inl ⟨_, _, eq₁.trans eq₁', r, r'⟩
  | .sum  _ _, _, _, _, .inr ⟨_, _, eq₂, r, r''⟩,       .inr ⟨_, _, eq₂', r''', r'⟩ => match r''.deterministic r''' .inr .inr with
                                                                                       | rfl => .inr ⟨_, _, eq₂.trans eq₂', r, r'⟩
  | .sum  _ _, _, _, _, .inl ⟨_, _, _, _, r⟩,           .inr ⟨_, _, _, r', _⟩ => nomatch r.deterministic r' .inl .inr
  | .sum  _ _, _, _, _, .inr ⟨_, _, _, _, r⟩,           .inl ⟨_, _, _, r', _⟩ => nomatch r.deterministic r' .inr .inl
  | .prod _ _, _, _, _, ⟨_, _, eq₁, _, _, eq₂, r, r''⟩, ⟨_, _, eq₁', _, _, eq₂', r''', r'⟩ => match r''.deterministic r''' .pair .pair with
                                                                                              | rfl => ⟨_, _, eq₁.trans eq₁', _, _, eq₂.trans eq₂', r, r'⟩
  | .arr  _ _, _, _, _, ⟨_, _, eq₂, r, r''⟩,            ⟨_, _, eq₂', r''', r'⟩ => match r''.deterministic r''' .lam .lam with
                                                                                  | rfl => ⟨_, _, fun eq₁ => eq₂ (eq₁.trans eq₁.symm) |>.trans <| eq₂' eq₁, r, r'⟩

end ExactEq

def ExactEqSubst (γ γ' : Subst .nil Γ) : Type :=
  ∀ {A} x, ExactEq A (γ x) (γ' x)

namespace ExactEqSubst

def extend (eq_γ : ExactEqSubst γ γ') (eq : ExactEq A M M') : ExactEqSubst (γ.extend M) (γ'.extend M')
  | _, .zero   => eq
  | _, .succ x => eq_γ x

def symm (eq : ExactEqSubst γ γ') : ExactEqSubst γ' γ
  | _, x => eq x |>.symm

def trans (eq : ExactEqSubst γ γ') (eq' : ExactEqSubst γ' γ'') : ExactEqSubst γ γ''
  | _, x => eq x |>.trans <| eq' x

end ExactEqSubst

def ExactEq' Γ A (M M' : Exp Γ A) : Type :=
  ∀ {γ γ'}, (eq_γ : ExactEqSubst γ γ') → ExactEq A (γ.subst M) (γ'.subst M')

structure Congruence (R : ∀ Γ A, (M M' : Exp Γ A) → Type) where
  symm  (r : R Γ A M M')                     : R Γ A M' M
  trans (r : R Γ A M M') (r' : R Γ A M' M'') : R Γ A M M''

  var   x                                                                                       : R Γ A             (.var x)        (.var x)
  abort (r : R Γ .void M M')                                                                    : R Γ A             (.abort M)      (.abort M')
  triv                                                                                          : R Γ .unit         .triv           .triv
  inl   (r : R Γ A₁ M M')                                                                       : R Γ (.sum  A₁ A₂) (.inl M)        (.inl M')
  inr   (r : R Γ A₂ M M')                                                                       : R Γ (.sum  A₁ A₂) (.inr M)        (.inr M')
  case  (r : R Γ (.sum A₁ A₂) M M') (r₁ : R (Γ.cons A₁) A M₁ M₁') (r₂ : R (Γ.cons A₂) A M₂ M₂') : R Γ A             (.case M M₁ M₂) (.case M' M₁' M₂')
  pair  (r₁ : R Γ A₁ M₁ M₁') (r₂ : R Γ A₂ M₂ M₂')                                               : R Γ (.prod A₁ A₂) (.pair M₁ M₂)   (.pair M₁' M₂')
  prl   (r : R Γ (.prod A₁ A₂) M M')                                                            : R Γ A₁            (.prl M)        (.prl M')
  prr   (r : R Γ (.prod A₁ A₂) M M')                                                            : R Γ A₂            (.prr M)        (.prr M')
  lam   (r : R (.cons Γ A₁) A₂ M M')                                                            : R Γ (.arr  A₁ A₂) (.lam M)        (.lam M')
  ap    (r : R Γ (.arr A₁ A₂) M M') (r₁ : R Γ A₁ M₁ M₁')                                        : R Γ A₂            (.ap M M₁)      (.ap M' M₁')

def Congruence.refl (self : Congruence R) {Γ A} : ∀ M, R Γ A M M
  | .var x        => self.var x
  | .abort M      => self.abort (self.refl M)
  | .triv         => self.triv
  | .inl M        => self.inl (self.refl M)
  | .inr M        => self.inr (self.refl M)
  | .case M M₁ M₂ => self.case (self.refl M) (self.refl M₁) (self.refl M₂)
  | .pair M₁ M₂   => self.pair (self.refl M₁) (self.refl M₂)
  | .prl M        => self.prl (self.refl M)
  | .prr M        => self.prr (self.refl M)
  | .lam M        => self.lam (self.refl M)
  | .ap M M₁      => self.ap (self.refl M) (self.refl M₁)

def ExactEq'.congruence : Congruence ExactEq' where
  symm eq      γ γ' eq_γ := eq eq_γ.symm |>.symm
  trans eq eq' γ γ' eq_γ := eq (eq_γ.trans eq_γ.symm) |>.trans <| eq' eq_γ

  var x           γ γ' eq_γ := eq_γ x
  abort eq        γ γ' eq_γ := nomatch eq eq_γ
  triv                 _    := (.refl, .refl)
  inl eq          γ γ' eq_γ := .inl ⟨_, _, eq eq_γ, .refl, .refl⟩
  inr eq          γ γ' eq_γ := .inr ⟨_, _, eq eq_γ, .refl, .refl⟩
  case eq eq₁ eq₂ γ γ' eq_γ := match eq eq_γ with
                               | .inl ⟨_, _, eq₃, r, r'⟩ => .expand (.trans (.case r) .case_inl) (.trans (.case r') .case_inl) <| cast (by lemma) <| eq₁ (eq_γ.extend eq₃)
                               | .inr ⟨_, _, eq₃, r, r'⟩ => .expand (.trans (.case r) .case_inr) (.trans (.case r') .case_inr) <| cast (by lemma) <| eq₂ (eq_γ.extend eq₃)
  pair eq₁ eq₂    γ γ' eq_γ := ⟨_, _, eq₁ eq_γ, _, _, eq₂ eq_γ, .refl, .refl⟩
  prl eq          γ γ' eq_γ := match eq eq_γ with
                               | ⟨_, _, eq₁, _, _, _, r, r'⟩ => .expand (.trans (.prl r) .prl_pair) (.trans (.prl r') .prl_pair) eq₁
  prr eq          γ γ' eq_γ := match eq eq_γ with
                               | ⟨_, _, _, _, _, eq₂, r, r'⟩ => .expand (.trans (.prr r) .prr_pair) (.trans (.prr r') .prr_pair) eq₂
  lam eq          γ γ' eq_γ := ⟨_, _, fun eq₁ => cast (by lemma) <| eq (eq_γ.extend eq₁), .refl, .refl⟩
  ap eq eq₁       γ γ' eq_γ := match eq eq_γ with
                               | ⟨_, _, eq₂, r, r'⟩ => .expand (.trans (.ap r) .ap_lam) (.trans (.ap r') .ap_lam) <| eq₂ (eq₁ eq_γ)

inductive DefEq : ∀ Γ A, (M M' : Exp Γ A) → Type
  | symm  (eq : DefEq Γ A M M')                          : DefEq Γ A M' M
  | trans (eq : DefEq Γ A M M') (eq' : DefEq Γ A M' M'') : DefEq Γ A M M''

  | var   x                                                                                                      : DefEq Γ A             (.var x)        (.var x)
  | abort (eq : DefEq Γ .void M M')                                                                              : DefEq Γ A             (.abort M)      (.abort M')
  | triv                                                                                                         : DefEq Γ .unit         .triv           .triv
  | inl   (eq : DefEq Γ A₁ M M')                                                                                 : DefEq Γ (.sum  A₁ A₂) (.inl M)        (.inl M')
  | inr   (eq : DefEq Γ A₂ M M')                                                                                 : DefEq Γ (.sum  A₁ A₂) (.inr M)        (.inr M')
  | case  (eq : DefEq Γ (.sum A₁ A₂) M M') (eq₁ : DefEq (Γ.cons A₁) A M₁ M₁') (eq₂ : DefEq (Γ.cons A₂) A M₂ M₂') : DefEq Γ A             (.case M M₁ M₂) (.case M' M₁' M₂')
  | pair  (eq₁ : DefEq Γ A₁ M₁ M₁') (eq₂ : DefEq Γ A₂ M₂ M₂')                                                    : DefEq Γ (.prod A₁ A₂) (.pair M₁ M₂)   (.pair M₁' M₂')
  | prl   (eq : DefEq Γ (.prod A₁ A₂) M M')                                                                      : DefEq Γ A₁            (.prl M)        (.prl M')
  | prr   (eq : DefEq Γ (.prod A₁ A₂) M M')                                                                      : DefEq Γ A₂            (.prr M)        (.prr M')
  | lam   (eq : DefEq (.cons Γ A₁) A₂ M M')                                                                      : DefEq Γ (.arr  A₁ A₂) (.lam M)        (.lam M')
  | ap    (eq : DefEq Γ (.arr A₁ A₂) M M') (eq₁ : DefEq Γ A₁ M₁ M₁')                                             : DefEq Γ A₂            (.ap M M₁)      (.ap M' M₁')

  | case_inl M M₁ M₂ : DefEq Γ A  (.case (.inl M) M₁ M₂) (M₁.subst M)
  | case_inr M M₁ M₂ : DefEq Γ A  (.case (.inr M) M₁ M₂) (M₂.subst M)
  | prl_pair M₁ M₂   : DefEq Γ A₁ (.prl (.pair M₁ M₂))   M₁
  | prr_pair M₁ M₂   : DefEq Γ A₂ (.prr (.pair M₁ M₂))   M₂
  | ap_lam   M M₁    : DefEq Γ A₂ (.ap (.lam M) M₁)      (M.subst M₁)

  | void_η M M' : DefEq Γ A             (.subst M' M) (.abort M)
  | unit_η M    : DefEq Γ .unit         M             .triv
  | sum_η  M M' : DefEq Γ A             (.subst M' M) (.case M (M'.subst₁₁ (.inl (.var .zero))) (M'.subst₁₁ (.inr (.var .zero))))
  | prod_η M    : DefEq Γ (.prod A₁ A₂) M             (.pair (.prl M) (.prr M))
  | arr_η  M    : DefEq Γ (.arr  A₁ A₂) M             (.lam (.ap M.weaken (.var .zero)))

def DefEq.congruence : Congruence DefEq where
  symm  := symm
  trans := trans

  var   := var
  abort := abort
  triv  := triv
  inl   := inl
  inr   := inr
  case  := case
  pair  := pair
  prl   := prl
  prr   := prr
  lam   := lam
  ap    := ap

def ftlr₂ : (eq : DefEq Γ A M M') → ExactEq' Γ A M M'
  | .symm eq      => ExactEq'.congruence.symm (ftlr₂ eq)
  | .trans eq eq' => ExactEq'.congruence.trans (ftlr₂ eq) (ftlr₂ eq')

  | .var x           => ExactEq'.congruence.var x
  | .abort eq        => ExactEq'.congruence.abort (ftlr₂ eq)
  | .triv            => ExactEq'.congruence.triv
  | .inl eq          => ExactEq'.congruence.inl (ftlr₂ eq)
  | .inr eq          => ExactEq'.congruence.inr (ftlr₂ eq)
  | .case eq eq₁ eq₂ => ExactEq'.congruence.case (ftlr₂ eq) (ftlr₂ eq₁) (ftlr₂ eq₂)
  | .pair eq₁ eq₂    => ExactEq'.congruence.pair (ftlr₂ eq₁) (ftlr₂ eq₂)
  | .prl eq          => ExactEq'.congruence.prl (ftlr₂ eq)
  | .prr eq          => ExactEq'.congruence.prr (ftlr₂ eq)
  | .lam eq          => ExactEq'.congruence.lam (ftlr₂ eq)
  | .ap eq eq₁       => ExactEq'.congruence.ap (ftlr₂ eq) (ftlr₂ eq₁)

  | .case_inl M M₁ M₂ => fun eq_γ => .expand .case_inl .refl <| cast (by lemma) <| ExactEq'.congruence.refl (M₁.subst M) eq_γ
  | .case_inr M M₁ M₂ => fun eq_γ => .expand .case_inr .refl <| cast (by lemma) <| ExactEq'.congruence.refl (M₂.subst M) eq_γ
  | .prl_pair M₁ M₂   => fun eq_γ => .expand .prl_pair .refl <| ExactEq'.congruence.refl M₁ eq_γ
  | .prr_pair M₁ M₂   => fun eq_γ => .expand .prr_pair .refl <| ExactEq'.congruence.refl M₂ eq_γ
  | .ap_lam M M₁      => fun eq_γ => .expand .ap_lam .refl <| cast (by lemma) <| ExactEq'.congruence.refl (M.subst M₁) eq_γ

  | .void_η M M' => fun eq_γ => nomatch ExactEq'.congruence.refl M eq_γ
  | .unit_η M    => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | (r, _) => (r, .refl)
  | .sum_η M M'  => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | .inl ⟨_, _, eq₁, r, r'⟩ => .expand .refl (.trans (.case r') .case_inl) <| cast (by lemma) <| ExactEq'.congruence.refl M' (eq_γ.extend (A := .sum _ _) (.inl ⟨_, _, eq₁, r, .refl⟩))
                                | .inr ⟨_, _, eq₂, r, r'⟩ => .expand .refl (.trans (.case r') .case_inr) <| cast (by lemma) <| ExactEq'.congruence.refl M' (eq_γ.extend (A := .sum _ _) (.inr ⟨_, _, eq₂, r, .refl⟩))
  | .prod_η M    => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | ⟨_, _, eq₁, _, _, eq₂, r, r'⟩ => ⟨_, _, .expand .refl (.trans (.prl r') .prl_pair) eq₁, _, _, .expand .refl (.trans (.prr r') .prr_pair) eq₂, r, .refl⟩
  | .arr_η M     => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | ⟨_, _, eq₂, r, r'⟩ => ⟨_, _, fun eq₁ => cast (by lemma) <| ExactEq.expand .refl (.trans (.ap r') .ap_lam) <| eq₂ eq₁, r, .refl⟩

--def completeness : ExactEq' Γ A M M' → DefEq Γ A M M' := sorry

/-
def interpret : Typ → Typ
  | .void => .void
  | .unit => .unit
-/

/-
def decide : ∀ A, Exp Γ A → Exp (.cons Γ A) (.sum .unit .unit)
  | .void,       M => .abort (.var .zero)
  | .unit,       M => .inl .triv
  | .sum  A₁ A₂, M => .case (.var .zero) (have := @decide sorry A₁ sorry; sorry) sorry
  | .prod A₁ A₂, M => sorry
  | .arr  A₁ A₂, M => sorry
-/

/-
def enumerate : ∀ A, List (Exp .nil A)
  | .void       => []
  | .unit       => [.triv]
  | .sum  A₁ A₂ => (enumerate A₁).map .inl ++ (enumerate A₂).map .inr
  | .prod A₁ A₂ => enumerate A₁ |>.bind fun M₁ => enumerate A₂ |>.map fun M₂ => .pair M₁ M₂
  | .arr  A₁ A₂ => panic! "not implemented"
-/

/-
def ExactEq'' Γ A (M M' : Exp Γ A) : Type :=
  {γ : Subst _ Γ} → ExactEq A (γ.subst M) (γ.subst M')

def to'' (eq : ExactEq' Γ A M M') : ExactEq'' Γ A M M'
  | γ => eq fun x => subst (fun M => ExactEq _ M M) Subst.subst_var <| ExactEq'.congruence.refl (γ x) nofun

def completeness'' : ExactEq'' Γ A M M' → DefEq Γ A M M' := sorry

def eq_of_steps : (s : Steps (A := A) M₁ M₂) → DefEq .nil A M₁ M₂
  | .abort s => .abort _ _ (eq_of_steps s)
  | .case  s => .case _ _ _ _ _ _ (eq_of_steps s) (DefEq.congruence.refl _) (DefEq.congruence.refl _)
  | .prl   s => .prl _ _ (eq_of_steps s)
  | .prr   s => .prr _ _ (eq_of_steps s)
  | .ap    s => .ap _ _ _ _ (eq_of_steps s) (DefEq.congruence.refl _)

  | .case_inl => .case_inl
  | .case_inr => .case_inr
  | .prl_pair => .prl_pair
  | .prr_pair => .prr_pair
  | .ap_lam   => .ap_lam

def eq_of_reduces : (r : Reduces (A := A) M₁ M₂) → DefEq .nil A M₁ M₂
  | .refl     => DefEq.congruence.refl _
  | .step s r => .trans (eq_of_steps s) (eq_of_reduces r)

def completeness' : ∀ {A M M'}, ExactEq A M M' → DefEq .nil A M M'
  | .unit,     _, _, (r, r')                       => eq_of_reduces r |>.trans <| eq_of_reduces r' |>.symm
  | .sum  _ _, _, _, .inl ⟨_, _, eq₁, r, r'⟩       => eq_of_reduces r |>.trans (.inl _ _ (completeness' eq₁)) |>.trans <| eq_of_reduces r' |>.symm
  | .sum  _ _, _, _, .inr ⟨_, _, eq₂, r, r'⟩       => eq_of_reduces r |>.trans (.inr _ _ (completeness' eq₂)) |>.trans <| eq_of_reduces r' |>.symm
  | .prod _ _, _, _, ⟨_, _, eq₁, _, _, eq₂, r, r'⟩ => eq_of_reduces r |>.trans (.pair _ _ _ _ (completeness' eq₁) (completeness' eq₂)) |>.trans <| eq_of_reduces r' |>.symm
  | .arr  _ _, _, _, ⟨_, _, eq₂, r, r'⟩            => have := fun {M₂} => @eq₂ M₂ M₂ (subst (fun M => ExactEq _ M M) Subst.subst_var <| ExactEq'.congruence.refl M₂ nofun); sorry
-/

-- TODO: observational equality
