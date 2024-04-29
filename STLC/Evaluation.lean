import STLC.Basic

namespace STLC.Evaluation

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

theorem Val.not_steps : Val M → Steps M M' → False :=
  nofun

def progress : (M : Exp .nil A) → Val M ⊕ Σ M', Steps M M'
  | .abort M      => .inr <|
                     match progress M with
                     | .inr ⟨_, s⟩ => ⟨_, .abort s⟩
  | .triv         => .inl .triv
  | .inl M        => .inl .inl
  | .inr M        => .inl .inr
  | .case M M₁ M₂ => .inr <|
                     match progress M with
                     | .inl .inl => ⟨_, .case_inl⟩
                     | .inl .inr => ⟨_, .case_inr⟩
                     | .inr ⟨_, s⟩ => ⟨_, .case s⟩
  | .pair M₁ M₂   => .inl .pair
  | .prl M        => .inr <|
                     match progress M with
                     | .inl .pair => ⟨_, .prl_pair⟩
                     | .inr ⟨_, s⟩ => ⟨_, .prl s⟩
  | .prr M        => .inr <|
                     match progress M with
                     | .inl .pair => ⟨_, .prr_pair⟩
                     | .inr ⟨_, s⟩ => ⟨_, .prr s⟩
  | .lam M        => .inl .lam
  | .ap M M₁      => .inr <|
                     match progress M with
                     | .inl .lam => ⟨_, .ap_lam⟩
                     | .inr ⟨_, s⟩ => ⟨_, .ap s⟩

inductive Reduces : (M M' : Exp .nil A) → Type
  | refl                                       : Reduces M M
  | step (s : Steps M M') (r : Reduces M' M'') : Reduces M M''

namespace Reduces

def trans : (r : Reduces M M') → (r' : Reduces M' M'') → Reduces M M''
  | refl,     r' => r'
  | step s r, r' => step s (r.trans r')

def lift {F : (M : Exp .nil A) → Exp .nil A'} (f : ∀ {M M'}, (s : Steps M M') → Steps (F M) (F M')) : (r : Reduces M M') → Reduces (F M) (F M')
  | refl     => refl
  | step s r => step (f s) (r.lift f)

def abort : (r : Reduces M M') → Reduces (A := A) (.abort M)      (.abort M')      := lift .abort
def case  : (r : Reduces M M') → Reduces          (.case M M₁ M₂) (.case M' M₁ M₂) := lift .case
def prl   : (r : Reduces M M') → Reduces          (.prl M)        (.prl M')        := lift .prl
def prr   : (r : Reduces M M') → Reduces          (.prr M)        (.prr M')        := lift .prr
def ap    : (r : Reduces M M') → Reduces          (.ap M M₁)      (.ap M' M₁)      := lift .ap

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
    | step s₂ r₂ => nomatch v₁.not_steps s₂
  | step s₁ _ ih =>
    cases r₂ with
    | refl => nomatch v₂.not_steps s₁
    | step s₂ r₂ =>
      cases s₁.deterministic s₂
      exact ih r₂ v₁

end Reduces

namespace Termination

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
  | .arr  _ _, _, _, r₁, ⟨_, ht, r₂⟩          => ⟨_, ht, r₁.trans r₂⟩

def HTSubst (γ : Subst .nil Γ) : Type :=
  ∀ {A} x, HT A (γ x)

def HTSubst.cons (ht_γ : HTSubst γ) (ht : HT A M) : HTSubst (γ.cons M)
  | _, .zero   => ht
  | _, .succ x => ht_γ x

def HT' Γ A (M : Exp Γ A) : Type :=
  ∀ {γ}, (ht_γ : HTSubst γ) → HT A (γ.apply M)

def ftlr : ∀ M, HT' Γ A M
  | .var x,        _, ht_γ => ht_γ x
  | .abort M,      γ, ht_γ => nomatch ftlr M ht_γ
  | .triv,         _, ht_γ => .refl
  | .inl M,        γ, ht_γ => .inl ⟨_, ftlr M ht_γ, .refl⟩
  | .inr M,        γ, ht_γ => .inr ⟨_, ftlr M ht_γ, .refl⟩
  | .case M M₁ M₂, γ, ht_γ => match ftlr M ht_γ with
                              | .inl ⟨_, ht₁, r⟩ => .expand (.trans (.case r) .case_inl) <| cast (by lemma) <| ftlr M₁ (ht_γ.cons ht₁)
                              | .inr ⟨_, ht₂, r⟩ => .expand (.trans (.case r) .case_inr) <| cast (by lemma) <| ftlr M₂ (ht_γ.cons ht₂)
  | .pair M₁ M₂,   γ, ht_γ => ⟨_, ftlr M₁ ht_γ, _, ftlr M₂ ht_γ, .refl⟩
  | .prl M,        γ, ht_γ => match ftlr M ht_γ with
                              | ⟨_, ht₁, _, _, r⟩ => .expand (.trans (.prl r) .prl_pair) ht₁
  | .prr M,        γ, ht_γ => match ftlr M ht_γ with
                              | ⟨_, _, _, ht₂, r⟩ => .expand (.trans (.prr r) .prr_pair) ht₂
  | .lam M,        γ, ht_γ => ⟨_, fun ht₁ => cast (by lemma) <| ftlr M (ht_γ.cons ht₁), .refl⟩
  | .ap M M₁,      γ, ht_γ => match ftlr M ht_γ with
                              | ⟨_, ht₂, r⟩ => .expand (.trans (.ap r) .ap_lam) <| ht₂ (ftlr M₁ ht_γ)

def termination (M : Exp .nil A) : Σ M', Val M' × Reduces M M' :=
  match A, M, Subst.apply_var.ndrec <| ftlr M nofun with
  | .unit,     _, r               => ⟨_, .triv, r⟩
  | .sum  _ _, _, .inl ⟨_, _, r⟩  => ⟨_, .inl, r⟩
  | .sum  _ _, _, .inr ⟨_, _, r⟩  => ⟨_, .inr, r⟩
  | .prod _ _, _, ⟨_, _, _, _, r⟩ => ⟨_, .pair, r⟩
  | .arr  _ _, _, ⟨_, _, r⟩       => ⟨_, .lam, r⟩

end Termination

namespace Equality

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
  | .arr  _ _, _, _, _, _, r₁, r₁', ⟨_, _, eq, r₂, r₂'⟩             => ⟨_, _, eq, r₁.trans r₂, r₁'.trans r₂'⟩

def symm : ∀ {A M M'}, (eq : ExactEq A M M') → ExactEq A M' M
  | .unit,     _, _, (r, r')                       => (r', r)
  | .sum  _ _, _, _, .inl ⟨_, _, eq₁, r, r'⟩       => .inl ⟨_, _, eq₁.symm, r', r⟩
  | .sum  _ _, _, _, .inr ⟨_, _, eq₂, r, r'⟩       => .inr ⟨_, _, eq₂.symm, r', r⟩
  | .prod _ _, _, _, ⟨_, _, eq₁, _, _, eq₂, r, r'⟩ => ⟨_, _, eq₁.symm, _, _, eq₂.symm, r', r⟩
  | .arr  _ _, _, _, ⟨_, _, eq, r, r'⟩             => ⟨_, _, fun eq₁ => eq eq₁.symm |>.symm, r', r⟩

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
  | .arr  _ _, _, _, _, ⟨_, _, eq, r, r''⟩,             ⟨_, _, eq', r''', r'⟩  => match r''.deterministic r''' .lam .lam with
                                                                                  | rfl => ⟨_, _, fun eq₁ => eq (eq₁.trans eq₁.symm) |>.trans <| eq' eq₁, r, r'⟩

end ExactEq

def ExactEqSubst (γ γ' : Subst .nil Γ) : Type :=
  ∀ {A} x, ExactEq A (γ x) (γ' x)

namespace ExactEqSubst

def cons (eq_γ : ExactEqSubst γ γ') (eq : ExactEq A M M') : ExactEqSubst (γ.cons M) (γ'.cons M')
  | _, .zero   => eq
  | _, .succ x => eq_γ x

def symm (eq : ExactEqSubst γ γ') : ExactEqSubst γ' γ
  | _, x => eq x |>.symm

def trans (eq : ExactEqSubst γ γ') (eq' : ExactEqSubst γ' γ'') : ExactEqSubst γ γ''
  | _, x => eq x |>.trans <| eq' x

end ExactEqSubst

def ExactEq' Γ A (M M' : Exp Γ A) : Type :=
  ∀ {γ γ'}, (eq_γ : ExactEqSubst γ γ') → ExactEq A (γ.apply M) (γ'.apply M')

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
                               | .inl ⟨_, _, eq₃, r, r'⟩ => .expand (.trans (.case r) .case_inl) (.trans (.case r') .case_inl) <| cast (by lemma) <| eq₁ (eq_γ.cons eq₃)
                               | .inr ⟨_, _, eq₃, r, r'⟩ => .expand (.trans (.case r) .case_inr) (.trans (.case r') .case_inr) <| cast (by lemma) <| eq₂ (eq_γ.cons eq₃)
  pair eq₁ eq₂    γ γ' eq_γ := ⟨_, _, eq₁ eq_γ, _, _, eq₂ eq_γ, .refl, .refl⟩
  prl eq          γ γ' eq_γ := match eq eq_γ with
                               | ⟨_, _, eq₁, _, _, _, r, r'⟩ => .expand (.trans (.prl r) .prl_pair) (.trans (.prl r') .prl_pair) eq₁
  prr eq          γ γ' eq_γ := match eq eq_γ with
                               | ⟨_, _, _, _, _, eq₂, r, r'⟩ => .expand (.trans (.prr r) .prr_pair) (.trans (.prr r') .prr_pair) eq₂
  lam eq          γ γ' eq_γ := ⟨_, _, fun eq₁ => cast (by lemma) <| eq (eq_γ.cons eq₁), .refl, .refl⟩
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
  | sum_η  M M' : DefEq Γ A             (.subst M' M) (.case M (M'.subst₁ (.inl (.var .zero))) (M'.subst₁ (.inr (.var .zero))))
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

def ftlr : (eq : DefEq Γ A M M') → ExactEq' Γ A M M'
  | .symm eq      => ExactEq'.congruence.symm (ftlr eq)
  | .trans eq eq' => ExactEq'.congruence.trans (ftlr eq) (ftlr eq')

  | .var x           => ExactEq'.congruence.var x
  | .abort eq        => ExactEq'.congruence.abort (ftlr eq)
  | .triv            => ExactEq'.congruence.triv
  | .inl eq          => ExactEq'.congruence.inl (ftlr eq)
  | .inr eq          => ExactEq'.congruence.inr (ftlr eq)
  | .case eq eq₁ eq₂ => ExactEq'.congruence.case (ftlr eq) (ftlr eq₁) (ftlr eq₂)
  | .pair eq₁ eq₂    => ExactEq'.congruence.pair (ftlr eq₁) (ftlr eq₂)
  | .prl eq          => ExactEq'.congruence.prl (ftlr eq)
  | .prr eq          => ExactEq'.congruence.prr (ftlr eq)
  | .lam eq          => ExactEq'.congruence.lam (ftlr eq)
  | .ap eq eq₁       => ExactEq'.congruence.ap (ftlr eq) (ftlr eq₁)

  | .case_inl M M₁ M₂ => fun eq_γ => .expand .case_inl .refl <| cast (by lemma) <| ExactEq'.congruence.refl (M₁.subst M) eq_γ
  | .case_inr M M₁ M₂ => fun eq_γ => .expand .case_inr .refl <| cast (by lemma) <| ExactEq'.congruence.refl (M₂.subst M) eq_γ
  | .prl_pair M₁ M₂   => fun eq_γ => .expand .prl_pair .refl <| ExactEq'.congruence.refl M₁ eq_γ
  | .prr_pair M₁ M₂   => fun eq_γ => .expand .prr_pair .refl <| ExactEq'.congruence.refl M₂ eq_γ
  | .ap_lam M M₁      => fun eq_γ => .expand .ap_lam .refl <| cast (by lemma) <| ExactEq'.congruence.refl (M.subst M₁) eq_γ

  | .void_η M M' => fun eq_γ => nomatch ExactEq'.congruence.refl M eq_γ
  | .unit_η M    => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | (r, _) => (r, .refl)
  | .sum_η M M'  => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | .inl ⟨_, _, eq₁, r, r'⟩ => .expand .refl (.trans (.case r') .case_inl) <| cast (by lemma) <| ExactEq'.congruence.refl M' (eq_γ.cons (A := .sum _ _) (.inl ⟨_, _, eq₁, r, .refl⟩))
                                | .inr ⟨_, _, eq₂, r, r'⟩ => .expand .refl (.trans (.case r') .case_inr) <| cast (by lemma) <| ExactEq'.congruence.refl M' (eq_γ.cons (A := .sum _ _) (.inr ⟨_, _, eq₂, r, .refl⟩))
  | .prod_η M    => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | ⟨_, _, eq₁, _, _, eq₂, r, r'⟩ => ⟨_, _, .expand .refl (.trans (.prl r') .prl_pair) eq₁, _, _, .expand .refl (.trans (.prr r') .prr_pair) eq₂, r, .refl⟩
  | .arr_η M     => fun eq_γ => match ExactEq'.congruence.refl M eq_γ with
                                | ⟨_, _, eq₂, r, r'⟩ => ⟨_, _, fun eq₁ => cast (by lemma) <| ExactEq.expand .refl (.trans (.ap r') .ap_lam) <| eq₂ eq₁, r, .refl⟩

-- TODO: CCC = observational = definitional = exact

end Equality
