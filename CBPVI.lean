inductive Polarity
  | pos
  | neg

inductive Typ : (p : Polarity) → Type
  | void                     : Typ .pos
  | unitP                    : Typ .pos
  | sum   (A₁ A₂ : Typ .pos) : Typ .pos
  | prodP (A₁ A₂ : Typ .pos) : Typ .pos
  | U     (X : Typ .neg)     : Typ .pos

  | unitN                               : Typ .neg
  | prodN (X₁ X₂ : Typ .neg)            : Typ .neg
  | arr   (A : Typ .pos) (X : Typ .neg) : Typ .neg
  | F     (A : Typ .pos)                : Typ .neg

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Typ .pos)

inductive Var (A : Typ .pos) : (Γ : Ctx) → Type
  | zero               : Var A (.cons Γ A)
  | succ (x : Var A Γ) : Var A (.cons Γ A')

inductive Exp : (Γ : Ctx) → (AX : Typ p) → Type
  | var   (x : Var A Γ)                   : Exp Γ A
  | trivP                                 : Exp Γ .unitP
  | inl   (V : Exp Γ A₁)                  : Exp Γ (.sum A₁ A₂)
  | inr   (V : Exp Γ A₂)                  : Exp Γ (.sum A₁ A₂)
  | pairP (V₁ : Exp Γ A₁) (V₂ : Exp Γ A₂) : Exp Γ (.prodP A₁ A₂)
  | susp  (C : Exp Γ X)                   : Exp Γ (.U X)

  | abort (V : Exp Γ .void)                                                          : @Exp .neg Γ X
  | check (V : Exp Γ .unitP) (C : Exp Γ X)                                           : @Exp .neg Γ X
  | case  (V : Exp Γ (.sum A₁ A₂)) (C₁ : Exp (Γ.cons A₁) X) (C₂ : Exp (Γ.cons A₂) X) : @Exp .neg Γ X
  | split (V : Exp Γ (.prodP A₁ A₂)) (C : Exp (Γ.cons A₁ |>.cons A₂) X)              : @Exp .neg Γ X
  | force (V : Exp Γ (.U X))                                                         : Exp Γ X

  | trivN                                            : Exp Γ .unitN
  | pairN (C₁ : Exp Γ X₁) (C₂ : Exp Γ X₂)            : Exp Γ (.prodN X₁ X₂)
  | prl   (C : Exp Γ (.prodN X₁ X₂))                 : Exp Γ X₁
  | prr   (C : Exp Γ (.prodN X₁ X₂))                 : Exp Γ X₂
  | lam   (C : Exp (Γ.cons A) X)                     : Exp Γ (.arr A X)
  | ap    (C : Exp Γ (.arr A X)) (V : Exp Γ A)       : Exp Γ X
  | ret   (V : Exp Γ A)                              : Exp Γ (.F A)
  | bind  (C : Exp Γ (.F A)) (C₁ : Exp (Γ.cons A) X) : @Exp .neg Γ X

def Renaming (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Var A Γ

namespace Renaming

@[simp]
def cons (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .zero
  | _, .succ x => .succ (γ x)

@[simp]
def rename (γ : Renaming Γ Γ') : (M : Exp Γ' AX) → Exp Γ AX
  | .var x       => .var (γ x)
  | .trivP       => .trivP
  | .inl V       => .inl (γ.rename V)
  | .inr V       => .inr (γ.rename V)
  | .pairP V₁ V₂ => .pairP (γ.rename V₁) (γ.rename V₂)
  | .susp C      => .susp (γ.rename C)

  | .abort V      => .abort (γ.rename V)
  | .check V C    => .check (γ.rename V) (γ.rename C)
  | .case V C₁ C₂ => .case (γ.rename V) (γ.cons.rename C₁) (γ.cons.rename C₂)
  | .split V C    => .split (γ.rename V) (γ.cons.cons.rename C)
  | .force V      => .force (γ.rename V)

  | .trivN       => .trivN
  | .pairN C₁ C₂ => .pairN (γ.rename C₁) (γ.rename C₂)
  | .prl C       => .prl (γ.rename C)
  | .prr C       => .prr (γ.rename C)
  | .lam C       => .lam (γ.cons.rename C)
  | .ap C V      => .ap (γ.rename C) (γ.rename V)
  | .ret V       => .ret (γ.rename V)
  | .bind C C₁   => .bind (γ.rename C) (γ.cons.rename C₁)

@[simp]
def extend (γ : Renaming Γ Γ') (x : Var A Γ) : Renaming Γ (Γ'.cons A)
  | _, .zero   => x
  | _, .succ x => γ x

end Renaming

@[simp]
def Exp.weaken : (M : Exp Γ AX) → Exp (Γ.cons A) AX :=
  Renaming.rename fun _ => .succ

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Exp Γ A

namespace Subst

@[simp]
def cons (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .var .zero
  | _, .succ x => .weaken (γ x)

@[simp]
def subst (γ : Subst Γ Γ') : (M : Exp Γ' AX) → Exp Γ AX
  | .var x       => γ x
  | .trivP       => .trivP
  | .inl V       => .inl (γ.subst V)
  | .inr V       => .inr (γ.subst V)
  | .pairP V₁ V₂ => .pairP (γ.subst V₁) (γ.subst V₂)
  | .susp C      => .susp (γ.subst C)

  | .abort V      => .abort (γ.subst V)
  | .check V C    => .check (γ.subst V) (γ.subst C)
  | .case V C₁ C₂ => .case (γ.subst V) (γ.cons.subst C₁) (γ.cons.subst C₂)
  | .split V C    => .split (γ.subst V) (γ.cons.cons.subst C)
  | .force V      => .force (γ.subst V)

  | .trivN       => .trivN
  | .pairN C₁ C₂ => .pairN (γ.subst C₁) (γ.subst C₂)
  | .prl C       => .prl (γ.subst C)
  | .prr C       => .prr (γ.subst C)
  | .lam C       => .lam (γ.cons.subst C)
  | .ap C V      => .ap (γ.subst C) (γ.subst V)
  | .ret V       => .ret (γ.subst V)
  | .bind C C₁   => .bind (γ.subst C) (γ.cons.subst C₁)

@[simp]
def extend (γ : Subst Γ Γ') (V : Exp Γ A) : Subst Γ (Γ'.cons A)
  | _, .zero   => V
  | _, .succ x => γ x

end Subst

@[simp]
def Exp.subst (M : Exp (Γ.cons A) AX) (V : Exp Γ A) : Exp Γ AX :=
  Subst.extend (fun _ => .var) V |>.subst M

@[simp]
def Exp.subst₂ (M : Exp (Γ.cons A₁ |>.cons A₂) AX) (V₁ : Exp Γ A₁) (V₂ : Exp Γ A₂) : Exp Γ AX :=
  Subst.extend (fun _ => .var) V₁ |>.extend V₂ |>.subst M

@[simp]
def Exp.subst₁₁ (M : Exp (.cons Γ A) AX) (V : Exp (Γ.cons A₁) A) : Exp (Γ.cons A₁) AX :=
  Subst.extend (fun _ x => .var x.succ) V |>.subst M

@[simp]
def Exp.subst₂₁ (M : Exp (.cons Γ A) AX) (V : Exp (Γ.cons A₁ |>.cons A₂) A) : Exp (Γ.cons A₁ |>.cons A₂) AX :=
  Subst.extend (fun _ x => .var x.succ.succ) V |>.subst M

@[simp]
def Exp.subst₂₂ (M : Exp (Ctx.cons Γ A₁ |>.cons A₂) AX) (V₁ : Exp (Γ.cons A' |>.cons A'') A₁) (V₂ : Exp (Γ.cons A' |>.cons A'') A₂) : Exp (Γ.cons A' |>.cons A'') AX :=
  Subst.extend (fun _ x => .var x.succ.succ) V₁ |>.extend V₂ |>.subst M

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
    cases ‹_›
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

macro "lemma" : tactic => `(tactic| simp <;> congr <;> funext _ x <;> cases x <;> simp <;> cases ‹_› <;> simp)

inductive Steps : (C C' : @Exp .neg .nil X) → Type
  | prl  (s : Steps C C') : Steps (.prl C)     (.prl C')
  | prr  (s : Steps C C') : Steps (.prr C)     (.prr C')
  | ap   (s : Steps C C') : Steps (.ap C V)    (.ap C' V)
  | bind (s : Steps C C') : Steps (.bind C C₁) (.bind C' C₁)

  | check_triv : Steps (.check .trivP C)         C
  | case_inl   : Steps (.case (.inl V) C₁ C₂)    (C₁.subst V)
  | case_inr   : Steps (.case (.inr V) C₁ C₂)    (C₂.subst V)
  | split_pair : Steps (.split (.pairP V₁ V₂) C) (C.subst₂ V₁ V₂)
  | force_susp : Steps (.force (.susp C))        C

  | prl_pair   : Steps (.prl (.pairN C₁ C₂))     C₁
  | prr_pair   : Steps (.prr (.pairN C₁ C₂))     C₂
  | ap_lam     : Steps (.ap (.lam C) V)          (C.subst V)
  | bind_ret   : Steps (.bind (.ret V) C)        (C.subst V)

theorem Steps.deterministic (s₁ : Steps C C₁) (s₂ : Steps C C₂) : C₁ = C₂ := by
  induction s₁
    <;> rename_i s₁ ih
    <;> cases s₂
    <;> (try cases s₁; done)
    <;> rename_i s₂
    <;> (try cases s₂; done)
    <;> congr
    <;> exact ih s₂

inductive Reduces : (C C' : @Exp .neg .nil A) → Type
  | refl                                       : Reduces C C
  | step (s : Steps C C') (r : Reduces C' C'') : Reduces C C''

namespace Reduces

def trans : (r : Reduces C C') → (r' : Reduces C' C'') → Reduces C C''
  | refl,     r' => r'
  | step s r, r' => step s (r.trans r')

def comp {F : (C : Exp .nil X) → Exp .nil Y} (f : ∀ {C C'}, (s : Steps C C') → Steps (F C) (F C')) : (r : Reduces C C') → Reduces (F C) (F C')
  | refl     => refl
  | step s r => step (f s) (r.comp f)

def prl  : (r : Reduces C C') → Reduces (.prl C)     (.prl C')     := comp .prl
def prr  : (r : Reduces C C') → Reduces (.prr C)     (.prr C')     := comp .prr
def ap   : (r : Reduces C C') → Reduces (.ap C V)    (.ap C' V)    := comp .ap
def bind : (r : Reduces C C') → Reduces (.bind C C₁) (.bind C' C₁) := comp .bind

def check_triv : Reduces (.check .trivP C)         C                := step .check_triv refl
def case_inl   : Reduces (.case (.inl V) C₁ C₂)    (C₁.subst V)     := step .case_inl   refl
def case_inr   : Reduces (.case (.inr V) C₁ C₂)    (C₂.subst V)     := step .case_inr   refl
def split_pair : Reduces (.split (.pairP V₁ V₂) C) (C.subst₂ V₁ V₂) := step .split_pair refl
def force_susp : Reduces (.force (.susp C))        C                := step .force_susp refl

def prl_pair   : Reduces (.prl (.pairN C₁ C₂))     C₁          := step .prl_pair refl
def prr_pair   : Reduces (.prr (.pairN C₁ C₂))     C₂          := step .prr_pair refl
def ap_lam     : Reduces (.ap (.lam C) V)          (C.subst V) := step .ap_lam   refl
def bind_ret   : Reduces (.bind (.ret V) C)        (C.subst V) := step .bind_ret refl

theorem deterministic (r₁ : Reduces C (.ret V₁)) (r₂ : Reduces C (.ret V₂)) : V₁ = V₂ := by
  generalize eq₁ : Exp.ret V₁ = C₁ at r₁
  induction r₁ with
  | refl =>
    subst eq₁
    cases r₂ with
    | refl => rfl
    | step s₂ r₂ => nomatch s₂
  | step s₁ r₁ ih =>
    subst eq₁
    cases r₂ with
    | refl => nomatch s₁
    | step s₂ r₂ =>
      cases s₁.deterministic s₂
      exact ih r₂ rfl

end Reduces

def HT : (AX : Typ p) → (M : Exp .nil AX) → Type
  | _, .trivP       => Unit
  | _, .inl V       => HT _ V
  | _, .inr V       => HT _ V
  | _, .pairP V₁ V₂ => HT _ V₁ × HT _ V₂
  | _, .susp C      => HT _ C

  | .unitN,       _ => Unit
  | .prodN X₁ X₂, C => HT X₁ (.prl C) × HT X₂ (.prr C)
  | .arr A X,     C => ∀ {V}, HT A V → HT X (.ap C V)
  | .F A,         C => Σ V, HT A V × Reduces C (.ret V)

def HT.expand : ∀ {X C₁ C₂}, (r₁ : Reduces C₁ C₂) → (ht₂ : HT X C₂) → HT X C₁
  | .unitN,       _, _, _,  ()          => ()
  | .prodN X₁ X₂, _, _, r₁, (ht₁, ht₂)  => (expand (.prl r₁) ht₁, expand (.prr r₁) ht₂)
  | .arr A X,     _, _, r₁, ht          => fun ht₁ => expand (.ap r₁) (ht ht₁)
  | .F A,         _, _, r₁, ⟨_, ht, r₂⟩ => ⟨_, ht, r₁.trans r₂⟩

def HTSubst (γ : Subst .nil Γ) : Type :=
  ∀ {{A}} x, HT A (γ x)

def HTSubst.extend (ht_γ : HTSubst γ) (ht : HT A V) : HTSubst (γ.extend V)
  | _, .zero   => ht
  | _, .succ x => ht_γ x

def HT' Γ (AX : Typ p) (M : Exp Γ AX) : Type :=
  ∀ {γ}, (ht_γ : HTSubst γ) → HT AX (γ.subst M)

def ftlr : ∀ M, HT' Γ AX M
  | .var x,       γ, ht_γ => ht_γ x
  | .trivP,       γ, ht_γ => ()
  | .inl V,       γ, ht_γ => ftlr V ht_γ
  | .inr V,       γ, ht_γ => ftlr V ht_γ
  | .pairP V₁ V₂, γ, ht_γ => (ftlr V₁ ht_γ, ftlr V₂ ht_γ)
  | .susp C,      γ, ht_γ => ftlr C ht_γ

  | .abort V,      γ, ht_γ => nomatch γ.subst V, ftlr V ht_γ
  | .check V C,    γ, ht_γ => show HT _ (.check ..) from
                              match γ.subst V, ftlr V ht_γ with
                              | .trivP, _ => .expand .check_triv <| ftlr C ht_γ
  | .case V C₁ C₂, γ, ht_γ => show HT _ (.case ..) from
                              match γ.subst V, ftlr V ht_γ with
                              | .inl V, ht => .expand .case_inl <| cast (by lemma) <| ftlr C₁ (ht_γ.extend ht)
                              | .inr V, ht => .expand .case_inr <| cast (by lemma) <| ftlr C₂ (ht_γ.extend ht)
  | .split V C,    γ, ht_γ => show HT _ (.split ..) from
                              match γ.subst V, ftlr V ht_γ with
                              | .pairP V₁ V₂, (ht₁, ht₂) => .expand .split_pair <| cast (by lemma) <| ftlr C (ht_γ.extend ht₁ |>.extend ht₂)
  | .force V,      γ, ht_γ => show HT _ (.force ..) from
                              match γ.subst V, ftlr V ht_γ with
                              | .susp C, ht => .expand .force_susp ht

  | .trivN,        γ, ht_γ => ()
  | .pairN C₁ C₂,  γ, ht_γ => (.expand .prl_pair <| ftlr C₁ ht_γ, .expand .prr_pair <| ftlr C₂ ht_γ)
  | .prl C,        γ, ht_γ => let (ht₁, _) := ftlr C ht_γ; ht₁
  | .prr C,        γ, ht_γ => let (_, ht₂) := ftlr C ht_γ; ht₂
  | .lam C,        γ, ht_γ => fun ht₁ => .expand .ap_lam <| cast (by lemma) <| ftlr C (ht_γ.extend ht₁)
  | .ap C V,       γ, ht_γ => ftlr C ht_γ (ftlr V ht_γ)
  | .ret V,        γ, ht_γ => ⟨_, ftlr V ht_γ, .refl⟩
  | .bind C C₁,    γ, ht_γ => let ⟨_, ht, r⟩ := ftlr C ht_γ; .expand (.trans (.bind r) .bind_ret) <| cast (by lemma) <| ftlr C₁ (ht_γ.extend ht)

def ExactEq : (AX : Typ p) → (M M' : Exp .nil AX) → Type
  | _, .trivP,       .trivP         => Unit
  | _, .inl V,       .inl V'        => ExactEq _ V V'
  | _, .inr V,       .inr V'        => ExactEq _ V V'
  | _, .inl _,       .inr _         => Empty
  | _, .inr _,       .inl _         => Empty
  | _, .pairP V₁ V₂, .pairP V₁' V₂' => ExactEq _ V₁ V₁' × ExactEq _ V₂ V₂'
  | _, .susp C,      .susp C'       => ExactEq _ C C'

  | .unitN,       _, _  => Unit
  | .prodN X₁ X₂, C, C' => ExactEq X₁ (.prl C) (.prl C') × ExactEq X₂ (.prr C) (.prr C')
  | .arr A X,     C, C' => ∀ {V V'}, ExactEq A V V' → ExactEq X (.ap C V) (.ap C' V')
  | .F A,         C, C' => Σ V V', ExactEq A V V' × Reduces C (.ret V) × Reduces C' (.ret V')

namespace ExactEq

def expand : ∀ {X C₁ C₁' C₂ C₂'}, (r₁ : Reduces C₁ C₂) → (r₁' : Reduces C₁' C₂') → (eq₂ : ExactEq X C₂ C₂') → ExactEq X C₁ C₁'
  | .unitN,       _, _, _, _, _,  _,   ()                  => ()
  | .prodN X₁ X₂, _, _, _, _, r₁, r₁', (eq₁, eq₂)          => (expand (.prl r₁) (.prl r₁') eq₁, expand (.prr r₁) (.prr r₁') eq₂)
  | .arr A X,     _, _, _, _, r₁, r₁', eq                  => fun eq₁ => expand (.ap r₁) (.ap r₁') (eq eq₁)
  | .F A,         _, _, _, _, r₁, r₁', ⟨_, _, eq, r₂, r₂'⟩ => ⟨_, _, eq, r₁.trans r₂, r₁'.trans r₂'⟩

set_option linter.unusedVariables false

def symm : ∀ {AX M M'}, (eq : @ExactEq p AX M M') → ExactEq AX M' M
  | .unitP,       .trivP,       .trivP,         ()         => ()
  | .sum A₁ A₂,   .inl V,       .inl V',        eq         => eq.symm (AX := A₁)
  | .sum A₁ A₂,   .inr V,       .inr V',        eq         => eq.symm (AX := A₂)
  | .prodP A₁ A₂, .pairP V₁ V₂, .pairP V₁' V₂', (eq₁, eq₂) => (eq₁.symm, eq₂.symm)
  | .U X,         .susp C,      .susp C',       eq         => eq.symm (AX := X)

  | .unitN,       _, _, ()                => ()
  | .prodN X₁ X₂, _, _, (eq₁, eq₂)        => (eq₁.symm, eq₂.symm)
  | .arr A X,     _, _, eq                => fun eq₁ => eq eq₁.symm |>.symm
  | .F A,         _, _, ⟨_, _, eq, r, r'⟩ => ⟨_, _, eq.symm, r', r⟩

def trans : ∀ {AX M M' M''}, (eq : @ExactEq p AX M M') → (eq' : ExactEq AX M' M'') → ExactEq AX M M''
  | .unitP,       .trivP,       .trivP,         .trivP,           (),         ()           => ()
  | .sum A₁ A₂,   .inl V,       .inl V',        .inl V'',         eq,         eq'          => eq.trans (AX := A₁) eq'
  | .sum A₁ A₂,   .inr V,       .inr V',        .inr V'',         eq,         eq'          => eq.trans (AX := A₂) eq'
  | .prodP A₁ A₂, .pairP V₁ V₂, .pairP V₁' V₂', .pairP V₁'' V₂'', (eq₁, eq₂), (eq₁', eq₂') => (eq₁.trans eq₁', eq₂.trans eq₂')
  | .U X,         .susp C,      .susp C',       .susp C'',        eq,         eq'          => eq.trans (AX := X) eq'

  | .unitN,       _, _, _, (),                 ()                    => ()
  | .prodN X₁ X₂, _, _, _, (eq₁, eq₂),         (eq₁', eq₂')          => (eq₁.trans eq₁', eq₂.trans eq₂')
  | .arr A X,     _, _, _, eq,                 eq'                   => fun eq₁ => eq (eq₁.trans eq₁.symm) |>.trans <| eq' eq₁
  | .F A,         _, _, _, ⟨_, _, eq, r, r''⟩, ⟨_, _, eq', r''', r'⟩ => match r''.deterministic r''' with
                                                                        | rfl => ⟨_, _, eq.trans eq', r, r'⟩

end ExactEq

def ExactEqSubst (γ γ' : Subst .nil Γ) : Type :=
  ∀ {{A}} x, ExactEq A (γ x) (γ' x)

namespace ExactEqSubst

def extend (eq_γ : ExactEqSubst γ γ') (eq : ExactEq A V V') : ExactEqSubst (γ.extend V) (γ'.extend V')
  | _, .zero   => eq
  | _, .succ x => eq_γ x

def symm (eq : ExactEqSubst γ γ') : ExactEqSubst γ' γ
  | _, x => eq x |>.symm

def trans (eq : ExactEqSubst γ γ') (eq' : ExactEqSubst γ' γ'') : ExactEqSubst γ γ''
  | _, x => eq x |>.trans <| eq' x

end ExactEqSubst

def ExactEq' Γ (AX : Typ p) (M M' : Exp Γ AX) : Type :=
  ∀ {γ γ'}, (eq_γ : ExactEqSubst γ γ') → ExactEq AX (γ.subst M) (γ'.subst M')

structure Congruence (R : ∀ {p} Γ (AX : Typ p), (M M' : Exp Γ AX) → Type) where
  symm  (r : R Γ AX M M')                      : R Γ AX M' M
  trans (r : R Γ AX M M') (r' : R Γ AX M' M'') : R Γ AX M M''

  var   x                                         : R Γ A              (.var x)       (.var x)
  trivP                                           : R Γ .unitP         .trivP         .trivP
  inl   (r : R Γ A₁ V V')                         : R Γ (.sum A₁ A₂)   (.inl V)       (.inl V')
  inr   (r : R Γ A₂ V V')                         : R Γ (.sum A₁ A₂)   (.inr V)       (.inr V')
  pairP (r₁ : R Γ A₁ V₁ V₁') (r₂ : R Γ A₂ V₂ V₂') : R Γ (.prodP A₁ A₂) (.pairP V₁ V₂) (.pairP V₁' V₂')
  susp  (r : R Γ X C C')                          : R Γ (.U X)         (.susp C)      (.susp C')

  abort (r : R Γ .void V V')                                                                    : R Γ X (.abort V)      (.abort V')
  check (r : R Γ .unitP V V') (r₁ : R Γ X C C')                                                 : R Γ X (.check V C)    (.check V' C')
  case  (r : R Γ (.sum A₁ A₂) V V') (r₁ : R (Γ.cons A₁) X C₁ C₁') (r₂ : R (Γ.cons A₂) X C₂ C₂') : R Γ X (.case V C₁ C₂) (.case V' C₁' C₂')
  split (r : R Γ (.prodP A₁ A₂) V V') (r₁ : R (Γ.cons A₁ |>.cons A₂) X C C')                    : R Γ X (.split V C)    (.split V' C')
  force (r : R Γ (.U X) V V')                                                                   : R Γ X (.force V)      (.force V')

  trivN                                                    : R Γ .unitN .trivN .trivN
  pairN (r₁ : R Γ X₁ C₁ C₁') (r₂ : R Γ X₂ C₂ C₂')          : R Γ (.prodN X₁ X₂) (.pairN C₁ C₂) (.pairN C₁' C₂')
  prl   (r : R Γ (.prodN X₁ X₂) C C')                      : R Γ X₁ (.prl C) (.prl C')
  prr   (r : R Γ (.prodN X₁ X₂) C C')                      : R Γ X₂ (.prr C) (.prr C')
  lam   (r : R (.cons Γ A) X C C')                         : R Γ (.arr A X) (.lam C) (.lam C')
  ap    (r : R Γ (.arr A X) C C') (r₁ : R Γ A V V')        : R Γ X (.ap C V) (.ap C' V')
  ret   (r : R Γ A V V')                                   : R Γ (.F A) (.ret V) (.ret V')
  bind  (r : R Γ (.F A) C C') (r₁ : R (Γ.cons A) X C₁ C₁') : R Γ X (.bind C C₁) (.bind C' C₁')

def Congruence.refl (self : Congruence R) {p Γ} {AX : Typ p} : ∀ M, R Γ AX M M
  | .var x       => self.var x
  | .trivP       => self.trivP
  | .inl V       => self.inl (self.refl V)
  | .inr V       => self.inr (self.refl V)
  | .pairP V₁ V₂ => self.pairP (self.refl V₁) (self.refl V₂)
  | .susp C      => self.susp (self.refl C)

  | .abort V      => self.abort (self.refl V)
  | .check V C    => self.check (self.refl V) (self.refl C)
  | .case V C₁ C₂ => self.case (self.refl V) (self.refl C₁) (self.refl C₂)
  | .split V C    => self.split (self.refl V) (self.refl C)
  | .force V      => self.force (self.refl V)

  | .trivN       => self.trivN
  | .pairN C₁ C₂ => self.pairN (self.refl C₁) (self.refl C₂)
  | .prl C       => self.prl (self.refl C)
  | .prr C       => self.prr (self.refl C)
  | .lam C       => self.lam (self.refl C)
  | .ap C V      => self.ap (self.refl C) (self.refl V)
  | .ret V       => self.ret (self.refl V)
  | .bind C C₁   => self.bind (self.refl C) (self.refl C₁)

def ExactEq'.congruence : Congruence ExactEq' where
  symm eq      γ γ' eq_γ := eq eq_γ.symm |>.symm
  trans eq eq' γ γ' eq_γ := eq (eq_γ.trans eq_γ.symm) |>.trans <| eq' eq_γ

  var x         γ γ' eq_γ := eq_γ x
  trivP              _    := ()
  inl eq        γ γ' eq_γ := eq eq_γ
  inr eq        γ γ' eq_γ := eq eq_γ
  pairP eq₁ eq₂ γ γ' eq_γ := (eq₁ eq_γ, eq₂ eq_γ)
  susp eq       γ γ' eq_γ := eq eq_γ

  abort eq        γ γ' eq_γ := nomatch γ.subst _, γ'.subst _, eq eq_γ
  check eq eq₁    γ γ' eq_γ := show ExactEq _ (.check ..) (.check ..) from
                               match γ.subst _, γ'.subst _, eq eq_γ with
                               | .trivP, .trivP, () => .expand .check_triv .check_triv <| eq₁ eq_γ
  case eq eq₁ eq₂ γ γ' eq_γ := show ExactEq _ (.case ..) (.case ..) from
                               match γ.subst _, γ'.subst _, eq eq_γ with
                               | .inl V, .inl V', eq => .expand .case_inl .case_inl <| cast (by lemma) <| eq₁ (eq_γ.extend eq)
                               | .inr V, .inr V', eq => .expand .case_inr .case_inr <| cast (by lemma) <| eq₂ (eq_γ.extend eq)
  split eq eq'    γ γ' eq_γ := show ExactEq _ (.split ..) (.split ..) from
                               match γ.subst _, γ'.subst _, eq eq_γ with
                               | .pairP V₁ V₂, .pairP V₁' V₂', (eq₁, eq₂) => .expand .split_pair .split_pair <| cast (by lemma) <| eq' (eq_γ.extend eq₁ |>.extend eq₂)
  force eq        γ γ' eq_γ := show ExactEq _ (.force ..) (.force ..) from
                               match γ.subst _, γ'.subst _, eq eq_γ with
                               | .susp C, .susp C', eq => .expand .force_susp .force_susp eq

  trivN              _    := ()
  pairN eq₁ eq₂ γ γ' eq_γ := (.expand .prl_pair .prl_pair <| eq₁ eq_γ, .expand .prr_pair .prr_pair <| eq₂ eq_γ)
  prl eq        γ γ' eq_γ := let (eq₁, _) := eq eq_γ; eq₁
  prr eq        γ γ' eq_γ := let (_, eq₂) := eq eq_γ; eq₂
  lam eq        γ γ' eq_γ := fun eq₁ => .expand .ap_lam .ap_lam <| cast (by lemma) <| eq (eq_γ.extend eq₁)
  ap eq eq₁     γ γ' eq_γ := eq eq_γ (eq₁ eq_γ)
  ret eq        γ γ' eq_γ := ⟨_, _, eq eq_γ, .refl, .refl⟩
  bind eq eq₁   γ γ' eq_γ := let ⟨_, _, eq, r, r'⟩ := eq eq_γ; .expand (.trans (.bind r) .bind_ret) (.trans (.bind r') .bind_ret) <| cast (by lemma) <| eq₁ (eq_γ.extend eq)

inductive DefEq : ∀ Γ (AX : Typ p), (M M' : Exp Γ AX) → Type :=
  | symm  (eq : DefEq Γ AX M M')                           : DefEq Γ AX M' M
  | trans (eq : DefEq Γ AX M M') (eq' : DefEq Γ AX M' M'') : DefEq Γ AX M M''

  | var   x                                                   : DefEq Γ A              (.var x)       (.var x)
  | trivP                                                     : DefEq Γ .unitP         .trivP         .trivP
  | inl   (eq : DefEq Γ A₁ V V')                              : DefEq Γ (.sum A₁ A₂)   (.inl V)       (.inl V')
  | inr   (eq : DefEq Γ A₂ V V')                              : DefEq Γ (.sum A₁ A₂)   (.inr V)       (.inr V')
  | pairP (eq₁ : DefEq Γ A₁ V₁ V₁') (eq₂ : DefEq Γ A₂ V₂ V₂') : DefEq Γ (.prodP A₁ A₂) (.pairP V₁ V₂) (.pairP V₁' V₂')
  | susp  (eq : DefEq Γ X C C')                               : DefEq Γ (.U X)         (.susp C)      (.susp C')

  | abort (eq : DefEq Γ .void V V')                                                                              : DefEq Γ X (.abort V)      (.abort V')
  | check (eq : DefEq Γ .unitP V V') (eq₁ : DefEq Γ X C C')                                                      : DefEq Γ X (.check V C)    (.check V' C')
  | case  (eq : DefEq Γ (.sum A₁ A₂) V V') (eq₁ : DefEq (Γ.cons A₁) X C₁ C₁') (eq₂ : DefEq (Γ.cons A₂) X C₂ C₂') : DefEq Γ X (.case V C₁ C₂) (.case V' C₁' C₂')
  | split (eq : DefEq Γ (.prodP A₁ A₂) V V') (eq₁ : DefEq (Γ.cons A₁ |>.cons A₂) X C C')                         : DefEq Γ X (.split V C)    (.split V' C')
  | force (eq : DefEq Γ (.U X) V V')                                                                             : DefEq Γ X (.force V)      (.force V')

  | trivN                                                              : DefEq Γ .unitN .trivN .trivN
  | pairN (eq₁ : DefEq Γ X₁ C₁ C₁') (eq₂ : DefEq Γ X₂ C₂ C₂')          : DefEq Γ (.prodN X₁ X₂) (.pairN C₁ C₂) (.pairN C₁' C₂')
  | prl   (eq : DefEq Γ (.prodN X₁ X₂) C C')                           : DefEq Γ X₁ (.prl C) (.prl C')
  | prr   (eq : DefEq Γ (.prodN X₁ X₂) C C')                           : DefEq Γ X₂ (.prr C) (.prr C')
  | lam   (eq : DefEq (.cons Γ A) X C C')                              : DefEq Γ (.arr A X) (.lam C) (.lam C')
  | ap    (eq : DefEq Γ (.arr A X) C C') (eq₁ : DefEq Γ A V V')        : DefEq Γ X (.ap C V) (.ap C' V')
  | ret   (eq : DefEq Γ A V V')                                        : DefEq Γ (.F A) (.ret V) (.ret V')
  | bind  (eq : DefEq Γ (.F A) C C') (eq₁ : DefEq (Γ.cons A) X C₁ C₁') : DefEq Γ X (.bind C C₁) (.bind C' C₁')

  | check_triv C       : DefEq Γ X (.check .trivP C)         C
  | case_inl   V C₁ C₂ : DefEq Γ X (.case (.inl V) C₁ C₂)    (C₁.subst V)
  | case_inr   V C₁ C₂ : DefEq Γ X (.case (.inr V) C₁ C₂)    (C₂.subst V)
  | split_pair V₁ V₂ C : DefEq Γ X (.split (.pairP V₁ V₂) C) (C.subst₂ V₁ V₂)
  | force_susp C       : DefEq Γ X (.force (.susp C))        C

  | prl_pair C₁ C₂ : DefEq Γ X₁ (.prl (.pairN C₁ C₂))     C₁
  | prr_pair C₁ C₂ : DefEq Γ X₂ (.prr (.pairN C₁ C₂))     C₂
  | ap_lam   C V   : DefEq Γ X  (.ap (.lam C) V)          (C.subst V)
  | bind_ret V C   : DefEq Γ X  (.bind (.ret V) C)        (C.subst V)

  | void_η  V C : DefEq Γ X      (.subst C V) (.abort V)
  | unitP_η V C : DefEq Γ X      (.subst C V) (.check V (C.subst .trivP))
  | sum_η   V C : DefEq Γ X      (.subst C V) (.case V (C.subst₁₁ (.inl (.var .zero))) (C.subst₁₁ (.inr (.var .zero))))
  | prodP_η V C : DefEq Γ X      (.subst C V) (.split V (C.subst₂₁ (.pairP (.var (.succ .zero)) (.var .zero))))
  | U_η     V   : DefEq Γ (.U X) V            (.susp (.force V))

  | unitN_η C : DefEq Γ .unitN         C .trivN
  | prodN_η C : DefEq Γ (.prodN X₁ X₂) C (.pairN (.prl C) (.prr C))
  | arr_η   C : DefEq Γ (.arr A X)     C (.lam (.ap C.weaken (.var .zero)))
  | F_η     C : DefEq Γ (.F A)         C (.bind C (.ret (.var .zero)))

  /-
  | abort (V : Exp Γ .void)                                                          : @Exp .neg Γ X
  | check (V : Exp Γ .unitP) (C : Exp Γ X)                                           : @Exp .neg Γ X
  | case  (V : Exp Γ (.sum A₁ A₂)) (C₁ : Exp (Γ.cons A₁) X) (C₂ : Exp (Γ.cons A₂) X) : @Exp .neg Γ X
  | split (V : Exp Γ (.prodP A₁ A₂)) (C : Exp (Γ.cons A₁ |>.cons A₂) X)              : @Exp .neg Γ X
  | force (V : Exp Γ (.U X))                                                         : Exp Γ X
  -/

  | prl_bind C C' : DefEq Γ X (.prl (.bind C C')) (.bind C (.prl C'))
  | prr_bind C C' : DefEq Γ X (.prr (.bind C C')) (.bind C (.prr C'))
  | ap_bind C C' V : DefEq Γ X (.ap (.bind C C') V) (.bind C (.ap C' V.weaken))
  | bind_bind C C' C'' : DefEq Γ X (.bind (.bind C C') C'') (.bind C (.bind C' (Renaming.extend (fun _ x => x.succ.succ) .zero |>.rename C'')))

namespace DefEq

def congruence : Congruence DefEq where
  symm  := symm
  trans := trans

  var   := var
  trivP := trivP
  inl   := inl
  inr   := inr
  pairP := pairP
  susp  := susp

  abort := abort
  check := check
  case  := case
  split := split
  force := force

  trivN := trivN
  pairN := pairN
  prl   := prl
  prr   := prr
  lam   := lam
  ap    := ap
  ret   := ret
  bind  := bind

section

variable (C : Exp Γ (.F A))

def bind_triv : DefEq Γ .unitN (.bind C .trivN) .trivN :=
  unitN_η ..

def bind_pair C₁ C₂ : DefEq Γ (.prodN X₁ X₂) (.bind C (.pairN C₁ C₂)) (.pairN (.bind C C₁) (.bind C C₂)) :=
  trans (prodN_η ..) <| pairN (trans (prl_bind C ..) <| bind (congruence.refl C) (prl_pair C₁ C₂)) (trans (prr_bind C _) <| bind (congruence.refl C) (prr_pair C₁ C₂))

def bind_lam C' : DefEq Γ (.arr A' X) (.bind C (.lam C')) (.lam (.bind C.weaken <| C'.subst₂₂ (.var .zero) (.var (.succ .zero)))) :=
  trans (arr_η ..) <| lam <| trans (ap_bind ..) <| bind (congruence.refl ..) <| trans (ap_lam ..) <| cast (by lemma) <| congruence.refl (C'.subst₂₂ (.var .zero) (.var (.succ .zero)))

end

def bind_case₁ (V : Exp Γ (.sum A₁ A₂)) C₁ C₂ (C : Exp (Γ.cons A) X) : DefEq Γ X (.bind (.case V C₁ C₂) C) (.case V (.bind C₁ sorry) (.bind C₂ sorry)) :=
  sorry

def bind_case₂ (C : Exp Γ (.F A)) (V : Exp Γ (.sum A₁ A₂)) C₁ C₂ : DefEq Γ X (.bind C (.case V.weaken C₁ C₂)) (.case V (.bind C.weaken <| C₁.subst₂₂ (.var .zero) (.var (.succ .zero))) (.bind C.weaken <| C₂.subst₂₂ (.var .zero) (.var (.succ .zero)))) :=
  have := sum_η V (.bind C.weaken (.case (.var (.succ .zero)) (Subst.subst (Subst.extend (Subst.extend (fun _ x => .var x.succ.succ.succ) (.var (.succ .zero))) (.var .zero)) C₁) (Subst.subst (Subst.extend (Subst.extend (fun _ x => .var x.succ.succ.succ) (.var (.succ .zero))) (.var .zero)) C₂)))
  trans (cast (congrArg (DefEq _ _ · _) <| by simp; constructor <;> refine .trans ?_ Subst.subst_var <;> congr <;> funext _ x <;> cases x <;> simp <;> cases ‹_› <;> simp) this) <|
  case (congruence.refl V) (bind sorry <| trans (case_inl ..) sorry) (bind sorry <| trans (case_inr ..) sorry)

end DefEq

def ftlr₂ : (eq : DefEq Γ AX M M') → ExactEq' Γ AX M M'
  | .symm eq      => ExactEq'.congruence.symm (ftlr₂ eq)
  | .trans eq eq' => ExactEq'.congruence.trans (ftlr₂ eq) (ftlr₂ eq')

  | .var x         => ExactEq'.congruence.var x
  | .trivP         => ExactEq'.congruence.trivP
  | .inl eq        => ExactEq'.congruence.inl (ftlr₂ eq)
  | .inr eq        => ExactEq'.congruence.inr (ftlr₂ eq)
  | .pairP eq₁ eq₂ => ExactEq'.congruence.pairP (ftlr₂ eq₁) (ftlr₂ eq₂)
  | .susp eq       => ExactEq'.congruence.susp (ftlr₂ eq)

  | .abort eq        => ExactEq'.congruence.abort (ftlr₂ eq)
  | .check eq eq₁    => ExactEq'.congruence.check (ftlr₂ eq) (ftlr₂ eq₁)
  | .case eq eq₁ eq₂ => ExactEq'.congruence.case (ftlr₂ eq) (ftlr₂ eq₁) (ftlr₂ eq₂)
  | .split eq eq₁    => ExactEq'.congruence.split (ftlr₂ eq) (ftlr₂ eq₁)
  | .force eq        => ExactEq'.congruence.force (ftlr₂ eq)

  | .trivN         => ExactEq'.congruence.trivN
  | .pairN eq₁ eq₂ => ExactEq'.congruence.pairN (ftlr₂ eq₁) (ftlr₂ eq₂)
  | .prl eq        => ExactEq'.congruence.prl (ftlr₂ eq)
  | .prr eq        => ExactEq'.congruence.prr (ftlr₂ eq)
  | .lam eq        => ExactEq'.congruence.lam (ftlr₂ eq)
  | .ap eq eq₁     => ExactEq'.congruence.ap (ftlr₂ eq) (ftlr₂ eq₁)
  | .ret eq        => ExactEq'.congruence.ret (ftlr₂ eq)
  | .bind eq eq₁   => ExactEq'.congruence.bind (ftlr₂ eq) (ftlr₂ eq₁)

  | .check_triv C       => fun eq_γ => .expand .check_triv .refl <| ExactEq'.congruence.refl C eq_γ
  | .case_inl V C₁ C₂   => fun eq_γ => .expand .case_inl .refl <| cast (by lemma) <| ExactEq'.congruence.refl (C₁.subst V) eq_γ
  | .case_inr V C₁ C₂   => fun eq_γ => .expand .case_inr .refl <| cast (by lemma) <| ExactEq'.congruence.refl (C₂.subst V) eq_γ
  | .split_pair V₁ V₂ C => fun eq_γ => .expand .split_pair .refl <| cast (by lemma) <| ExactEq'.congruence.refl (C.subst₂ V₁ V₂) eq_γ
  | .force_susp C       => fun eq_γ => .expand .force_susp .refl <| ExactEq'.congruence.refl C eq_γ

  | .prl_pair C₁ C₂ => fun eq_γ => .expand .prl_pair .refl <| ExactEq'.congruence.refl C₁ eq_γ
  | .prr_pair C₁ C₂ => fun eq_γ => .expand .prr_pair .refl <| ExactEq'.congruence.refl C₂ eq_γ
  | .ap_lam C V     => fun eq_γ => .expand .ap_lam .refl <| cast (by lemma) <| ExactEq'.congruence.refl (C.subst V) eq_γ
  | .bind_ret V C   => fun eq_γ => .expand .bind_ret .refl <| cast (by lemma) <| ExactEq'.congruence.refl (C.subst V) eq_γ

  | .void_η V C  => fun eq_γ => nomatch Subst.subst _ V, Subst.subst _ V, ExactEq'.congruence.refl V eq_γ
  | .unitP_η V C => fun eq_γ => sorry
  | .sum_η V C   => fun eq_γ => sorry
  | .prodP_η V C => fun eq_γ => sorry
  | .U_η V       => fun eq_γ => show ExactEq _ _ (.susp (.force ..)) from
                                match Subst.subst _ V, Subst.subst _ V, ExactEq'.congruence.refl V eq_γ with
                                | .susp _, .susp _, eq => .expand .refl .force_susp eq

  | .unitN_η C => fun eq_γ => let () := ExactEq'.congruence.refl C eq_γ; ()
  | .prodN_η C => fun eq_γ => let (eq₁, eq₂) := ExactEq'.congruence.refl C eq_γ; (.expand .refl .prl_pair eq₁, .expand .refl .prr_pair eq₂)
  | .arr_η C   => fun eq_γ => fun eq₁ => .expand .refl .ap_lam <| cast (by lemma) <| ExactEq'.congruence.refl C eq_γ eq₁
  | .F_η C     => fun eq_γ => let ⟨_, _, eq, r, r'⟩ := ExactEq'.congruence.refl C eq_γ; ⟨_, _, eq, r, .trans (.bind r') .bind_ret⟩

-- TODO : EEC with full eta for F
