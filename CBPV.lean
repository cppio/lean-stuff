mutual

inductive TypP
  | void
  | unit
  | sum  (A₁ A₂ : TypP)
  | prod (A₁ A₂ : TypP)
  | U    (X : TypN)

inductive TypN
  | unit
  | prod (X₁ X₂ : TypN)
  | arr  (A : TypP) (X : TypN)
  | F    (A : TypP)

end

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : TypP)

inductive Var (A : TypP) : (Γ : Ctx) → Type
  | zero               : Var A (.cons Γ A)
  | succ (x : Var A Γ) : Var A (.cons Γ A')

mutual

inductive ExpP : (Γ : Ctx) → (A : TypP) → Type
  | var  (x : Var A Γ)                     : ExpP Γ A
  | triv                                   : ExpP Γ .unit
  | inl  (V : ExpP Γ A₁)                   : ExpP Γ (.sum A₁ A₂)
  | inr  (V : ExpP Γ A₂)                   : ExpP Γ (.sum A₁ A₂)
  | pair (V₁ : ExpP Γ A₁) (V₂ : ExpP Γ A₂) : ExpP Γ (.prod A₁ A₂)
  | susp (C : ExpN Γ X)                    : ExpP Γ (.U X)

inductive ExpN : (Γ : Ctx) → (X : TypN) → Type
  | abort (V : ExpP Γ .void)                                                            : ExpN Γ X
  | check (V : ExpP Γ .unit) (C : ExpN Γ X)                                             : ExpN Γ X
  | case  (V : ExpP Γ (.sum A₁ A₂)) (C₁ : ExpN (Γ.cons A₁) X) (C₂ : ExpN (Γ.cons A₂) X) : ExpN Γ X
  | split (V : ExpP Γ (.prod A₁ A₂)) (C : ExpN (Γ.cons A₁ |>.cons A₂) X)                : ExpN Γ X
  | force (V : ExpP Γ (.U X))                                                           : ExpN Γ X

  | triv                                               : ExpN Γ .unit
  | pair  (C₁ : ExpN Γ X₁) (C₂ : ExpN Γ X₂)            : ExpN Γ (.prod X₁ X₂)
  | prl   (C : ExpN Γ (.prod X₁ X₂))                   : ExpN Γ X₁
  | prr   (C : ExpN Γ (.prod X₁ X₂))                   : ExpN Γ X₂
  | lam   (C : ExpN (Γ.cons A) X)                      : ExpN Γ (.arr A X)
  | ap    (C : ExpN Γ (.arr A X)) (V : ExpP Γ A)       : ExpN Γ X
  | ret   (V : ExpP Γ A)                               : ExpN Γ (.F A)
  | bind  (C : ExpN Γ (.F A)) (C₁ : ExpN (Γ.cons A) X) : ExpN Γ X

end

def Renaming (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Var A Γ

namespace Renaming

@[simp]
def weaken (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .zero
  | _, .succ x => .succ (γ x)

mutual

@[simp]
def applyP (γ : Renaming Γ Γ') : (V : ExpP Γ' A) → ExpP Γ A
  | .var x      => .var (γ x)
  | .triv       => .triv
  | .inl V      => .inl (γ.applyP V)
  | .inr V      => .inr (γ.applyP V)
  | .pair V₁ V₂ => .pair (γ.applyP V₁) (γ.applyP V₂)
  | .susp C     => .susp (γ.applyN C)

@[simp]
def applyN (γ : Renaming Γ Γ') : (C : ExpN Γ' X) → ExpN Γ X
  | .abort V      => .abort (γ.applyP V)
  | .check V C    => .check (γ.applyP V) (γ.applyN C)
  | .case V C₁ C₂ => .case (γ.applyP V) (γ.weaken.applyN C₁) (γ.weaken.applyN C₂)
  | .split V C    => .split (γ.applyP V) (γ.weaken.weaken.applyN C)
  | .force V      => .force (γ.applyP V)

  | .triv       => .triv
  | .pair C₁ C₂ => .pair (γ.applyN C₁) (γ.applyN C₂)
  | .prl C      => .prl (γ.applyN C)
  | .prr C      => .prr (γ.applyN C)
  | .lam C      => .lam (γ.weaken.applyN C)
  | .ap C V     => .ap (γ.applyN C) (γ.applyP V)
  | .ret V      => .ret (γ.applyP V)
  | .bind C C₁  => .bind (γ.applyN C) (γ.weaken.applyN C₁)

end

@[simp]
def cons (γ : Renaming Γ Γ') (x : Var A Γ) : Renaming Γ (Γ'.cons A)
  | _, .zero   => x
  | _, .succ x => γ x

end Renaming

@[simp]
def ExpP.weaken : (V : ExpP Γ A) → ExpP (Γ.cons A') A :=
  Renaming.applyP fun _ => .succ

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → ExpP Γ A

namespace Subst

@[simp]
def weaken (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .var .zero
  | _, .succ x => .weaken (γ x)

mutual

@[simp]
def applyP (γ : Subst Γ Γ') : (V : ExpP Γ' A) → ExpP Γ A
  | .var x      => γ x
  | .triv       => .triv
  | .inl V      => .inl (γ.applyP V)
  | .inr V      => .inr (γ.applyP V)
  | .pair V₁ V₂ => .pair (γ.applyP V₁) (γ.applyP V₂)
  | .susp C     => .susp (γ.applyN C)

@[simp]
def applyN (γ : Subst Γ Γ') : (C : ExpN Γ' X) → ExpN Γ X
  | .abort V      => .abort (γ.applyP V)
  | .check V C    => .check (γ.applyP V) (γ.applyN C)
  | .case V C₁ C₂ => .case (γ.applyP V) (γ.weaken.applyN C₁) (γ.weaken.applyN C₂)
  | .split V C    => .split (γ.applyP V) (γ.weaken.weaken.applyN C)
  | .force V      => .force (γ.applyP V)

  | .triv       => .triv
  | .pair C₁ C₂ => .pair (γ.applyN C₁) (γ.applyN C₂)
  | .prl C      => .prl (γ.applyN C)
  | .prr C      => .prr (γ.applyN C)
  | .lam C      => .lam (γ.weaken.applyN C)
  | .ap C V     => .ap (γ.applyN C) (γ.applyP V)
  | .ret V      => .ret (γ.applyP V)
  | .bind C C₁  => .bind (γ.applyN C) (γ.weaken.applyN C₁)

end

@[simp]
def cons (γ : Subst Γ Γ') (V : ExpP Γ A) : Subst Γ (Γ'.cons A)
  | _, .zero   => V
  | _, .succ x => γ x

end Subst

@[simp]
def ExpN.subst (C : ExpN (Γ.cons A) X) (V : ExpP Γ A) : ExpN Γ X :=
  Subst.cons (fun _ => .var) V |>.applyN C

@[simp]
def ExpN.subst₂ (C : ExpN (Γ.cons A₁ |>.cons A₂) X) (V₁ : ExpP Γ A₁) (V₂ : ExpP Γ A₂) : ExpN Γ X :=
  Subst.cons (fun _ => .var) V₁ |>.cons V₂ |>.applyN C

section

local macro "lemma" M:ident γ:ident γTy:ident γ':ident γ'Ty:ident fnP:ident fnN:ident arg:term : tactic =>
  `(tactic| (
    apply $(M).rec
      (motive_1 := fun Γ'' A V => ∀ {Γ Γ'}, ($γ : $γTy Γ Γ') → ($γ' : $γ'Ty Γ' Γ'') → $(γ).applyP ($(γ').applyP V) = $fnP $arg V)
      (motive_2 := fun Γ'' X C => ∀ {Γ Γ'}, ($γ : $γTy Γ Γ') → ($γ' : $γ'Ty Γ' Γ'') → $(γ).applyN ($(γ').applyN C) = $fnN $arg C)
      <;> intros
      <;> intro _ _ _ _
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
theorem Renaming.rename_rename (γ : Renaming Γ Γ') (γ' : Renaming Γ' Γ'') : γ.applyP (γ'.applyP V) = applyP (fun A x => γ (γ' x)) V :=
  by lemma V γ Renaming γ' Renaming applyP applyN fun A x => γ (γ' x)

@[simp]
theorem Subst.subst_rename (γ : Subst Γ Γ') (γ' : Renaming Γ' Γ'') : γ.applyP (γ'.applyP V) = applyP (fun A x => γ (γ' x)) V :=
  by lemma V γ Subst γ' Renaming applyP applyN fun A x => γ (γ' x)

@[simp]
theorem Subst.rename_subst (γ : Renaming Γ Γ') (γ' : Subst Γ' Γ'') : γ.applyP (γ'.applyP V) = applyP (fun A x => γ.applyP (γ' x)) V :=
  by lemma V γ Renaming γ' Subst applyP applyN fun A x => γ.applyP (γ' x)

@[simp]
theorem Subst.subst_subst (γ : Subst Γ Γ') (γ' : Subst Γ' Γ'') : γ.applyN (γ'.applyN C) = applyN (fun A x => γ.applyP (γ' x)) C :=
  by lemma C γ Subst γ' Subst applyP applyN fun A x => γ.applyP (γ' x)

end

@[simp]
theorem Subst.weaken_var : weaken (Γ := Γ) (A := A) (fun _ => .var) = fun _ => .var := by
  funext _ x
  cases x
    <;> simp

@[simp]
theorem Subst.applyP_var : applyP (fun _ => .var) V = V := by
  apply V.rec
    (motive_1 := fun Γ A V => applyP (fun _ => .var) V = V)
    (motive_2 := fun Γ X C => applyN (fun _ => .var) C = C)
    <;> intros
    <;> simp [*]

macro "subst" : tactic => `(tactic| (simp; congr; funext _ x; cases x <;> simp; first | done | cases ‹_› <;> simp))

inductive Steps : (C C' : ExpN .nil X) → Type
  | prl  (s : Steps C C') : Steps (.prl C)     (.prl C')
  | prr  (s : Steps C C') : Steps (.prr C)     (.prr C')
  | ap   (s : Steps C C') : Steps (.ap C V)    (.ap C' V)
  | bind (s : Steps C C') : Steps (.bind C C₁) (.bind C' C₁)

  | check_triv : Steps (.check .triv C)         C
  | case_inl   : Steps (.case (.inl V) C₁ C₂)   (C₁.subst V)
  | case_inr   : Steps (.case (.inr V) C₁ C₂)   (C₂.subst V)
  | split_pair : Steps (.split (.pair V₁ V₂) C) (C.subst₂ V₁ V₂)
  | force_susp : Steps (.force (.susp C))       C

  | prl_pair   : Steps (.prl (.pair C₁ C₂))     C₁
  | prr_pair   : Steps (.prr (.pair C₁ C₂))     C₂
  | ap_lam     : Steps (.ap (.lam C) V)         (C.subst V)
  | bind_ret   : Steps (.bind (.ret V) C)       (C.subst V)

inductive Reduces : (C C' : ExpN .nil A) → Type
  | refl                                       : Reduces C C
  | step (s : Steps C C') (r : Reduces C' C'') : Reduces C C''

namespace Reduces

def trans : (r : Reduces C C') → (r' : Reduces C' C'') → Reduces C C''
  | .refl,     r' => r'
  | .step s r, r' => .step s (r.trans r')

def comp {F : (C : ExpN .nil X) → ExpN .nil Y} (f : ∀ {C C'}, (s : Steps C C') → Steps (F C) (F C')) : (r : Reduces C C') → Reduces (F C) (F C')
  | .refl     => .refl
  | .step s r => .step (f s) (r.comp f)

end Reduces

mutual

def HTP : (A : TypP) → (V : ExpP .nil A) → Type
  | .void       => nofun
  | .unit       => fun | .triv => Unit
  | .sum  A₁ A₂ => fun | .inl V => HTP A₁ V
                       | .inr V => HTP A₂ V
  | .prod A₁ A₂ => fun | .pair V₁ V₂ => HTP A₁ V₁ × HTP A₂ V₂
  | .U X        => fun | .susp C => HTN X C

def HTN : (X : TypN) → (C : ExpN .nil X) → Type
  | .unit       => fun _ => Unit
  | .prod X₁ X₂ => fun C => HTN X₁ (.prl C) × HTN X₂ (.prr C)
  | .arr A X    => fun C => ∀ {V}, HTP A V → HTN X (.ap C V)
  | .F A        => fun C => Σ V, HTP A V × Reduces C (.ret V)

end

def HTN.expand : ∀ {X C₁ C₂}, (r₁ : Reduces C₁ C₂) → (ht₂ : HTN X C₂) → HTN X C₁
  | .unit,       _, _, _,  ()          => ()
  | .prod X₁ X₂, _, _, r₁, (ht₁, ht₂)  => (expand (.comp .prl r₁) ht₁, expand (.comp .prr r₁) ht₂)
  | .arr A X,    _, _, r₁, ht          => fun ht₁ => expand (.comp .ap r₁) (ht ht₁)
  | .F A,        _, _, r₁, ⟨_, ht, r₂⟩ => ⟨_, ht, r₁.trans r₂⟩

def HTSubst (γ : Subst .nil Γ) : Type :=
  ∀ {{A}} x, HTP A (γ x)

def HTSubst.cons (ht_γ : HTSubst γ) (ht : HTP A M) : HTSubst (γ.cons M)
  | _, .zero   => ht
  | _, .succ x => ht_γ x

def HTP' Γ A (V : ExpP Γ A) : Type :=
  ∀ {γ}, (ht_γ : HTSubst γ) → HTP A (γ.applyP V)

def HTN' Γ X (C : ExpN Γ X) : Type :=
  ∀ {γ}, (ht_γ : HTSubst γ) → HTN X (γ.applyN C)

mutual

def ftlrP : (V : ExpP Γ A) → HTP' Γ A V
  | .var x      => fun ht_γ => ht_γ x
  | .triv       => fun ht_γ => ()
  | .inl V      => fun ht_γ => ftlrP V ht_γ
  | .inr V      => fun ht_γ => ftlrP V ht_γ
  | .pair V₁ V₂ => fun ht_γ => (ftlrP V₁ ht_γ, ftlrP V₂ ht_γ)
  | .susp C     => fun ht_γ => ftlrN C ht_γ

def ftlrN : (C : ExpN Γ X) → HTN' Γ X C
  | .abort V      => fun ht_γ => nomatch Subst.applyP _ V, ftlrP V ht_γ
  | .check V C    => fun ht_γ => show HTN _ (.check ..) from
                                 match Subst.applyP _ V, ftlrP V ht_γ with
                                 | .triv, ht => .expand (.step .check_triv .refl) (ftlrN C ht_γ)
  | .case V C₁ C₂ => fun ht_γ => show HTN _ (.case ..) from
                                 match Subst.applyP _ V, ftlrP V ht_γ with
                                 | .inl V, ht => .expand (.step .case_inl .refl) <| cast (by subst) <| ftlrN C₁ (ht_γ.cons ht)
                                 | .inr V, ht => .expand (.step .case_inr .refl) <| cast (by subst) <| ftlrN C₂ (ht_γ.cons ht)
  | .split V C    => fun ht_γ => show HTN _ (.split ..) from
                                 match Subst.applyP _ V, ftlrP V ht_γ with
                                 | .pair V₁ V₂, (ht₁, ht₂) => .expand (.step .split_pair .refl) <| cast (by subst) <| ftlrN C (ht_γ.cons ht₁ |>.cons ht₂)
  | .force V      => fun ht_γ => show HTN _ (.force ..) from
                                 match Subst.applyP _ V, ftlrP V ht_γ with
                                 | .susp C, ht => .expand (.step .force_susp .refl) ht

  | .triv       => fun ht_γ => ()
  | .pair C₁ C₂ => fun ht_γ => (.expand (.step .prl_pair .refl) <| ftlrN C₁ ht_γ, .expand (.step .prr_pair .refl) <| ftlrN C₂ ht_γ)
  | .prl C      => fun ht_γ => let (ht₁, ht₂) := ftlrN C ht_γ; ht₁
  | .prr C      => fun ht_γ => let (ht₁, ht₂) := ftlrN C ht_γ; ht₂
  | .lam C      => fun ht_γ => fun ht => .expand (.step .ap_lam .refl) <| cast (by subst) <| ftlrN C (ht_γ.cons ht)
  | .ap C V     => fun ht_γ => ftlrN C ht_γ (ftlrP V ht_γ)
  | .ret V      => fun ht_γ => ⟨_, ftlrP V ht_γ, .refl⟩
  | .bind C C₁  => fun ht_γ => let ⟨_, ht, r⟩ := ftlrN C ht_γ; .expand (.trans (.comp .bind r) (.step .bind_ret .refl)) <| cast (by subst) <| ftlrN C₁ (ht_γ.cons ht)

end
