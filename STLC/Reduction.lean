import STLC.Basic

import Mathlib.Util.CompileInductive

namespace STLC.Reduction

inductive Steps : (M M' : Exp Γ A) → Type
  | abort (s : Steps M M')   : Steps (.abort M)      (.abort M')
  | inl   (s : Steps M M')   : Steps (.inl M)        (.inl M')
  | inr   (s : Steps M M')   : Steps (.inr M)        (.inr M')
  | case  (s : Steps M M')   : Steps (.case M M₁ M₂) (.case M' M₁ M₂)
  | case₁ (s : Steps M₁ M₁') : Steps (.case M M₁ M₂) (.case M M₁' M₂)
  | case₂ (s : Steps M₂ M₂') : Steps (.case M M₁ M₂) (.case M M₁ M₂')
  | pair₁ (s : Steps M₁ M₁') : Steps (.pair M₁ M₂)   (.pair M₁' M₂)
  | pair₂ (s : Steps M₂ M₂') : Steps (.pair M₁ M₂)   (.pair M₁ M₂')
  | prl   (s : Steps M M')   : Steps (.prl M)        (.prl M')
  | prr   (s : Steps M M')   : Steps (.prr M)        (.prr M')
  | lam   (s : Steps M M')   : Steps (.lam M)        (.lam M')
  | ap    (s : Steps M M')   : Steps (.ap M M₁)      (.ap M' M₁)
  | ap₁   (s : Steps M₁ M₁') : Steps (.ap M M₁)      (.ap M M₁')

  | case_inl : Steps (.case (.inl M) M₁ M₂) (M₁.subst M)
  | case_inr : Steps (.case (.inr M) M₁ M₂) (M₂.subst M)
  | prl_pair : Steps (.prl (.pair M₁ M₂))   M₁
  | prr_pair : Steps (.prr (.pair M₁ M₂))   M₂
  | ap_lam   : Steps (.ap (.lam M) M₁)      (M.subst M₁)

def Steps.rename (γ : Renaming Γ Γ') : (s : Steps M M') → Steps (γ.apply M) (γ.apply M')
  | abort s => abort (s.rename γ)
  | inl   s => inl   (s.rename γ)
  | inr   s => inr   (s.rename γ)
  | case  s => case  (s.rename γ)
  | case₁ s => case₁ (s.rename γ.weaken)
  | case₂ s => case₂ (s.rename γ.weaken)
  | pair₁ s => pair₁ (s.rename γ)
  | pair₂ s => pair₂ (s.rename γ)
  | prl   s => prl   (s.rename γ)
  | prr   s => prr   (s.rename γ)
  | lam   s => lam   (s.rename γ.weaken)
  | ap    s => ap    (s.rename γ)
  | ap₁   s => ap₁   (s.rename γ)

  | case_inl => cast (congrArg (Steps _) (by lemma)) case_inl
  | case_inr => cast (congrArg (Steps _) (by lemma)) case_inr
  | prl_pair => prl_pair
  | prr_pair => prr_pair
  | ap_lam   => cast (congrArg (Steps _) (by lemma)) ap_lam

mutual

inductive Norm : ∀ Γ A, (M : Exp Γ A) → Type
  | neut (n : Neut Γ A M)                        : Norm Γ A             M
  | triv                                         : Norm Γ .unit         .triv
  | inl  (n : Norm Γ A₁ M)                       : Norm Γ (.sum A₁ A₂)  (.inl M)
  | inr  (n : Norm Γ A₂ M)                       : Norm Γ (.sum A₁ A₂)  (.inr M)
  | pair (n₁ : Norm Γ A₁ M₁) (n₂ : Norm Γ A₂ M₂) : Norm Γ (.prod A₁ A₂) (.pair M₁ M₂)
  | lam  (n : Norm (.cons Γ A₁) A₂ M)            : Norm Γ (.arr A₁ A₂)  (.lam M)

inductive Neut : ∀ Γ A, (M : Exp Γ A) → Type
  | var   (x : Var A Γ)                                                                         : Neut Γ A  (.var x)
  | abort (n : Neut Γ .void M)                                                                  : Neut Γ A  (.abort M)
  | case  (n : Neut Γ (.sum A₁ A₂) M) (n₁ : Norm (Γ.cons A₁) A M₁) (n₂ : Norm (Γ.cons A₂) A M₂) : Neut Γ A  (.case M M₁ M₂)
  | prl   (n : Neut Γ (.prod A₁ A₂) M)                                                          : Neut Γ A₁ (.prl M)
  | prr   (n : Neut Γ (.prod A₁ A₂) M)                                                          : Neut Γ A₂ (.prr M)
  | ap    (n : Neut Γ (.arr A₁ A₂) M) (n₁ : Norm Γ A₁ M₁)                                       : Neut Γ A₂ (.ap M M₁)

end

mutual

def Norm.rename (γ : Renaming Γ Γ') : (n : Norm Γ' A M) → Norm Γ A (γ.apply M)
  | .neut n     => .neut (n.rename γ)
  | .triv       => .triv
  | .inl n      => .inl (n.rename γ)
  | .inr n      => .inr (n.rename γ)
  | .pair n₁ n₂ => .pair (n₁.rename γ) (n₂.rename γ)
  | .lam n      => .lam (n.rename γ.weaken)

def Neut.rename (γ : Renaming Γ Γ') : (n : Neut Γ' A M) → Neut Γ A (γ.apply M)
  | .var x        => .var (γ x)
  | .abort n      => .abort (n.rename γ)
  | .case n n₁ n₂ => .case (n.rename γ) (n₁.rename γ.weaken) (n₂.rename γ.weaken)
  | .prl n        => .prl (n.rename γ)
  | .prr n        => .prr (n.rename γ)
  | .ap n n₁      => .ap (n.rename γ) (n₁.rename γ)

end

def Normal (M : Exp Γ A) : Prop :=
  ∀ {M'}, Steps M M' → False

theorem Norm.normal : (n : Norm Γ A M) → Normal M := by
  apply @Norm.rec (fun _ _ M _ => Normal M) (fun _ _ M _ => Normal M)
    <;> intros
    <;> (try assumption)
    <;> intro _ s
    <;> cases s
    <;> (try contradiction)
    <;> rename_i s
    <;> exact ‹Normal _› s

private inductive Val : (M : Exp Γ A) → Type
  | triv : Val .triv
  | inl  : Val (.inl M)
  | inr  : Val (.inr M)
  | pair : Val (.pair M₁ M₂)
  | lam  : Val (.lam M)

private def of_normal : ∀ {M}, (n : Normal M) → Norm Γ A M × (((v : Val M) → False) → Neut Γ A M)
  | .var x,      n => let n := .var x; (.neut n, fun _ => n)
  | .abort _,    n => let n := .abort ((of_normal fun s => n (.abort s)).snd nofun); (.neut n, fun _ => n)
  | .triv,       n => (.triv, fun nv => nomatch nv .triv)
  | .inl _,      n => (.inl (of_normal fun s => n (.inl s)).fst, fun nv => nomatch nv .inl)
  | .inr _,      n => (.inr (of_normal fun s => n (.inr s)).fst, fun nv => nomatch nv .inr)
  | .case _ _ _, n => let n := .case ((of_normal fun s => n (.case s)).snd fun | .inl => n .case_inl | .inr => n .case_inr) (of_normal fun s => n (.case₁ s)).fst (of_normal fun s => n (.case₂ s)).fst; (.neut n, fun _ => n)
  | .pair _ _,   n => (.pair (of_normal fun s => n (.pair₁ s)).fst (of_normal fun s => n (.pair₂ s)).fst, fun nv => nomatch nv .pair)
  | .prl _,      n => let n := .prl ((of_normal fun s => n (.prl s)).snd fun | .pair => n .prl_pair); (.neut n, fun _ => n)
  | .prr _,      n => let n := .prr ((of_normal fun s => n (.prr s)).snd fun | .pair => n .prr_pair); (.neut n, fun _ => n)
  | .lam _,      n => (.lam (of_normal fun s => n (.lam s)).fst, fun nv => nomatch nv .lam)
  | .ap _ _,     n => let n := .ap ((of_normal fun s => n (.ap s)).snd fun | .lam => n .ap_lam) (of_normal fun s => n (.ap₁ s)).fst; (.neut n, fun _ => n)

def Norm.of_normal {M} (n : Normal M) : Norm Γ A M :=
  Reduction.of_normal n |>.fst

inductive Reduces : (M M' : Exp Γ A) → Type
  | refl                                       : Reduces M M
  | step (s : Steps M M') (r : Reduces M' M'') : Reduces M M''

namespace Reduces

def trans : (r : Reduces M M') → (r' : Reduces M' M'') → Reduces M M''
  | refl,     r' => r'
  | step s r, r' => step s (r.trans r')

def lift {F : (M : Exp Γ A) → Exp Γ' A'} (f : ∀ {M M'}, (s : Steps M M') → Steps (F M) (F M')) : (r : Reduces M M') → Reduces (F M) (F M')
  | refl     => refl
  | step s r => step (f s) (r.lift f)

def abort : (r : Reduces M M')   → Reduces (A := A)         (.abort M)      (.abort M')      := lift .abort
def inl   : (r : Reduces M M')   → Reduces (A := .sum _ A₂) (.inl M)        (.inl M')        := lift .inl
def inr   : (r : Reduces M M')   → Reduces (A := .sum A₁ _) (.inr M)        (.inr M')        := lift .inr
def case  : (r : Reduces M M')   → Reduces                  (.case M M₁ M₂) (.case M' M₁ M₂) := lift .case
def case₁ : (r : Reduces M₁ M₁') → Reduces                  (.case M M₁ M₂) (.case M M₁' M₂) := lift .case₁
def case₂ : (r : Reduces M₂ M₂') → Reduces                  (.case M M₁ M₂) (.case M M₁ M₂') := lift .case₂
def pair₁ : (r : Reduces M₁ M₁') → Reduces                  (.pair M₁ M₂)   (.pair M₁' M₂)   := lift .pair₁
def pair₂ : (r : Reduces M₂ M₂') → Reduces                  (.pair M₁ M₂)   (.pair M₁ M₂')   := lift .pair₂
def prl   : (r : Reduces M M')   → Reduces                  (.prl M)        (.prl M')        := lift .prl
def prr   : (r : Reduces M M')   → Reduces                  (.prr M)        (.prr M')        := lift .prr
def lam   : (r : Reduces M M')   → Reduces                  (.lam M)        (.lam M')        := lift .lam
def ap    : (r : Reduces M M')   → Reduces                  (.ap M M₁)      (.ap M' M₁)      := lift .ap
def ap₁   : (r : Reduces M₁ M₁') → Reduces                  (.ap M M₁)      (.ap M M₁')      := lift .ap₁

def case_inl : Reduces (.case (.inl M) M₁ M₂) (M₁.subst M) := step .case_inl refl
def case_inr : Reduces (.case (.inr M) M₁ M₂) (M₂.subst M) := step .case_inr refl
def prl_pair : Reduces (.prl (.pair M₁ M₂))   M₁           := step .prl_pair refl
def prr_pair : Reduces (.prr (.pair M₁ M₂))   M₂           := step .prr_pair refl
def ap_lam   : Reduces (.ap (.lam M) M₁)      (M.subst M₁) := step .ap_lam   refl

def rename (γ : Renaming Γ Γ') : (r : Reduces M M') → Reduces (γ.apply M) (γ.apply M') :=
  lift (.rename γ)

end Reduces

namespace WeakNormalization

def WNorm Γ A (M : Exp Γ A) : Type :=
  Σ M', Norm Γ A M' × Reduces M M'

def WNorm.expand {M₁ M₂} (r₁ : Reduces M₁ M₂) : (n₂ : WNorm Γ A M₂) → WNorm Γ A M₁
  | ⟨_, n, r₂⟩ => ⟨_, n, r₁.trans r₂⟩

def WNorm.rename (γ : Renaming Γ Γ') : (n : WNorm Γ' A M) → WNorm Γ A (γ.apply M)
  | ⟨_, n, r⟩ => ⟨_, n.rename γ, r.rename γ⟩

inductive WNeut : ∀ Γ A, (M : Exp Γ A) → Type
  | var   (x : Var A Γ)                                                                            : WNeut Γ A  (.var x)
  | abort (n : WNeut Γ .void M)                                                                    : WNeut Γ A  (.abort M)
  | case  (n : WNeut Γ (.sum A₁ A₂) M) (n₁ : WNorm (Γ.cons A₁) A M₁) (n₂ : WNorm (Γ.cons A₂) A M₂) : WNeut Γ A  (.case M M₁ M₂)
  | prl   (n : WNeut Γ (.prod A₁ A₂) M)                                                            : WNeut Γ A₁ (.prl M)
  | prr   (n : WNeut Γ (.prod A₁ A₂) M)                                                            : WNeut Γ A₂ (.prr M)
  | ap    (n : WNeut Γ (.arr A₁ A₂) M) (n₁ : WNorm Γ A₁ M₁)                                        : WNeut Γ A₂ (.ap M M₁)

def WNeut.neut : (n : WNeut Γ A M) → Σ M', Neut Γ A M' × Reduces M M'
  | var x                          => ⟨_, .var x, .refl⟩
  | abort n                        => let ⟨_, n, r⟩ := n.neut; ⟨_, .abort n, .abort r⟩
  | case n ⟨_, n₁, r₁⟩ ⟨_, n₂, r₂⟩ => let ⟨_, n, r⟩ := n.neut; ⟨_, .case n n₁ n₂, .trans (.case r) (.trans (.case₁ r₁) (.case₂ r₂))⟩
  | prl n                          => let ⟨_, n, r⟩ := n.neut; ⟨_, .prl n, .prl r⟩
  | prr n                          => let ⟨_, n, r⟩ := n.neut; ⟨_, .prr n, .prr r⟩
  | ap n ⟨_, n₁, r₁⟩               => let ⟨_, n, r⟩ := n.neut; ⟨_, .ap n n₁, .trans (.ap r) (.ap₁ r₁)⟩

def WNeut.wnorm (n : WNeut Γ A M) : WNorm Γ A M :=
  let ⟨_, n, r⟩ := n.neut
  ⟨_, .neut n, r⟩

def WNeut.rename (γ : Renaming Γ Γ') : (n : WNeut Γ' A M) → WNeut Γ A (γ.apply M)
  | var x        => var (γ x)
  | abort n      => abort (n.rename γ)
  | case n n₁ n₂ => case (n.rename γ) (n₁.rename γ.weaken) (n₂.rename γ.weaken)
  | prl n        => prl (n.rename γ)
  | prr n        => prr (n.rename γ)
  | ap n n₁      => ap (n.rename γ) (n₁.rename γ)

def HN₀ (M : Exp Γ A) : Type :=
  Σ M', WNeut Γ _ M' × Reduces M M'

def HN₁ : ∀ A, (M : Exp Γ A) → Type
  | .void,       _ => Empty
  | .unit,       M => Reduces M .triv
  | .sum  A₁ A₂, M => (Σ M₁, (HN₀ M₁ ⊕ HN₁ A₁ M₁) × Reduces M (.inl M₁)) ⊕ (Σ M₂, (HN₀ M₂ ⊕ HN₁ A₂ M₂) × Reduces M (.inr M₂))
  | .prod A₁ A₂, M => Σ M₁, (HN₀ M₁ ⊕ HN₁ A₁ M₁) × Σ M₂, (HN₀ M₂ ⊕ HN₁ A₂ M₂) × Reduces M (.pair M₁ M₂)
  | .arr  A₁ A₂, M => Σ M₂, (∀ {Γ'} (γ : Renaming Γ' Γ) {M₁ : Exp Γ' A₁}, (ht₁ : HN₀ M₁ ⊕ HN₁ A₁ M₁) → let M₂ := (Subst.cons (fun _ x => .var (γ x)) M₁).apply M₂; HN₀ M₂ ⊕ HN₁ A₂ M₂) × Reduces M (.lam M₂)

def HN (M : Exp Γ A) : Type :=
  HN₀ M ⊕ HN₁ A M

def HN.var (x : Var A Γ) : HN (.var x) :=
  .inl ⟨_, .var x, .refl⟩

def HN.expand : ∀ {A} {M₁ M₂ : Exp Γ A}, (r₁ : Reduces M₁ M₂) → (hn₂ : HN M₂) → HN M₁
  | _, _, _, r₁, .inl ⟨_, n, r₂⟩ => .inl ⟨_, n, r₁.trans r₂⟩

  | .unit,     _, _, r₁, .inr r₂                   => .inr (r₁.trans r₂)
  | .sum  _ _, _, _, r₁, .inr (.inl ⟨_, hn₁, r₂⟩)  => .inr (.inl ⟨_, hn₁, r₁.trans r₂⟩)
  | .sum  _ _, _, _, r₁, .inr (.inr ⟨_, hn₂, r₂⟩)  => .inr (.inr ⟨_, hn₂, r₁.trans r₂⟩)
  | .prod _ _, _, _, r₁, .inr ⟨_, hn₁, _, hn₂, r₂⟩ => .inr ⟨_, hn₁, _, hn₂, r₁.trans r₂⟩
  | .arr  _ _, _, _, r₁, .inr ⟨_, hn, r₂⟩          => .inr ⟨_, hn, r₁.trans r₂⟩

def HN.rename (γ : Renaming Γ Γ') : ∀ {A} {M : Exp Γ' A}, (hn : HN M) → HN (γ.apply M)
  | _, _, .inl ⟨_, n, r⟩ => .inl ⟨_, n.rename γ, r.rename γ⟩

  | .unit,     _, .inr r                   => .inr (r.rename γ)
  | .sum  _ _, _, .inr (.inl ⟨_, hn₁, r⟩)  => .inr (.inl ⟨_, rename γ hn₁, r.rename γ⟩)
  | .sum  _ _, _, .inr (.inr ⟨_, hn₂, r⟩)  => .inr (.inr ⟨_, rename γ hn₂, r.rename γ⟩)
  | .prod _ _, _, .inr ⟨_, hn₁, _, hn₂, r⟩ => .inr ⟨_, rename γ hn₁, _, rename γ hn₂, r.rename γ⟩
  | .arr  _ _, _, .inr ⟨_, hn, r⟩          => .inr ⟨_, fun γ' _ hn₁ => have := hn (fun _ x => γ' (γ x)) hn₁; cast (by lemma) this, r.rename γ⟩

def HN.wnorm : ∀ {A M}, (n : HN M) → WNorm Γ A M
  | _, _, .inl ⟨_, n, r⟩ => n.wnorm.expand r

  | .unit,     _, .inr r                   => ⟨_, .triv, r⟩
  | .sum  _ _, _, .inr (.inl ⟨_, hn₁, r⟩)  => let ⟨_, n, r'⟩ := wnorm hn₁; .expand r ⟨_, .inl n, .inl r'⟩
  | .sum  _ _, _, .inr (.inr ⟨_, hn₂, r⟩)  => let ⟨_, n, r'⟩ := wnorm hn₂; .expand r ⟨_, .inr n, .inr r'⟩
  | .prod _ _, _, .inr ⟨_, hn₁, _, hn₂, r⟩ => let ⟨_, n₁, r₁⟩ := wnorm hn₁; let ⟨_, n₂, r₂⟩ := wnorm hn₂; .expand r ⟨_, .pair n₁ n₂, .trans (.pair₁ r₁) (.pair₂ r₂)⟩
  | .arr  _ _, _, .inr ⟨_, hn, r⟩          => let ⟨_, n, r'⟩ := wnorm (hn (fun _ => .succ) (.inl ⟨_, .var .zero, .refl⟩)); .expand r ⟨_, .lam n, .lam (cast (by lemma) r')⟩

def HNSubst (γ : Subst Γ' Γ) : Type :=
  ∀ {A} (x : Var A Γ), HN (γ x)

def HNSubst.cons (hn_γ : HNSubst γ) (hn : HN M) : HNSubst (γ.cons M)
  | _, .zero   => hn
  | _, .succ x => hn_γ x

def HNSubst.weaken (hn_γ : HNSubst γ) : HNSubst (γ.weaken (A := A)) :=
  cons (fun x => (hn_γ x).rename _) (.var .zero)

def HN' Γ A (M : Exp Γ A) : Type :=
  ∀ {Γ'} {γ : Subst Γ' Γ}, (hn_γ : HNSubst γ) → HN (γ.apply M)

def ftlr : ∀ M, HN' Γ A M
  | .var x,        _, _, hn_γ => hn_γ x
  | .abort M,      _, γ, hn_γ => match ftlr M hn_γ with
                                 | .inl ⟨_, n, r⟩ => .inl ⟨_, .abort n, .abort r⟩
  | .triv,         _, _, hn_γ => .inr .refl
  | .inl M,        _, γ, hn_γ => .inr (.inl ⟨_, ftlr M hn_γ, .refl⟩)
  | .inr M,        _, γ, hn_γ => .inr (.inr ⟨_, ftlr M hn_γ, .refl⟩)
  | .case M M₁ M₂, _, γ, hn_γ => match ftlr M hn_γ with
                                 | .inl ⟨_, n, r⟩          => .inl ⟨_, .case n (ftlr M₁ hn_γ.weaken).wnorm (ftlr M₂ hn_γ.weaken).wnorm, .case r⟩
                                 | .inr (.inl ⟨_, hn₁, r⟩) => .expand (.trans (.case r) .case_inl) <| cast (by lemma) <| ftlr M₁ (hn_γ.cons hn₁)
                                 | .inr (.inr ⟨_, hn₂, r⟩) => .expand (.trans (.case r) .case_inr) <| cast (by lemma) <| ftlr M₂ (hn_γ.cons hn₂)
  | .pair M₁ M₂,   _, γ, hn_γ => .inr ⟨_, ftlr M₁ hn_γ, _, ftlr M₂ hn_γ, .refl⟩
  | .prl M,        _, γ, hn_γ => match ftlr M hn_γ with
                                 | .inl ⟨_, n, r⟩         => .inl ⟨_, .prl n, .prl r⟩
                                 | .inr ⟨_, hn₁, _, _, r⟩ => .expand (.trans (.prl r) .prl_pair) hn₁
  | .prr M,        _, γ, hn_γ => match ftlr M hn_γ with
                                 | .inl ⟨_, n, r⟩         => .inl ⟨_, .prr n, .prr r⟩
                                 | .inr ⟨_, _, _, hn₂, r⟩ => .expand (.trans (.prr r) .prr_pair) hn₂
  | .lam M,        _, γ, hn_γ => .inr ⟨_, fun γ' _ hn₁ => cast (by lemma) <| ftlr M (HNSubst.cons (fun x => (hn_γ x).rename γ') hn₁), .refl⟩
  | .ap M M₁,      _, γ, hn_γ => match ftlr M hn_γ with
                                 | .inl ⟨_, n, r⟩   => .inl ⟨_, .ap n (ftlr M₁ hn_γ).wnorm, .ap r⟩
                                 | .inr ⟨_, hn₂, r⟩ => .expand (.trans (.ap r) .ap_lam) <| hn₂ _ (ftlr M₁ hn_γ)

def wnorm M : WNorm Γ A M :=
  Subst.apply_var.ndrec (ftlr M .var).wnorm

end WeakNormalization

namespace StrongNormalization

inductive SN : (M : Exp Γ A) → Type
  | mk (sn : ∀ {M'}, (s : Steps M M') → SN M') : SN M

-- TODO

end StrongNormalization
