import Common.Meta

#del trailingParser term «∈» 0
#del leadingParser binderPred «∈» 0

syntax "Σ " Lean.binderIdent binderPred ", " term : term

macro_rules
  | `(Σ $x:ident $pred:binderPred, $p) =>
    `(Σ $x:ident, satisfies_binder_pred% $x $pred × $p)
  | `(Σ _ $pred:binderPred, $p) =>
    `(Σ x, satisfies_binder_pred% x $pred × $p)

class Mem (α : Type u) (β : outParam (α → Type v)) where
  mem : ∀ x, β x → Type w

notation:51 y:52 " ∈ " x:52 => Mem.mem x y
binder_predicate x " ∈ " y:term => `($x ∈ $y)

inductive Typ
  | void
  | unit
  | sum  (A₁ A₂ : Typ)
  | prod (A₁ A₂ : Typ)
  | arr  (A₁ A₂ : Typ)

notation "void" => Typ.void
notation "unit" => Typ.unit
infix:53 " ⊎ " => Typ.sum
infix:53 " ⊗ " => Typ.prod
infix:53 " ⇒ " => Typ.arr

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Typ)

notation "⬝" => Ctx.nil
infix:52 "⹁ " => Ctx.cons

section
set_option hygiene false

local infix:51 " ∈ " => Var

inductive Var (A : Typ) : (Γ : Ctx) → Type
  | zero             : A ∈ Γ⹁ A
  | succ (x : A ∈ Γ) : A ∈ Γ⹁ B

end

instance : Mem Ctx fun _ => Typ where
  mem Γ A := Var A Γ

section
set_option hygiene false

local infix:51 " ⊢ " => Exp

inductive Exp : (Γ : Ctx) → (A : Typ) → Type
  | var   (x : A ∈ Γ)                                         : Γ ⊢ A
  | abort (M : Γ ⊢ void)                                      : Γ ⊢ A
  | triv                                                      : Γ ⊢ unit
  | inl   (M : Γ ⊢ A₁)                                        : Γ ⊢ A₁ ⊎ A₂
  | inr   (M : Γ ⊢ A₂)                                        : Γ ⊢ A₁ ⊎ A₂
  | case  (M : Γ ⊢ A₁ ⊎ A₂) (M₁ : Γ⹁ A₁ ⊢ A) (M₂ : Γ⹁ A₂ ⊢ A) : Γ ⊢ A
  | pair  (M₁ : Γ ⊢ A₁) (M₂ : Γ ⊢ A₂)                         : Γ ⊢ A₁ ⊗ A₂
  | prl   (M : Γ ⊢ A₁ ⊗ A₂)                                   : Γ ⊢ A₁
  | prr   (M : Γ ⊢ A₁ ⊗ A₂)                                   : Γ ⊢ A₂
  | lam   (M : Γ⹁ A₁ ⊢ A₂)                                    : Γ ⊢ A₁ ⇒ A₂
  | ap    (M : Γ ⊢ A₁ ⇒ A₂) (M₁ : Γ ⊢ A₁)                     : Γ ⊢ A₂

end

infix:51 " ⊢ " => Exp

def Renaming (Γ Γ' : Ctx) : Type := ∀ A ∈ Γ', A ∈ Γ

infix:51 " ⊩ " => Renaming

@[simp]
def Renaming.cons (γ : Γ ⊩ Γ') (x : A ∈ Γ) : Γ ⊩ Γ'⹁ A
  | _, Var.zero   => x
  | _, Var.succ x => γ _ x

infix:52 "⹁ " => Renaming.cons

@[simp]
def Renaming.extend (γ : Γ ⊩ Γ') : Γ⹁ A ⊩ Γ'⹁ A := (fun _ x => .succ (γ _ x))⹁ .zero

@[simp]
def Renaming.apply (γ : Γ ⊩ Γ') : Γ' ⊢ A → Γ ⊢ A
  | .var x        => .var (γ _ x)
  | .abort M      => .abort (γ.apply M)
  | .triv         => .triv
  | .inl M        => .inl (γ.apply M)
  | .inr M        => .inr (γ.apply M)
  | .case M M₁ M₂ => .case (γ.apply M) (γ.extend.apply M₁) (γ.extend.apply M₂)
  | .pair M₁ M₂   => .pair (γ.apply M₁) (γ.apply M₂)
  | .prl M        => .prl (γ.apply M)
  | .prr M        => .prr (γ.apply M)
  | .lam M        => .lam (γ.extend.apply M)
  | .ap M M₁      => .ap (γ.apply M) (γ.apply M₁)

@[simp]
def Exp.weaken : (M : Γ ⊢ B) → Γ⹁ A ⊢ B := Renaming.apply fun _ => .succ

def Subst (Γ Γ' : Ctx) : Type := ∀ A ∈ Γ', Γ ⊢ A

infix:51 " ⊨ " => Subst

@[simp]
def Subst.cons (γ : Γ ⊨ Γ') (x : Γ ⊢ A) : Γ ⊨ Γ'⹁ A
  | _, Var.zero   => x
  | _, Var.succ x => γ _ x

infix:52 "⹁ " => Subst.cons

@[simp]
def Subst.extend (γ : Γ ⊨ Γ') : Γ⹁ A ⊨ Γ'⹁ A := (fun _ x => .weaken (γ _ x))⹁ .var .zero

@[simp]
def Subst.apply (γ : Γ ⊨ Γ') : Γ' ⊢ A → Γ ⊢ A
  | .var x        => γ _ x
  | .abort M      => .abort (γ.apply M)
  | .triv         => .triv
  | .inl M        => .inl (γ.apply M)
  | .inr M        => .inr (γ.apply M)
  | .case M M₁ M₂ => .case (γ.apply M) (γ.extend.apply M₁) (γ.extend.apply M₂)
  | .pair M₁ M₂   => .pair (γ.apply M₁) (γ.apply M₂)
  | .prl M        => .prl (γ.apply M)
  | .prr M        => .prr (γ.apply M)
  | .lam M        => .lam (γ.extend.apply M)
  | .ap M M₁      => .ap (γ.apply M) (γ.apply M₁)

@[simp]
def Exp.subst (M' : Γ ⊢ A) : (M : Γ⹁ A ⊢ B) → Γ ⊢ B := Subst.apply fun | _, .zero => M' | _, .succ x => .var x

@[simp]
theorem rename_rename  (γ : Γ ⊩ Γ') (γ' : Γ' ⊩ Γ'') (M : Γ'' ⊢ A) : γ.apply (γ'.apply M) = Renaming.apply (fun _ x => γ _ (γ' _ x)) M := by
  induction M generalizing Γ Γ'
    <;> simp [*]
    <;> (try constructor)
    <;> congr
    <;> funext _ x
    <;> cases x
    <;> simp

@[simp]
theorem subst_rename  (γ : Γ ⊨ Γ') (γ' : Γ' ⊩ Γ'') (M : Γ'' ⊢ A) : γ.apply (γ'.apply M) = Subst.apply (fun _ x => γ _ (γ' _ x)) M := by
  induction M generalizing Γ Γ'
    <;> simp [*]
    <;> (try constructor)
    <;> congr
    <;> funext _ x
    <;> cases x
    <;> simp

@[simp]
theorem rename_subst  (γ : Γ ⊩ Γ') (γ' : Γ' ⊨ Γ'') (M : Γ'' ⊢ A) : γ.apply (γ'.apply M) = Subst.apply (fun _ x => γ.apply (γ' _ x)) M := by
  induction M generalizing Γ Γ'
    <;> simp [*]
    <;> (try constructor)
    <;> congr
    <;> funext _ x
    <;> cases x
    <;> simp

@[simp]
theorem subst_subst  (γ : Γ ⊨ Γ') (γ' : Γ' ⊨ Γ'') (M : Γ'' ⊢ A) : γ.apply (γ'.apply M) = Subst.apply (fun _ x => γ.apply (γ' _ x)) M := by
  induction M generalizing Γ Γ'
    <;> simp [*]
    <;> (try constructor)
    <;> congr
    <;> funext _ x
    <;> cases x
    <;> simp

@[simp]
theorem succ_cons_zero (γ : Γ⹁ A ⊨ Γ'⹁ B) : (fun _ x => γ _ (.succ x))⹁ γ _ .zero = γ := by
  funext _ x
  cases x
    <;> simp

@[simp]
theorem subst_var (M : Γ ⊢ A) : Subst.apply (fun _ => .var) M = M := by
  induction M
    <;> simp [*]

macro "subst" : tactic => `(tactic| (simp; congr; funext _ x; cases x <;> simp))

section
set_option hygiene false

local infix:50 " ↦ " => Steps

inductive Steps : (M M' : ⬝ ⊢ A) → Type
  | abort : M ↦ M' → .abort M      ↦ .abort M'
  | case  : M ↦ M' → .case M M₁ M₂ ↦ .case M' M₁ M₂
  | prl   : M ↦ M' → .prl M        ↦ .prl M'
  | prr   : M ↦ M' → .prr M        ↦ .prr M'
  | ap    : M ↦ M' → .ap M M₁      ↦ .ap M' M₁

  | case_inl : .case (.inl M) M₁ M₂ ↦ .subst M M₁
  | case_inr : .case (.inr M) M₁ M₂ ↦ .subst M M₂
  | prl_pair : .prl (.pair M₁ M₂)   ↦ M₁
  | prr_pair : .prr (.pair M₁ M₂)   ↦ M₂
  | ap_lam   : .ap (.lam M) M₁      ↦ .subst M₁ M

end

infix:50 " ↦ " => Steps

theorem Steps.deterministic (s₁ : M ↦ M₁) (s₂ : M ↦ M₂) : M₁ = M₂ := by
  induction s₁
    <;> rename_i s₁ ih
    <;> cases s₂
    <;> (try cases s₁; done)
    <;> rename_i s₂
    <;> (try cases s₂; done)
    <;> congr
    <;> exact ih s₂

inductive Val : (M : ⬝ ⊢ A) → Type
  | triv : Val .triv
  | inl  : Val (.inl M)
  | inr  : Val (.inr M)
  | pair : Val (.pair M₁ M₂)
  | lam  : Val (.lam M)

theorem Val.not_steps (v : Val M) (s : M ↦ M') : False := by
  cases v <;> nomatch s

section
set_option hygiene false

local infix:50 " ↦⋆ " => Reduces

inductive Reduces : (M M' : ⬝ ⊢ A) → Type
  | refl : M ↦⋆ M
  | step : M ↦ M' → M' ↦⋆ M'' → M ↦⋆ M''

end

infix:50 " ↦⋆ " => Reduces

def Reduces.trans : M ↦⋆ M' → M' ↦⋆ M'' → M ↦⋆ M''
  | .refl,     r' => r'
  | .step s r, r' => .step s (r.trans r')

def Reduces.step' (r : M ↦⋆ M') (s : M' ↦ M'') : M ↦⋆ M'' := r.trans (.step s .refl)

def Reduces.comp {F : ⬝ ⊢ A → ⬝ ⊢ B} (f : ∀ {M M'}, M ↦ M' → F M ↦ F M') : M ↦⋆ M' → F M ↦⋆ F M'
  | .refl     => .refl
  | .step s r => .step (f s) (r.comp f)

theorem Reduces.deterministic (r₁ : M ↦⋆ M₁) (r₂ : M ↦⋆ M₂) (v₁ : Val M₁) (v₂ : Val M₂) : M₁ = M₂ := by
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

section
set_option hygiene false

local notation:51 M:52 " ∈ " A:52 => HT A M
local macro_rules
  | `(∀ $M:ident ∈ $A, $p) =>
    `(∀ $M, $M ∈ $A → $p)
  | `(Σ $M:ident ∈ $A, $p) =>
    `(Σ $M:ident, $M ∈ $A × $p)

def HT : ∀ A, ⬝ ⊢ A → Type
  | void,    _ => Empty
  | unit,    M => M ↦⋆ .triv
  | A₁ ⊎ A₂, M => (Σ M₁ ∈ A₁, M ↦⋆ .inl M₁) ⊕ (Σ M₂ ∈ A₂, M ↦⋆ .inr M₂)
  | A₁ ⊗ A₂, M => Σ M₁ ∈ A₁, Σ M₂ ∈ A₂, M ↦⋆ Exp.pair M₁ M₂
  | A₁ ⇒ A₂, M => Σ M₂, M ↦⋆ .lam M₂ × ∀ M₁ ∈ A₁, .subst M₁ M₂ ∈ A₂

end

instance : Mem Typ fun A => ⬝ ⊢ A where
  mem := HT

def HT.expand : ∀ {A M₁ M₂}, M₁ ↦⋆ M₂ → M₂ ∈ A → M₁ ∈ A
  | unit,  _, _, r₁, r₂                     => r₁.trans r₂
  | _ ⊎ _, _, _, r₁, .inl ⟨M₁, ht₁, r₂⟩     => .inl ⟨M₁, ht₁, r₁.trans r₂⟩
  | _ ⊎ _, _, _, r₁, .inr ⟨M₂, ht₂, r₂⟩     => .inr ⟨M₂, ht₂, r₁.trans r₂⟩
  | _ ⊗ _, _, _, r₁, ⟨M₁, ht₁, M₂, ht₂, r₂⟩ => ⟨M₁, ht₁, M₂, ht₂, r₁.trans r₂⟩
  | _ ⇒ _, _, _, r₁, ⟨M₂, r₂, ht₂⟩          => ⟨M₂, r₁.trans r₂, ht₂⟩

def HTSubst (γ : ⬝ ⊨ Γ) : Type := ∀ A x, γ A x ∈ A

instance : Mem Ctx fun Γ => ⬝ ⊨ Γ where
  mem _ := HTSubst

def HTSubst.cons {M : ⬝ ⊢ A} (ht_γ : γ ∈ Γ) (ht_M : M ∈ A) : γ⹁ M ∈ Γ⹁ A
  | _, .zero   => ht_M
  | _, .succ x => ht_γ _ x

infix:52 "⹁ " => HTSubst.cons

def HT' Γ A (M : Γ ⊢ A) : Type := ∀ γ ∈ Γ, γ.apply M ∈ A

notation:50 Γ:51 " ≫ " M:52 " ∈ " A:51 => HT' Γ A M

def Eq_subst (motive : α → Sort u) : a = b → motive a → motive b
  | rfl, m => m

def ftlr : ∀ M, Γ ≫ M ∈ A
  | .var x,        _, ht_γ => ht_γ _ x
  | .abort M,      γ, ht_γ => nomatch ftlr M γ ht_γ
  | .triv,         _, ht_γ => .refl
  | .inl M,        γ, ht_γ => .inl ⟨γ.apply M, ftlr M γ ht_γ, .refl⟩
  | .inr M,        γ, ht_γ => .inr ⟨γ.apply M, ftlr M γ ht_γ, .refl⟩
  | .case M M₁ M₂, γ, ht_γ => match ftlr M γ ht_γ with
                              | .inl ⟨M₃, ht_M₃, r⟩ => .expand (.step' (.comp .case r) .case_inl) <| Eq_subst (HT A) (by subst) <| ftlr M₁ (γ⹁ M₃) (ht_γ⹁ ht_M₃)
                              | .inr ⟨M₃, ht_M₃, r⟩ => .expand (.step' (.comp .case r) .case_inr) <| Eq_subst (HT A) (by subst) <| ftlr M₂ (γ⹁ M₃) (ht_γ⹁ ht_M₃)
  | .pair M₁ M₂,   γ, ht_γ => ⟨γ.apply M₁, ftlr M₁ γ ht_γ, γ.apply M₂, ftlr M₂ γ ht_γ, .refl⟩
  | .prl M,        γ, ht_γ => match ftlr M γ ht_γ with
                              | ⟨_, ht_M₁, _, _, r⟩ => .expand (.step' (.comp .prl r) .prl_pair) ht_M₁
  | .prr M,        γ, ht_γ => match ftlr M γ ht_γ with
                              | ⟨_, _, _, ht_M₂, r⟩ => .expand (.step' (.comp .prr r) .prr_pair) ht_M₂
  | .lam M,        γ, ht_γ => ⟨γ.extend.apply M, .refl, fun M₁ ht_M₁ => Eq_subst (HT _) (by subst) <| ftlr M (γ⹁ M₁) (ht_γ⹁ ht_M₁)⟩
  | .ap M M₁,      γ, ht_γ => match ftlr M γ ht_γ with
                              | ⟨_, r, ht_M₂⟩ => .expand (.step' (.comp (M := γ.apply M) .ap r) .ap_lam) <| ht_M₂ (γ.apply M₁) (ftlr M₁ γ ht_γ)

section
set_option hygiene false

local notation:51 M:52 " ≐ " M':52 " ∈ " A:52 => ExactEq A M M'
local binder_predicate M " ≐ " M':ident " ∈ " A:term => `($M ≐ $M' ∈ $A)
local macro_rules
  | `(∀ $M:ident ≐ $M' ∈ $A, $p) =>
    `(∀ $M, ∀ $M', $M ≐ $M' ∈ $A → $p)
  | `(Σ $M:ident ≐ $M' ∈ $A, $p) =>
    `(Σ $M:ident, Σ $M':ident, $M ≐ $M' ∈ $A × $p)

def ExactEq : ∀ A, ⬝ ⊢ A → ⬝ ⊢ A → Type
  | void,    _, _   => Empty
  | unit,    M, M' => M ↦⋆ .triv × M' ↦⋆ .triv
  | A₁ ⊎ A₂, M, M' => (Σ M₁ ≐ M₁' ∈ A₁, M ↦⋆ .inl M₁ × M' ↦⋆ .inl M₁') ⊕ (Σ M₂ ≐ M₂' ∈ A₂, M ↦⋆ .inr M₂ × M' ↦⋆ .inr M₂')
  | A₁ ⊗ A₂, M, M' => Σ M₁ ≐ M₁' ∈ A₁, Σ M₂ ≐ M₂' ∈ A₂, M ↦⋆ Exp.pair M₁ M₂ × M' ↦⋆ Exp.pair M₁' M₂'
  | A₁ ⇒ A₂, M, M' => Σ M₂, Σ M₂', M ↦⋆ .lam M₂ × M' ↦⋆ .lam M₂' × ∀ M₁ ≐ M₁' ∈ A₁, .subst M₁ M₂ ≐ .subst M₁' M₂' ∈ A₂

end

notation:51 M:52 " ≐ " M':52 " ∈ " A:52 => ExactEq A M M'

def ExactEq.expand : ∀ {A M₁ M₁' M₂ M₂'}, M₁ ↦⋆ M₂ → M₁' ↦⋆ M₂' → M₂ ≐ M₂' ∈ A → M₁ ≐ M₁' ∈ A
  | unit,  _, _, _, _, r₁, r₁', (r₂, r₂')                             => (r₁.trans r₂, r₁'.trans r₂')
  | _ ⊎ _, _, _, _, _, r₁, r₁', .inl ⟨M₁, M₁', eq₁, r₂, r₂'⟩          => .inl ⟨M₁, M₁', eq₁, r₁.trans r₂, r₁'.trans r₂'⟩
  | _ ⊎ _, _, _, _, _, r₁, r₁', .inr ⟨M₂, M₂', eq₂, r₂, r₂'⟩          => .inr ⟨M₂, M₂', eq₂, r₁.trans r₂, r₁'.trans r₂'⟩
  | _ ⊗ _, _, _, _, _, r₁, r₁', ⟨M₁, M₁', eq₁, M₂, M₂', eq₂, r₂, r₂'⟩ => ⟨M₁, M₁', eq₁, M₂, M₂', eq₂, r₁.trans r₂, r₁'.trans r₂'⟩
  | _ ⇒ _, _, _, _, _, r₁, r₁', ⟨M₂, M₂', r₂, r₂', eq₂⟩               => ⟨M₂, M₂', r₁.trans r₂, r₁'.trans r₂', eq₂⟩

def ExactEq.sym : ∀ A {M M'}, M ≐ M' ∈ A → M' ≐ M ∈ A
  | unit,  _, _, (r, r')                             => (r', r)
  | _ ⊎ _, _, _, .inl ⟨M₁, M₁', eq₁, r, r'⟩          => .inl ⟨M₁', M₁, eq₁.sym, r', r⟩
  | _ ⊎ _, _, _, .inr ⟨M₂, M₂', eq₂, r, r'⟩          => .inr ⟨M₂', M₂, eq₂.sym, r', r⟩
  | _ ⊗ _, _, _, ⟨M₁, M₁', eq₁, M₂, M₂', eq₂, r, r'⟩ => ⟨M₁', M₁, eq₁.sym, M₂', M₂, eq₂.sym, r', r⟩
  | _ ⇒ _, _, _, ⟨M₂, M₂', r, r', eq₂⟩               => ⟨M₂', M₂, r', r, fun M₁ M₁' eq₁ => eq₂ M₁' M₁ eq₁.sym |>.sym⟩

def ExactEq.trans : ∀ A {M M' M''}, M ≐ M' ∈ A → M' ≐ M'' ∈ A → M ≐ M'' ∈ A
  | unit, _, _, _, (r, _), (_, r') => (r, r')
  | A₁ ⊎ _, _, _, _, .inl ⟨M₁, _, eq₁, r, r''⟩, .inl ⟨_, M₁', eq₁', r''', r'⟩ =>
    match Reduces.deterministic r'' r''' .inl .inl with
    | rfl => .inl ⟨M₁, M₁', trans A₁ eq₁ eq₁', r, r'⟩
  | _ ⊎ A₂, _, _, _, .inr ⟨M₂, _, eq₂, r, r''⟩, .inr ⟨_, M₂', eq₂', r''', r'⟩ =>
    match Reduces.deterministic r'' r''' .inr .inr with
    | rfl => .inr ⟨M₂, M₂', trans A₂ eq₂ eq₂', r, r'⟩
  | _ ⊎ _, _, _, _, .inl ⟨_, _, _, _, r⟩, .inr ⟨_, _, _, r', _⟩ => nomatch Reduces.deterministic r r' .inl .inr
  | _ ⊎ _, _, _, _, .inr ⟨_, _, _, _, r⟩, .inl ⟨_, _, _, r', _⟩ => nomatch Reduces.deterministic r r' .inr .inl
  | A₁ ⊗ A₂, _, _, _, ⟨M₁, _, eq₁, M₂, _, eq₂, r, r''⟩, ⟨_, M₁', eq₁', _, M₂', eq₂', r''', r'⟩ =>
    match Reduces.deterministic r'' r''' .pair .pair with
    | rfl => ⟨M₁, M₁', trans A₁ eq₁ eq₁', M₂, M₂', trans A₂ eq₂ eq₂', r, r'⟩
  | A₁ ⇒ A₂, _, _, _, ⟨M₂, _, r, r'', eq₂⟩, ⟨_, M₂', r''', r', eq₂'⟩ =>
    match Reduces.deterministic r'' r''' .lam .lam with
    | rfl => ⟨M₂, M₂', r, r', fun M₁ M₁' eq₁ => trans A₂ (eq₂ M₁ M₁ (trans A₁ eq₁ (sym A₁ eq₁))) (eq₂' M₁ M₁' eq₁)⟩

def ExactEqSubst (γ γ' : ⬝ ⊨ Γ) : Type := ∀ A x, γ A x ≐ γ' A x ∈ A

notation:51 γ:52 " ≐ " γ':52 " ∈ " Γ:52 => @ExactEqSubst Γ γ γ'

binder_predicate M " ≐ " M':ident " ∈ " A:term => `($M ≐ $M' ∈ $A)
macro_rules
  | `(∀ $M:ident ≐ $M' ∈ $A, $p) =>
    `(∀ $M, ∀ $M', $M ≐ $M' ∈ $A → $p)
  | `(Σ $M:ident ≐ $M' ∈ $A, $p) =>
    `(Σ $M:ident, Σ $M':ident, $M ≐ $M' ∈ $A × $p)

def ExactEqSubst.cons {γ γ' : ⬝ ⊨ Γ} {M M' : ⬝ ⊢ A} (eq_γ : γ ≐ γ' ∈ Γ) (eq_M : M ≐ M' ∈ A) : γ⹁ M ≐ γ'⹁ M' ∈ Γ⹁ A
  | _, .zero   => eq_M
  | _, .succ x => eq_γ _ x

infix:52 "⹁ " => ExactEqSubst.cons

def ExactEqSubst.sym {γ γ' : ⬝ ⊨ Γ} (eq : γ ≐ γ' ∈ Γ) : γ' ≐ γ ∈ Γ
  | _, x => .sym _ (eq _ x)

def ExactEqSubst.trans {γ γ' γ'' : ⬝ ⊨ Γ} (eq : γ ≐ γ' ∈ Γ) (eq' : γ' ≐ γ'' ∈ Γ) : γ ≐ γ'' ∈ Γ
  | _, x => .trans _ (eq _ x) (eq' _ x)

def ExactEq' Γ A (M M' : Γ ⊢ A) : Type := ∀ γ ≐ γ' ∈ Γ, γ.apply M ≐ γ'.apply M' ∈ A

notation:50 Γ:51 " ≫ " M:52 " ≐ " M':52 " ∈ " A:51 => ExactEq' Γ A M M'

def Eq_subst₂ (motive : α → β → Sort u) : a = b → a' = b' → motive a a' → motive b b'
  | rfl, rfl, m => m

section
set_option hygiene false
local notation:50 Γ:51 " ⊢ " M:52 " ≡ " M':52 " : " A:51 => R Γ A M M'

structure Congruence (R : ∀ Γ A, Γ ⊢ A → Γ ⊢ A → Type) where
  sym   : Γ ⊢ M ≡ M' : A → Γ ⊢ M' ≡ M : A
  trans : Γ ⊢ M ≡ M' : A → Γ ⊢ M' ≡ M'' : A → Γ ⊢ M ≡ M'' : A

  var                                                                                              : Γ ⊢ .var x        ≡ .var x           : A
  abort : ∀ M M', Γ ⊢ M ≡ M' : void                                                                → Γ ⊢ .abort M      ≡ .abort M'        : A
  triv                                                                                             : Γ ⊢ .triv         ≡ .triv            : unit
  inl   : ∀ M M', Γ ⊢ M ≡ M' : A₁                                                                  → Γ ⊢ .inl M        ≡ .inl M'          : A₁ ⊎ A₂
  inr   : ∀ M M', Γ ⊢ M ≡ M' : A₂                                                                  → Γ ⊢ .inr M        ≡ .inr M'          : A₁ ⊎ A₂
  case  : ∀ M M' M₁ M₁' M₂ M₂', Γ ⊢ M ≡ M' : A₁ ⊎ A₂ → Γ⹁ A₁ ⊢ M₁ ≡ M₁' : A → Γ⹁ A₂ ⊢ M₂ ≡ M₂' : A → Γ ⊢ .case M M₁ M₂ ≡ .case M' M₁' M₂' : A
  pair  : ∀ M₁ M₁' M₂ M₂', Γ ⊢ M₁ ≡ M₁' : A₁ → Γ ⊢ M₂ ≡ M₂' : A₂                                   → Γ ⊢ .pair M₁ M₂   ≡ .pair M₁' M₂'    : A₁ ⊗ A₂
  prl   : ∀ M M', Γ ⊢ M ≡ M' : A₁ ⊗ A₂                                                             → Γ ⊢ .prl M        ≡ .prl M'          : A₁
  prr   : ∀ M M', Γ ⊢ M ≡ M' : A₁ ⊗ A₂                                                             → Γ ⊢ .prr M        ≡ .prr M'          : A₂
  lam   : ∀ M M', Γ⹁ A₁ ⊢ M ≡ M' : A₂                                                              → Γ ⊢ .lam M        ≡ .lam M'          : A₁ ⇒ A₂
  ap    : ∀ M M' M₁ M₁', Γ ⊢ M ≡ M' : A₁ ⇒ A₂ → Γ ⊢ M₁ ≡ M₁' : A₁                                  → Γ ⊢ .ap M M₁      ≡ .ap M' M₁'       : A₂

def Congruence.refl (self : Congruence R) {Γ A} : ∀ M, Γ ⊢ M ≡ M : A
  | .var x        => self.var
  | .abort M      => self.abort M M (self.refl M)
  | .triv         => self.triv
  | .inl M        => self.inl M M (self.refl M)
  | .inr M        => self.inr M M (self.refl M)
  | .case M M₁ M₂ => self.case M M M₁ M₁ M₂ M₂ (self.refl M) (self.refl M₁) (self.refl M₂)
  | .pair M₁ M₂   => self.pair M₁ M₁ M₂ M₂ (self.refl M₁) (self.refl M₂)
  | .prl M        => self.prl M M (self.refl M)
  | .prr M        => self.prr M M (self.refl M)
  | .lam M        => self.lam M M (self.refl M)
  | .ap M M₁      => self.ap M M M₁ M₁ (self.refl M) (self.refl M₁)

end

def ExactEq'.congruence : Congruence ExactEq' where
  sym   eq     γ γ' eq_γ := .sym _ (eq γ' γ eq_γ.sym)
  trans eq eq' γ γ' eq_γ := .trans _ (eq γ γ (eq_γ.trans eq_γ.sym)) (eq' γ γ' eq_γ)

  var                                      _ _  eq_γ := eq_γ _ _
  abort _ _ eq_M                           γ γ' eq_γ := nomatch eq_M γ γ' eq_γ
  triv                                     _ _  _    := (.refl, .refl)
  inl   M M' eq_M                          γ γ' eq_γ := .inl ⟨γ.apply M, γ'.apply M', eq_M γ γ' eq_γ, .refl, .refl⟩
  inr   M M' eq_M                          γ γ' eq_γ := .inr ⟨γ.apply M, γ'.apply M', eq_M γ γ' eq_γ, .refl, .refl⟩
  case  _ _ M₁ M₁' M₂ M₂' eq_M eq_M₁ eq_M₂ γ γ' eq_γ := match eq_M γ γ' eq_γ with
                                                        | .inl ⟨M₃, M₃', eq_M₃, r, r'⟩ => .expand (.step' (.comp .case r) .case_inl) (.step' (.comp .case r') .case_inl) <| Eq_subst₂ (ExactEq _) (by subst) (by subst) <| eq_M₁ (γ⹁ M₃) (γ'⹁ M₃') (eq_γ⹁ eq_M₃)
                                                        | .inr ⟨M₃, M₃', eq_M₃, r, r'⟩ => .expand (.step' (.comp .case r) .case_inr) (.step' (.comp .case r') .case_inr) <| Eq_subst₂ (ExactEq _) (by subst) (by subst) <| eq_M₂ (γ⹁ M₃) (γ'⹁ M₃') (eq_γ⹁ eq_M₃)
  pair  M₁ M₁' M₂ M₂' eq_M₁ eq_M₂          γ γ' eq_γ := ⟨γ.apply M₁, γ'.apply M₁', eq_M₁ γ γ' eq_γ, γ.apply M₂, γ'.apply M₂', eq_M₂ γ γ' eq_γ, .refl, .refl⟩
  prl   _ _ eq_M                           γ γ' eq_γ := match eq_M γ γ' eq_γ with
                                                        | ⟨_, _, eq_M₁, _, _, _, r, r'⟩ => .expand (.step' (.comp .prl r) .prl_pair) (.step' (.comp .prl r') .prl_pair) eq_M₁
  prr   _ _ eq_M                           γ γ' eq_γ := match eq_M γ γ' eq_γ with
                                                        | ⟨_, _, _, _, _, eq_M₂, r, r'⟩ => .expand (.step' (.comp .prr r) .prr_pair) (.step' (.comp .prr r') .prr_pair) eq_M₂
  lam   M M' eq_M                          γ γ' eq_γ := ⟨γ.extend.apply M, γ'.extend.apply M', .refl, .refl, fun M₁ M₁' eq_M₁ => Eq_subst₂ (ExactEq _) (by subst) (by subst) <| eq_M (γ⹁ M₁) (γ'⹁ M₁') (eq_γ⹁ eq_M₁)⟩
  ap    M M' M₁ M₁' eq_M eq_M₁             γ γ' eq_γ := match eq_M γ γ' eq_γ with
                                                        | ⟨_, _, r, r', eq_M₂⟩ => .expand (.step' (.comp (M := γ.apply M) .ap r) .ap_lam) (.step' (.comp (M := γ'.apply M') .ap r') .ap_lam) <| eq_M₂ (γ.apply M₁) (γ'.apply M₁') (eq_M₁ γ γ' eq_γ)

section
set_option hygiene false

local notation:50 Γ:51 " ⊢ " M:52 " ≡ " M':52 " : " A:51 => DefEq Γ A M M'

inductive DefEq : ∀ Γ A, Γ ⊢ A → Γ ⊢ A → Type
  | sym   : Γ ⊢ M ≡ M' : A → Γ ⊢ M' ≡ M : A
  | trans : Γ ⊢ M ≡ M' : A → Γ ⊢ M' ≡ M'' : A → Γ ⊢ M ≡ M'' : A

  | var                                                                                              : Γ ⊢ .var x        ≡ .var x           : A
  | abort : ∀ M M', Γ ⊢ M ≡ M' : void                                                                → Γ ⊢ .abort M      ≡ .abort M'        : A
  | triv                                                                                             : Γ ⊢ .triv         ≡ .triv            : unit
  | inl   : ∀ M M', Γ ⊢ M ≡ M' : A₁                                                                  → Γ ⊢ .inl M        ≡ .inl M'          : A₁ ⊎ A₂
  | inr   : ∀ M M', Γ ⊢ M ≡ M' : A₂                                                                  → Γ ⊢ .inr M        ≡ .inr M'          : A₁ ⊎ A₂
  | case  : ∀ M M' M₁ M₁' M₂ M₂', Γ ⊢ M ≡ M' : A₁ ⊎ A₂ → Γ⹁ A₁ ⊢ M₁ ≡ M₁' : A → Γ⹁ A₂ ⊢ M₂ ≡ M₂' : A → Γ ⊢ .case M M₁ M₂ ≡ .case M' M₁' M₂' : A
  | pair  : ∀ M₁ M₁' M₂ M₂', Γ ⊢ M₁ ≡ M₁' : A₁ → Γ ⊢ M₂ ≡ M₂' : A₂                                   → Γ ⊢ .pair M₁ M₂   ≡ .pair M₁' M₂'    : A₁ ⊗ A₂
  | prl   : ∀ M M', Γ ⊢ M ≡ M' : A₁ ⊗ A₂                                                             → Γ ⊢ .prl M        ≡ .prl M'          : A₁
  | prr   : ∀ M M', Γ ⊢ M ≡ M' : A₁ ⊗ A₂                                                             → Γ ⊢ .prr M        ≡ .prr M'          : A₂
  | lam   : ∀ M M', Γ⹁ A₁ ⊢ M ≡ M' : A₂                                                              → Γ ⊢ .lam M        ≡ .lam M'          : A₁ ⇒ A₂
  | ap    : ∀ M M' M₁ M₁', Γ ⊢ M ≡ M' : A₁ ⇒ A₂ → Γ ⊢ M₁ ≡ M₁' : A₁                                  → Γ ⊢ .ap M M₁      ≡ .ap M' M₁'       : A₂

  | case_inl : Γ ⊢ .case (.inl M) M₁ M₂ ≡ .subst M M₁ : A
  | case_inr : Γ ⊢ .case (.inr M) M₁ M₂ ≡ .subst M M₂ : A
  | prl_pair : Γ ⊢ .prl (.pair M₁ M₂)   ≡ M₁          : A₁
  | prr_pair : Γ ⊢ .prr (.pair M₁ M₂)   ≡ M₂          : A₂
  | ap_lam   : Γ ⊢ .ap (.lam M) M₁      ≡ .subst M₁ M : A₂

  | void_η : Γ ⊢ .subst M' M ≡ .abort M'                                                                                                                            : A
  | unit_η : Γ ⊢ M           ≡ .triv                                                                                                                                : unit
  | sum_η  : Γ ⊢ .subst M' M ≡ .case M' (Subst.apply ((fun _ x => .var x.succ)⹁ .inl (.var .zero)) M) (Subst.apply ((fun _ x => .var x.succ)⹁ .inr (.var .zero)) M) : A
  | prod_η : Γ ⊢ M           ≡ .pair (.prl M) (.prr M)                                                                                                              : A₁ ⊗ A₂
  | arr_η  : Γ ⊢ M           ≡ .lam (.ap M.weaken (.var .zero))                                                                                                     : A₁ ⇒ A₂

end

notation:50 Γ:51 " ⊢ " M:52 " ≡ " M':52 " : " A:51 => DefEq Γ A M M'

def DefEq.congruence : Congruence DefEq where
  sym   := sym
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

def ftlr₂ : Γ ⊢ M ≡ M' : A → Γ ≫ M ≐ M' ∈ A
  | .sym   eq      => ExactEq'.congruence.sym (ftlr₂ eq)
  | .trans eq eq' => ExactEq'.congruence.trans (ftlr₂ eq) (ftlr₂ eq')

  | .var                                      => ExactEq'.congruence.var
  | .abort M M' eq_M                          => ExactEq'.congruence.abort M M' (ftlr₂ eq_M)
  | .triv                                     => ExactEq'.congruence.triv
  | .inl M M' eq_M                            => ExactEq'.congruence.inl M M' (ftlr₂ eq_M)
  | .inr M M' eq_M                            => ExactEq'.congruence.inr M M' (ftlr₂ eq_M)
  | .case M M' M₁ M₁' M₂ M₂' eq_M eq_M₁ eq_M₂ => ExactEq'.congruence.case M M' M₁ M₁' M₂ M₂' (ftlr₂ eq_M) (ftlr₂ eq_M₁) (ftlr₂ eq_M₂)
  | .pair M₁ M₁' M₂ M₂' eq_M₁ eq_M₂           => ExactEq'.congruence.pair M₁ M₁' M₂ M₂' (ftlr₂ eq_M₁) (ftlr₂ eq_M₂)
  | .prl M M' eq_M                            => ExactEq'.congruence.prl M M' (ftlr₂ eq_M)
  | .prr M M' eq_M                            => ExactEq'.congruence.prr M M' (ftlr₂ eq_M)
  | .lam M M' eq_M                            => ExactEq'.congruence.lam M M' (ftlr₂ eq_M)
  | .ap M M' M₁ M₁' eq_M eq_M₁                => ExactEq'.congruence.ap M M' M₁ M₁' (ftlr₂ eq_M) (ftlr₂ eq_M₁)

  | .case_inl => fun γ γ' eq_γ => .expand (.step .case_inl .refl) .refl <| Eq_subst (ExactEq _ · _) (by subst) <| ExactEq'.congruence.refl (Exp.subst _ _) γ γ' eq_γ
  | .case_inr => fun γ γ' eq_γ => .expand (.step .case_inr .refl) .refl <| Eq_subst (ExactEq _ · _) (by subst) <| ExactEq'.congruence.refl (Exp.subst _ _) γ γ' eq_γ
  | .prl_pair => fun γ γ' eq_γ => .expand (.step .prl_pair .refl) .refl <| ExactEq'.congruence.refl M' γ γ' eq_γ
  | .prr_pair => fun γ γ' eq_γ => .expand (.step .prr_pair .refl) .refl <| ExactEq'.congruence.refl M' γ γ' eq_γ
  | .ap_lam   => fun γ γ' eq_γ => .expand (.step .ap_lam .refl) .refl <| Eq_subst (ExactEq _ · _) (by subst) <| ExactEq'.congruence.refl (Exp.subst _ _) γ γ' eq_γ

  | .void_η (M' := M') => fun γ γ' eq_γ => nomatch ExactEq'.congruence.refl M' γ γ' eq_γ
  | .unit_η => fun γ γ' eq_γ =>
    match ExactEq'.congruence.refl M γ γ' eq_γ with
    | ⟨r, _⟩ => ⟨r, .refl⟩
  | .sum_η (M' := M') (M := M) => fun γ γ' eq_γ =>
    match ExactEq'.congruence.refl M' γ γ' eq_γ with
    | .inl ⟨M₁, M₁', eq₁, r, r'⟩ => .expand .refl (.step' (.comp .case r') .case_inl) <| Eq_subst₂ (ExactEq _) (by subst) (by subst) <| ExactEq'.congruence.refl M (γ⹁ γ.apply M') (γ'⹁ .inl M₁') (eq_γ⹁ .expand r .refl (.inl ⟨M₁, M₁', eq₁, .refl, .refl⟩))
    | .inr ⟨M₂, M₂', eq₂, r, r'⟩ => .expand .refl (.step' (.comp .case r') .case_inr) <| Eq_subst₂ (ExactEq _) (by subst) (by subst) <| ExactEq'.congruence.refl M (γ⹁ γ.apply M') (γ'⹁ .inr M₂') (eq_γ⹁ .expand r .refl (.inr ⟨M₂, M₂', eq₂, .refl, .refl⟩))
  | .prod_η => fun γ γ' eq_γ =>
    match ExactEq'.congruence.refl M γ γ' eq_γ with
    | ⟨M₁, M₁', eq₁, M₂, M₂', eq₂, r, r'⟩ => ⟨M₁, .prl (γ'.apply M), .expand .refl (.step' (.comp .prl r') .prl_pair) eq₁, M₂, .prr (γ'.apply M), .expand .refl (.step' (.comp .prr r') .prr_pair) eq₂, r, .refl⟩
  | .arr_η => fun γ γ' eq_γ =>
    match ExactEq'.congruence.refl M γ γ' eq_γ with
    | ⟨M₂, M₂', r, r', eq₂⟩ => ⟨M₂, .ap (γ'.extend.apply M.weaken) (.var .zero), r, .refl, fun M₁ M₁' eq₁ => Eq_subst (ExactEq _ _) (by simp) <| .expand .refl (.step' (.comp (M := γ'.apply M) .ap r') .ap_lam) <| eq₂ M₁ M₁' eq₁⟩


def completeness : Γ ≫ M ≐ M' ∈ A → Γ ⊢ M ≡ M' : A := sorry

-- TODO: observational equality
