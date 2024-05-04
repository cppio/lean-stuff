namespace CBV

inductive Typ
  | void
  | unit
  | sum  (A₁ A₂ : Typ)
  | prod (A₁ A₂ : Typ)
  | arr  (A₁ A₂ : Typ)
  | nat

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Typ)

inductive Var (A : Typ) : (Γ : Ctx) → Type
  | zero               : Var A (.cons Γ A)
  | succ (x : Var A Γ) : Var A (.cons Γ A')

inductive Exp : (Γ : Ctx) → (A : Typ) → Type
  | var    (x : Var A Γ)                          : Exp Γ A
  | let    (M : Exp Γ A) (M' : Exp (Γ.cons A) A') : Exp Γ A'

  | absurd (M : Exp Γ .void)                                                          : Exp Γ A
  | triv                                                                              : Exp Γ .unit
  | inl    (M : Exp Γ A₁)                                                             : Exp Γ (.sum A₁ A₂)
  | inr    (M : Exp Γ A₂)                                                             : Exp Γ (.sum A₁ A₂)
  | case   (M : Exp Γ (.sum A₁ A₂)) (M₁ : Exp (Γ.cons A₁) A) (M₂ : Exp (Γ.cons A₂) A) : Exp Γ A
  | pair   (M₁ : Exp Γ A₁) (M₂ : Exp Γ A₂)                                            : Exp Γ (.prod A₁ A₂)
  | fst    (M : Exp Γ (.prod A₁ A₂))                                                  : Exp Γ A₁
  | snd    (M : Exp Γ (.prod A₁ A₂))                                                  : Exp Γ A₂
  | lam    (M : Exp (Γ.cons A₁) A₂)                                                   : Exp Γ (.arr A₁ A₂)
  | ap     (M : Exp Γ (.arr A₁ A₂)) (M₁ : Exp Γ A₁)                                   : Exp Γ A₂
  | zero                                                                              : Exp Γ .nat
  | succ   (M : Exp Γ .nat)                                                           : Exp Γ .nat
  | iter   (M : Exp Γ .nat) (M₁ : Exp Γ A) (M₂ : Exp (Γ.cons A) A)                    : Exp Γ A

  | print  (M : Exp Γ .nat) : Exp Γ .unit
  | read                    : Exp Γ (.sum .unit .nat)

def Renaming (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Var A Γ

namespace Renaming

def cons (γ : Renaming Γ Γ') (y : Var A Γ) : Renaming Γ (Γ'.cons A)
  | _, .zero   => y
  | _, .succ x => γ x

def weaken (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A) :=
  cons (fun _ x => .succ (γ x)) .zero

def apply (γ : Renaming Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x    => .var (γ x)
  | .let M M' => .let (γ.apply M) (γ.weaken.apply M')

  | .absurd M       => .absurd (γ.apply M)
  | .triv           => .triv
  | .inl    M       => .inl    (γ.apply M)
  | .inr    M       => .inr    (γ.apply M)
  | .case   M M₁ M₂ => .case   (γ.apply M) (γ.weaken.apply M₁) (γ.weaken.apply M₂)
  | .pair   M₁ M₂   => .pair   (γ.apply M₁) (γ.apply M₂)
  | .fst    M       => .fst    (γ.apply M)
  | .snd    M       => .snd    (γ.apply M)
  | .lam    M       => .lam    (γ.weaken.apply M)
  | .ap     M M₁    => .ap     (γ.apply M) (γ.apply M₁)
  | .zero           => .zero
  | .succ   M       => .succ   (γ.apply M)
  | .iter   M M₁ M₂ => .iter   (γ.apply M) (γ.apply M₁) (γ.weaken.apply M₂)

  | .print  M => .print (γ.apply M)
  | .read     => .read

end Renaming

def Exp.weaken : (M : Exp Γ A) → Exp (Γ.cons A') A :=
  Renaming.apply fun _ => .succ

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Exp Γ A

namespace Subst

def cons (γ : Subst Γ Γ') (M : Exp Γ A) : Subst Γ (Γ'.cons A)
  | _, .zero   => M
  | _, .succ x => γ x

def weaken (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A) :=
  cons (fun _ x => (γ x).weaken) (.var .zero)

def apply (γ : Subst Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x    => γ x
  | .let M M' => .let (γ.apply M) (γ.weaken.apply M')

  | .absurd M       => .absurd (γ.apply M)
  | .triv           => .triv
  | .inl    M       => .inl    (γ.apply M)
  | .inr    M       => .inr    (γ.apply M)
  | .case   M M₁ M₂ => .case   (γ.apply M) (γ.weaken.apply M₁) (γ.weaken.apply M₂)
  | .pair   M₁ M₂   => .pair   (γ.apply M₁) (γ.apply M₂)
  | .fst    M       => .fst    (γ.apply M)
  | .snd    M       => .snd    (γ.apply M)
  | .lam    M       => .lam    (γ.weaken.apply M)
  | .ap     M M₁    => .ap     (γ.apply M) (γ.apply M₁)
  | .zero           => .zero
  | .succ   M       => .succ   (γ.apply M)
  | .iter   M M₁ M₂ => .iter   (γ.apply M) (γ.apply M₁) (γ.weaken.apply M₂)

  | .print  M => .print (γ.apply M)
  | .read     => .read

end Subst

inductive Val : (M : Exp .nil A) → Type
  | triv                             : Val .triv
  | inl  (V : Val M)                 : Val (.inl M)
  | inr  (V : Val M)                 : Val (.inr M)
  | pair (V₁ : Val M₁) (V₂ : Val M₂) : Val (.pair M₁ M₂)
  | lam                              : Val (.lam M)
  | zero                             : Val .zero
  | succ (V : Val M)                 : Val (.succ M)

instance : Subsingleton (Val M) where
  allEq V V' := by
    induction V
      <;> cases V'
      <;> congr
      <;> apply_assumption

def Exp.subst (M : Exp (.cons .nil A') A) {M' : Exp _ A'} : (V : Val M') → Exp .nil A
  | _ => Subst.cons (fun _ => .var) M' |>.apply M

def Exp.ofNat : (n : Nat) → Exp Γ .nat
  | .zero   => zero
  | .succ n => succ (ofNat n)

def Val.toNat {M : Exp _ .nat} : (V : Val M) → Nat
  | .zero   => .zero
  | .succ V => .succ (toNat V)

def State (A : Typ) : Type :=
  List Nat × Exp .nil A × List Nat

inductive Steps : (S S' : State A) → Type
  | let    (s : Steps (I, M, O) (I', M', O')) : Steps (I, .let    M M'',   O) (I', .let    M' M'',   O')
  | absurd (s : Steps (I, M, O) (I', M', O')) : Steps (I, .absurd M,       O) (I', .absurd M',       O')
  | inl    (s : Steps (I, M, O) (I', M', O')) : Steps (I, .inl    M,       O) (I', .inl    M',       O')
  | inr    (s : Steps (I, M, O) (I', M', O')) : Steps (I, .inr    M,       O) (I', .inr    M',       O')
  | case   (s : Steps (I, M, O) (I', M', O')) : Steps (I, .case   M M₁ M₂, O) (I', .case   M' M₁ M₂, O')
  | fst    (s : Steps (I, M, O) (I', M', O')) : Steps (I, .fst    M,       O) (I', .fst    M',       O')
  | snd    (s : Steps (I, M, O) (I', M', O')) : Steps (I, .snd    M,       O) (I', .snd    M',       O')
  | succ   (s : Steps (I, M, O) (I', M', O')) : Steps (I, .succ   M,       O) (I', .succ   M',       O')
  | iter   (s : Steps (I, M, O) (I', M', O')) : Steps (I, .iter   M M₁ M₂, O) (I', .iter   M' M₁ M₂, O')
  | print  (s : Steps (I, M, O) (I', M', O')) : Steps (I, .print  M,       O) (I', .print  M',       O')

  | pair₁               (s₁ : Steps (I, M₁, O) (I', M₁', O')) : Steps (I, .pair M₁ M₂, O) (I', .pair M₁' M₂,  O')
  | pair₂ (V₁ : Val M₁) (s₂ : Steps (I, M₂, O) (I', M₂', O')) : Steps (I, .pair M₁ M₂, O) (I', .pair M₁  M₂', O')
  | ap₁                 (s  : Steps (I, M,  O) (I', M',  O')) : Steps (I, .ap   M  M₁, O) (I', .ap   M'  M₁,  O')
  | ap₂   (V  : Val M)  (s₁ : Steps (I, M₁, O) (I', M₁', O')) : Steps (I, .ap   M  M₁, O) (I', .ap   M   M₁', O')

  | let'      (V : Val M)                 : Steps (I, .let M M',             O) (I, M'.subst V,              O)
  | case_inl  (V : Val M)                 : Steps (I, .case (.inl M) M₁ M₂,  O) (I, M₁.subst V,              O)
  | case_inr  (V : Val M)                 : Steps (I, .case (.inr M) M₁ M₂,  O) (I, M₂.subst V,              O)
  | fst_pair  (V₁ : Val M₁) (V₂ : Val M₂) : Steps (I, .fst (.pair M₁ M₂),    O) (I, M₁,                      O)
  | snd_pair  (V₁ : Val M₁) (V₂ : Val M₂) : Steps (I, .snd (.pair M₁ M₂),    O) (I, M₂,                      O)
  | ap_lam    (V₁ : Val M₁)               : Steps (I, .ap (.lam M) M₁,       O) (I, M.subst V₁,              O)
  | iter_zero                             : Steps (I, .iter .zero M₁ M₂,     O) (I, M₁,                      O)
  | iter_succ (V : Val M)                 : Steps (I, .iter (.succ M) M₁ M₂, O) (I, .let (.iter M M₁ M₂) M₂, O)

  | print' (V : Val M) : Steps (I,      .print M, O) (I,  .triv,           V.toNat :: O)
  | read₁              : Steps ([],     .read,    O) ([], .inl .triv,      O)
  | read₂              : Steps (n :: I, .read,    O) (I,  .inr (.ofNat n), O)

def Final : (S : State A) → Type
  | (_, M, _) => Val M

theorem Final.not_steps (V : Final S) (s : Steps S S') : False := by
  let (I, M, O) := S
  clear S
  induction V
    <;> cases s
    <;> solve_by_elim

instance : Subsingleton (Σ S', Steps S S') where
  allEq := by
    intro ⟨S', s⟩ ⟨S'', s'⟩
    induction s
      <;> rename_i ih
      <;> cases s'
      <;> (try cases ih _ ‹_›)
      <;> (try rfl)
      <;> (try nomatch Final.not_steps ‹_› ‹Steps (_, _, _) _›)
      <;> (try refine nomatch Final.not_steps ?_ ‹_›; (try constructor) <;> assumption)
      <;> congr
      <;> apply Subsingleton.allEq

def progress : (S : State A) → Final S ⊕ Σ S', Steps S S'
  | (_, M, _) => progress M
  where progress {A I O} : (M : Exp _ A) → Final (I, M, O) ⊕ Σ S', Steps (I, M, O) S'
    | .let M _ => match progress M with
                  | .inl V      => .inr ⟨_, .let' V⟩
                  | .inr ⟨_, s⟩ => .inr ⟨_, .let s⟩

    | .absurd M     => match progress M with
                       | .inr ⟨_, s⟩ => .inr ⟨_, .absurd s⟩
    | .triv         => .inl .triv
    | .inl    M     => match progress M with
                       | .inl V      => .inl (.inl V)
                       | .inr ⟨_, s⟩ => .inr ⟨_, .inl s⟩
    | .inr    M     => match progress M with
                       | .inl V      => .inl (.inr V)
                       | .inr ⟨_, s⟩ => .inr ⟨_, .inr s⟩
    | .case   M ..  => match progress M with
                       | .inl (.inl V) => .inr ⟨_, .case_inl V⟩
                       | .inl (.inr V) => .inr ⟨_, .case_inr V⟩
                       | .inr ⟨_, s⟩   => .inr ⟨_, .case s⟩
    | .pair   M₁ M₂ => match progress M₁, progress M₂ with
                       | .inl V₁,      .inl V₂      => .inl (.pair V₁ V₂)
                       | .inl V₁,      .inr ⟨_, s₂⟩ => .inr ⟨_, .pair₂ V₁ s₂⟩
                       | .inr ⟨_, s₁⟩, _            => .inr ⟨_, .pair₁ s₁⟩
    | .fst    M     => match progress M with
                       | .inl (.pair V₁ V₂) => .inr ⟨_, .fst_pair V₁ V₂⟩
                       | .inr ⟨_, s⟩        => .inr ⟨_, .fst s⟩
    | .snd    M     => match progress M with
                       | .inl (.pair V₁ V₂) => .inr ⟨_, .snd_pair V₁ V₂⟩
                       | .inr ⟨_, s⟩        => .inr ⟨_, .snd s⟩
    | .lam    _     => .inl .lam
    | .ap     M M₁  => match progress M, progress M₁ with
                       | .inl .lam,   .inl V₁      => .inr ⟨_, .ap_lam V₁⟩
                       | .inl V,      .inr ⟨_, s₁⟩ => .inr ⟨_, .ap₂ V s₁⟩
                       | .inr ⟨_, s⟩, _            => .inr ⟨_, .ap₁ s⟩
    | .zero         => .inl .zero
    | .succ   M     => match progress M with
                       | .inl V      => .inl (.succ V)
                       | .inr ⟨_, s⟩ => .inr ⟨_, .succ s⟩
    | .iter   M ..  => match progress M with
                       | .inl .zero     => .inr ⟨_, .iter_zero⟩
                       | .inl (.succ V) => .inr ⟨_, .iter_succ V⟩
                       | .inr ⟨_, s⟩    => .inr ⟨_, .iter s⟩

    | .print M => match progress M with
                  | .inl V      => .inr ⟨_, .print' V⟩
                  | .inr ⟨_, s⟩ => .inr ⟨_, .print s⟩
    | .read    => match I with
                  | []     => .inr ⟨_, .read₁⟩
                  | n :: I => .inr ⟨_, .read₂⟩

instance : Subsingleton (Final S ⊕ Σ S', Steps S S') where
  allEq S₁ S₂ := by
    match S₁ with
    | .inl V₁ =>
      match S₂ with
      | .inl V₂ =>
        cases Subsingleton.elim (α := Val _) V₁ V₂
        rfl
      | .inr ⟨S₂, s₂⟩ =>
        nomatch V₁.not_steps s₂
    | .inr ⟨S₁, s₁⟩ =>
      match S₂ with
      | .inl V₂ =>
        nomatch V₂.not_steps s₁
      | .inr ⟨S₂, s₂⟩ =>
        cases Subsingleton.elim (α := Σ _, _) ⟨S₁, s₁⟩ ⟨S₂, s₂⟩
        rfl

end CBV

namespace Modal

export CBV (Typ Ctx Var)

mutual

inductive Val : (Γ : Ctx) → (A : Typ) → Type
  | var  (x : Var A Γ)                   : Val Γ A

  | triv                                 : Val Γ .unit
  | inl  (V : Val Γ A₁)                  : Val Γ (.sum A₁ A₂)
  | inr  (V : Val Γ A₂)                  : Val Γ (.sum A₁ A₂)
  | pair (V₁ : Val Γ A₁) (V₂ : Val Γ A₂) : Val Γ (.prod A₁ A₂)
  | lam  (M : Exp (Γ.cons A₁) A₂)        : Val Γ (.arr A₁ A₂)
  | zero                                 : Val Γ .nat
  | succ (V : Val Γ .nat)                : Val Γ .nat

inductive Exp : (Γ : Ctx) → (A : Typ) → Type
  | ret    (V : Val Γ A)                                                              : Exp Γ A
  | let    (M : Exp Γ A) (M' : Exp (Γ.cons A) A')                                     : Exp Γ A'

  | absurd (V : Val Γ .void)                                                          : Exp Γ A
  | case   (V : Val Γ (.sum A₁ A₂)) (M₁ : Exp (Γ.cons A₁) A) (M₂ : Exp (Γ.cons A₂) A) : Exp Γ A
  | fst    (V : Val Γ (.prod A₁ A₂))                                                  : Exp Γ A₁
  | snd    (V : Val Γ (.prod A₁ A₂))                                                  : Exp Γ A₂
  | ap     (V : Val Γ (.arr A₁ A₂)) (V₁ : Val Γ A₁)                                   : Exp Γ A₂
  | iter   (V : Val Γ .nat) (M₁ : Exp Γ A) (M₂ : Exp (Γ.cons A) A)                    : Exp Γ A

  | print  (V : Val Γ .nat)                                                           : Exp Γ .unit
  | read                                                                              : Exp Γ (.sum .unit .nat)

end

def Renaming (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Var A Γ

namespace Renaming

def cons (γ : Renaming Γ Γ') (y : Var A Γ) : Renaming Γ (Γ'.cons A)
  | _, .zero   => y
  | _, .succ x => γ x

def weaken (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A) :=
  cons (fun _ x => .succ (γ x)) .zero

mutual -- TODO

def applyV (γ : Renaming Γ Γ') : (V : Val Γ' A) → Val Γ A
  | .var  x     => .var  (γ x)
  | .triv       => .triv
  | .inl  V     => .inl  (γ.applyV V)
  | .inr  V     => .inr  (γ.applyV V)
  | .pair V₁ V₂ => .pair (γ.applyV V₁) (γ.applyV V₂)
  | .lam  M     => .lam  (γ.weaken.applyE M)
  | .zero       => .zero
  | .succ V     => .succ (γ.applyV V)

def applyE (γ : Renaming Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .ret    V       => .ret    (γ.applyV V)
  | .let    M M'    => .let    (γ.applyE M) (γ.weaken.applyE M')
  | .absurd V       => .absurd (γ.applyV V)
  | .case   V M₁ M₂ => .case   (γ.applyV V) (γ.weaken.applyE M₁) (γ.weaken.applyE M₂)
  | .fst    V       => .fst    (γ.applyV V)
  | .snd    V       => .snd    (γ.applyV V)
  | .ap     V V₁    => .ap     (γ.applyV V) (γ.applyV V₁)
  | .iter   V M₁ M₂ => .iter   (γ.applyV V) (γ.applyE M₁) (γ.weaken.applyE M₂)
  | .print  V       => .print  (γ.applyV V)
  | .read           => .read

end

end Renaming

def Val.weaken : (V : Val Γ A) → Val (Γ.cons A') A :=
  Renaming.applyV fun _ => .succ

def Exp.weaken : (M : Exp Γ A) → Exp (Γ.cons A') A :=
  Renaming.applyE fun _ => .succ

def Exp.weaken₁ : (M : Exp (.cons Γ A') A) → Exp ((Γ.cons A'').cons A') A :=
  Renaming.cons (fun _ x => x.succ.succ) .zero |>.applyE

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Val Γ A

namespace Subst

def cons (γ : Subst Γ Γ') (V : Val Γ A) : Subst Γ (Γ'.cons A)
  | _, .zero   => V
  | _, .succ x => γ x

def weaken (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A) :=
  cons (fun _ x => (γ x).weaken) (.var .zero)

mutual -- TODO

def applyV (γ : Subst Γ Γ') : (V : Val Γ' A) → Val Γ A
  | .var  x     => γ x
  | .triv       => .triv
  | .inl  V     => .inl  (γ.applyV V)
  | .inr  V     => .inr  (γ.applyV V)
  | .pair V₁ V₂ => .pair (γ.applyV V₁) (γ.applyV V₂)
  | .lam  M     => .lam  (γ.weaken.applyE M)
  | .zero       => .zero
  | .succ V     => .succ (γ.applyV V)

def applyE (γ : Subst Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .ret    V       => .ret    (γ.applyV V)
  | .let    M M'    => .let    (γ.applyE M) (γ.weaken.applyE M')
  | .absurd V       => .absurd (γ.applyV V)
  | .case   V M₁ M₂ => .case   (γ.applyV V) (γ.weaken.applyE M₁) (γ.weaken.applyE M₂)
  | .fst    V       => .fst    (γ.applyV V)
  | .snd    V       => .snd    (γ.applyV V)
  | .ap     V V₁    => .ap     (γ.applyV V) (γ.applyV V₁)
  | .iter   V M₁ M₂ => .iter   (γ.applyV V) (γ.applyE M₁) (γ.weaken.applyE M₂)
  | .print  V       => .print  (γ.applyV V)
  | .read           => .read

end

end Subst

def Exp.subst (M : Exp (.cons Γ A') A) (V : Val Γ A') : Exp Γ A :=
  Subst.cons (fun _ => .var) V |>.applyE M

def Val.ofNat : (n : Nat) → Val Γ .nat
  | .zero   => zero
  | .succ n => succ (ofNat n)

def Val.toNat : (V : Val .nil .nat) → Nat
  | .zero   => .zero
  | .succ V => .succ (toNat V)

def State (A : Typ) : Type :=
  List Nat × Exp .nil A × List Nat

inductive Steps : (S S' : State A) → Type
  | let₁ (s : Steps (I, M, O) (I', M', O')) : Steps (I, .let M M'',      O) (I', .let M' M'', O')
  | let₂                                    : Steps (I, .let (.ret V) M, O) (I, M.subst V, O)

  | case_inl  : Steps (I, .case (.inl V) M₁ M₂,  O) (I, M₁.subst V,              O)
  | case_inr  : Steps (I, .case (.inr V) M₁ M₂,  O) (I, M₂.subst V,              O)
  | fst_pair  : Steps (I, .fst (.pair V₁ V₂),    O) (I, .ret V₁,                 O)
  | snd_pair  : Steps (I, .snd (.pair V₁ V₂),    O) (I, .ret V₂,                 O)
  | ap_lam    : Steps (I, .ap (.lam M) V₁,       O) (I, M.subst V₁,              O)
  | iter_zero : Steps (I, .iter .zero M₁ M₂,     O) (I, M₁,                      O)
  | iter_succ : Steps (I, .iter (.succ V) M₁ M₂, O) (I, .let (.iter V M₁ M₂) M₂, O)

  | print : Steps (I,      .print V, O) (I,  .ret .triv,             V.toNat :: O)
  | read₁ : Steps ([],     .read,    O) ([], .ret (.inl .triv),      O)
  | read₂ : Steps (n :: I, .read,    O) (I,  .ret (.inr (.ofNat n)), O)

inductive Final : (S : State A) → Type
  | ret : Final (I, .ret V, O)

instance : Subsingleton (Final S) where
  allEq := by
    intro .ret .ret
    rfl

theorem Final.not_steps : (V : Final S) → (s : Steps S S') → False := nofun

instance : Subsingleton (Σ S', Steps S S') where
  allEq := by
    intro ⟨S', s⟩ ⟨S'', s'⟩
    induction s
      <;> rename_i ih
      <;> cases s'
      <;> (try cases ih _ ‹_›)
      <;> (try rfl)
      <;> nomatch Final.not_steps .ret ‹_›

def progress : (S : State A) → Final S ⊕ Σ S', Steps S S'
  | (I, M, O) => progress I O M
  where progress {A} I O : (M : Exp _ A) → Final (I, M, O) ⊕ Σ S', Steps (I, M, O) S'
    | .ret V    => .inl .ret
    | .let M M' => match progress I O M with
                   | .inl .ret   => .inr ⟨_, .let₂⟩
                   | .inr ⟨_, s⟩ => .inr ⟨_, .let₁ s⟩

    | .case (.inl _) ..  => .inr ⟨_, .case_inl⟩
    | .case (.inr _) ..  => .inr ⟨_, .case_inr⟩
    | .fst  (.pair ..)   => .inr ⟨_, .fst_pair⟩
    | .snd  (.pair ..)   => .inr ⟨_, .snd_pair⟩
    | .ap   (.lam _) _   => .inr ⟨_, .ap_lam⟩
    | .iter .zero ..     => .inr ⟨_, .iter_zero⟩
    | .iter (.succ _) .. => .inr ⟨_, .iter_succ⟩

    | .print _ => .inr ⟨_, .print⟩
    | .read    => match I with
                  | []     => .inr ⟨_, .read₁⟩
                  | _ :: _ => .inr ⟨_, .read₂⟩

instance : Subsingleton (Final S ⊕ Σ S', Steps S S') where
  allEq S₁ S₂ := by
    match S₁ with
    | .inl V₁ =>
      match S₂ with
      | .inl V₂ =>
        cases Subsingleton.elim V₁ V₂
        rfl
      | .inr ⟨S₂, s₂⟩ =>
        nomatch V₁.not_steps s₂
    | .inr ⟨S₁, s₁⟩ =>
      match S₂ with
      | .inl V₂ =>
        nomatch V₂.not_steps s₁
      | .inr ⟨S₂, s₂⟩ =>
        cases Subsingleton.elim (α := Σ _, _) ⟨S₁, s₁⟩ ⟨S₂, s₂⟩
        rfl

inductive Reduces : (S S' : State A) → Type
  | refl                                       : Reduces S S
  | step (s : Steps S S') (r : Reduces S' S'') : Reduces S S''

def Reduces.lift {F : (S : State A) → State A'} (f : ∀ {S S'}, (s : Steps S S') → Steps (F S) (F S')) : (r : Reduces S S') → Reduces (F S) (F S')
  | refl     => refl
  | step s r => step (f s) (r.lift f)

end Modal

namespace CBV_to_Modal

def translateExp : (M : CBV.Exp Γ A) → Modal.Exp Γ A
  | .var x    => .ret (.var x)
  | .let M M' => .let (translateExp M) (translateExp M')

  | .absurd M       => .let (translateExp M) (.absurd (.var .zero))
  | .triv           => .ret .triv
  | .inl    M       => .let (translateExp M) (.ret (.inl (.var .zero)))
  | .inr    M       => .let (translateExp M) (.ret (.inr (.var .zero)))
  | .case   M M₁ M₂ => .let (translateExp M) (.case (.var .zero) (translateExp M₁).weaken₁ (translateExp M₂).weaken₁)
  | .pair   M₁ M₂   => .let (translateExp M₁) (.let (translateExp M₂).weaken (.ret (.pair (.var (.succ .zero)) (.var .zero))))
  | .fst    M       => .let (translateExp M) (.fst (.var .zero))
  | .snd    M       => .let (translateExp M) (.snd (.var .zero))
  | .lam    M       => .ret (.lam (translateExp M))
  | .ap     M M₁    => .let (translateExp M) (.let (translateExp M₁).weaken (.ap (.var (.succ .zero)) (.var .zero)))
  | .zero           => .ret .zero
  | .succ   M       => .let (translateExp M) (.ret (.succ (.var .zero)))
  | .iter   M M₁ M₂ => .let (translateExp M) (.iter (.var .zero) (translateExp M₁).weaken (translateExp M₂).weaken₁)

  | .print  M       => .let (translateExp M) (.print (.var .zero))
  | .read           => .read

def translateState : (S : CBV.State A) → Modal.State A
  | (I, M, O) => (I, translateExp M, O)

def translateSteps : (s : CBV.Steps S S') → Σ S'', Modal.Reduces (translateState S) S'' × Modal.Reduces (translateState S') S''
  | .let    s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .absurd s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .inl    s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .inr    s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .case   s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .fst    s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .snd    s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .succ   s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .iter   s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .print  s => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩

  | .pair₁    s₁ => let ⟨_, r₁, r₁'⟩ := translateSteps s₁; ⟨_, .lift .let₁ r₁, .lift .let₁ r₁'⟩
  | .pair₂ V₁ s₂ => by dsimp [translateState, translateExp]; sorry
  | .ap₁      s  => let ⟨_, r, r'⟩ := translateSteps s; ⟨_, .lift .let₁ r, .lift .let₁ r'⟩
  | .ap₂   V  s₁ => by dsimp [translateState, translateExp]; sorry

  | .let'      V     => by dsimp [translateState, translateExp]; sorry
  | .case_inl  V     => by dsimp [translateState, translateExp]; sorry
  | .case_inr  V     => by dsimp [translateState, translateExp]; sorry
  | .fst_pair  V₁ V₂ => by dsimp [translateState, translateExp]; sorry
  | .snd_pair  V₁ V₂ => by dsimp [translateState, translateExp]; sorry
  | .ap_lam    V₁    => by dsimp [translateState, translateExp]; sorry
  | .iter_zero       => by dsimp [translateState, translateExp]; exact ⟨_, .step .let₂ (by simp [Modal.Exp.subst, Modal.Subst.applyE, Modal.Subst.applyV, Modal.Subst.cons]; refine .step .iter_zero ?_; sorry), .refl⟩
  | .iter_succ V     => by dsimp [translateState, translateExp]; sorry

  | .print' V => by dsimp [translateState, translateExp]; sorry
  | .read₁    => ⟨_, .step .read₁ .refl, .step .let₂ <| by simp [Modal.Exp.subst, Modal.Subst.applyE, Modal.Subst.applyV, Modal.Subst.cons, Modal.Subst.weaken]; sorry⟩
  | .read₂    => by dsimp [translateState, translateExp]; sorry

end CBV_to_Modal

namespace CBV_to_Modal'

def ret? : (M : Modal.Val Γ A ⊕ Modal.Exp Γ A) → Modal.Exp Γ A
  | .inl V => .ret V
  | .inr M => M

def translateExp : (M : CBV.Exp Γ A) → Modal.Val Γ A ⊕ Modal.Exp Γ A
  | .var x    => .inl (.var x)
  | .let M M' => .inr (.let (ret? (translateExp M)) (ret? (translateExp M')))

  | .absurd M       => match translateExp M with
                       | .inl V => .inr (.absurd V)
                       | .inr M => .inr (.let M (.absurd (.var .zero)))
  | .triv           => .inl .triv
  | .inl    M       => match translateExp M with
                       | .inl V => .inl (.inl V)
                       | .inr M => .inr (.let M (.ret (.inl (.var .zero))))
  | .inr    M       => match translateExp M with
                       | .inl V => .inl (.inr V)
                       | .inr M => .inr (.let M (.ret (.inr (.var .zero))))
  | .case   M M₁ M₂ => match translateExp M with
                       | .inl V => .inr (.case V (ret? (translateExp M₁)) (ret? (translateExp M₂)))
                       | .inr M => .inr (.let M (.case (.var .zero) (ret? (translateExp M₁)).weaken₁ (ret? (translateExp M₂)).weaken₁))
  | .pair   M₁ M₂   => match translateExp M₁, translateExp M₂ with
                       | .inl V₁, .inl V₂ => .inl (.pair V₁ V₂)
                       | .inr M₁, .inl V₂ => .inr (.let M₁ (.ret (.pair (.var .zero) V₂.weaken)))
                       | .inl V₁, .inr M₂ => .inr (.let M₂ (.ret (.pair V₁.weaken (.var .zero))))
                       | .inr M₁, .inr M₂ => .inr (.let M₁ (.let M₂.weaken (.ret (.pair (.var (.succ .zero)) (.var .zero)))))
  | .fst    M       => match translateExp M with
                       | .inl V => .inr (.fst V)
                       | .inr M => .inr (.let M (.fst (.var .zero)))
  | .snd    M       => match translateExp M with
                       | .inl V => .inr (.snd V)
                       | .inr M => .inr (.let M (.snd (.var .zero)))
  | .lam    M       => .inl (.lam (ret? (translateExp M)))
  | .ap     M₁ M₂   => match translateExp M₁, translateExp M₂ with
                       | .inl V₁, .inl V₂ => .inr (.ap V₁ V₂)
                       | .inr M₁, .inl V₂ => .inr (.let M₁ (.ap (.var .zero) V₂.weaken))
                       | .inl V₁, .inr M₂ => .inr (.let M₂ (.ap V₁.weaken (.var .zero)))
                       | .inr M₁, .inr M₂ => .inr (.let M₁ (.let M₂.weaken (.ap (.var (.succ .zero)) (.var .zero))))
  | .zero           => .inl .zero
  | .succ   M       => match translateExp M with
                       | .inl V => .inl (.succ V)
                       | .inr M => .inr (.let M (.ret (.succ (.var .zero))))
  | .iter   M M₁ M₂ => match translateExp M with
                       | .inl V => .inr (.iter V (ret? (translateExp M₁)) (ret? (translateExp M₂)))
                       | .inr M => .inr (.let M (.iter (.var .zero) (ret? (translateExp M₁)).weaken (ret? (translateExp M₂)).weaken₁))

  | .print M => match translateExp M with
                | .inl V => .inr (.print V)
                | .inr M => .inr (.let M (.print (.var .zero)))
  | .read    => .inr .read

def translateState : (S : CBV.State A) → Modal.State A
  | (I, M, O) => (I, ret? (translateExp M), O)

def translateSteps : (s : CBV.Steps S S') → Modal.Reduces (translateState S) (translateState S')
  | .let    s => by dsimp [translateState, translateExp]; sorry
  | .absurd s => have := translateSteps s; by dsimp [translateState, translateExp] at this ⊢; sorry
  | .inl    s => by dsimp [translateState, translateExp]; sorry
  | .inr    s => by dsimp [translateState, translateExp]; sorry
  | .case   s => by dsimp [translateState, translateExp]; sorry
  | .fst    s => by dsimp [translateState, translateExp]; sorry
  | .snd    s => by dsimp [translateState, translateExp]; sorry
  | .succ   s => by dsimp [translateState, translateExp]; sorry
  | .iter   s => by dsimp [translateState, translateExp]; sorry
  | .print  s => by dsimp [translateState, translateExp]; sorry

  | .pair₁    s₁ => by dsimp [translateState, translateExp]; sorry
  | .pair₂ V₁ s₂ => by dsimp [translateState, translateExp]; sorry
  | .ap₁      s  => by dsimp [translateState, translateExp]; sorry
  | .ap₂   V  s₁ => by dsimp [translateState, translateExp]; sorry

  | .let'      V     => by dsimp [translateState, translateExp]; sorry
  | .case_inl  V     => by dsimp [translateState, translateExp]; sorry
  | .case_inr  V     => by dsimp [translateState, translateExp]; sorry
  | .fst_pair  V₁ V₂ => by dsimp [translateState, translateExp]; sorry
  | .snd_pair  V₁ V₂ => by dsimp [translateState, translateExp]; sorry
  | .ap_lam    V₁    => by dsimp [translateState, translateExp]; sorry
  | .iter_zero       => by dsimp [translateState, translateExp]; sorry
  | .iter_succ V     => by dsimp [translateState, translateExp]; sorry

  | .print' V => by dsimp [translateState, translateExp]; sorry
  | .read₁    => by dsimp [translateState, translateExp]; sorry
  | .read₂    => by dsimp [translateState, translateExp]; sorry

end CBV_to_Modal'
