import Common.Structural

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
  | var (x : Var A Γ)                          : Exp Γ A
  | let (M : Exp Γ A) (M' : Exp (Γ.cons A) A') : Exp Γ A'

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

  | print (M : Exp Γ .nat) : Exp Γ .unit
  | read                   : Exp Γ (.sum .unit .nat)

inductive Val : (M : Exp Γ A) → Type
  | var x : Val (.var x)

  | triv                                                 : Val .triv
  | inl  (V : Val (A := A₁) M)                           : Val (A := .sum A₁ A₂)  (.inl M)
  | inr  (V : Val (A := A₂) M)                           : Val (A := .sum A₁ A₂)  (.inr M)
  | pair (V₁ : Val (A := A₁) M₁) (V₂ : Val (A := A₂) M₂) : Val (.pair M₁ M₂)
  | lam  M                                               : Val (A := .arr A₁ A₂)  (.lam M)
  | zero                                                 : Val .zero
  | succ (V : Val M)                                     : Val (.succ M)

instance : Subsingleton (Val M) where
  allEq V V' := by
    induction V
      <;> cases V'
      <;> congr
      <;> apply_assumption

inductive Renaming (Γ : Ctx) : (Γ' : Ctx) → Type
 | nil                                    : Renaming Γ .nil
 | cons (γ : Renaming Γ Γ') (x : Var A Γ) : Renaming Γ (Γ'.cons A)

@[simp]
def Renaming.map (f : ∀ {A}, (x : Var A Γ) → Var A Γ'') : (γ : Renaming Γ Γ') → Renaming Γ'' Γ'
  | nil      => nil
  | cons γ x => cons (γ.map @f) (f x)

@[simp]
def Renaming.weaken (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A) :=
  cons (γ.map .succ) .zero

def Renaming.id : ∀ {Γ}, Renaming Γ Γ
  | .nil     => nil
  | .cons .. => cons (map .succ id) .zero

@[simp]
theorem Renaming.map_map : map f (map g γ) = γ.map (f <| g ·) :=
  by induction γ <;> simp [*]

@[simp]
def Var.rename : (γ : Renaming Γ Γ') → (x : Var A Γ') → Var A Γ
  | .cons _ x, zero   => x
  | .cons γ _, succ x => x.rename γ

@[simp]
theorem Var.rename_map : rename (.map f γ) x = f (x.rename γ) :=
  by induction x <;> cases γ <;> apply_assumption

@[simp]
theorem Var.rename_id : rename .id x = x :=
  by induction x <;> simp [*]

@[simp]
theorem Renaming.map_rename {γ : Renaming Γ Γ'} : map (f <| ·.rename γ) .id = map f γ :=
  by induction γ <;> simp [*]

def Exp.rename (γ : Renaming Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x    => .var (x.rename γ)
  | .let M M' => .let (M.rename γ) (M'.rename γ.weaken)

  | absurd M       => absurd (M.rename γ)
  | triv           => triv
  | inl    M       => inl    (M.rename γ)
  | inr    M       => inr    (M.rename γ)
  | case   M M₁ M₂ => case   (M.rename γ) (M₁.rename γ.weaken) (M₂.rename γ.weaken)
  | pair   M₁ M₂   => pair   (M₁.rename γ) (M₂.rename γ)
  | fst    M       => fst    (M.rename γ)
  | snd    M       => snd    (M.rename γ)
  | lam    M       => lam    (M.rename γ.weaken)
  | ap     M M₁    => ap     (M.rename γ) (M₁.rename γ)
  | zero           => zero
  | succ   M       => succ   (M.rename γ)
  | iter   M M₁ M₂ => iter   (M.rename γ) (M₁.rename γ) (M₂.rename γ.weaken)

  | print M => print (M.rename γ)
  | read    => read

def Val.rename (γ : Renaming Γ Γ') : (V : Val (A := A) M) → Val (M.rename γ)
  | var x => var _

  | triv       => triv
  | inl  V     => inl  (V.rename γ)
  | inr  V     => inr  (V.rename γ)
  | pair V₁ V₂ => pair (V₁.rename γ) (V₂.rename γ)
  | lam  M     => lam  _
  | zero       => zero
  | succ V     => succ (V.rename γ)

def Exp.weaken : (M : Exp Γ A) → Exp (Γ.cons A') A :=
  rename (.map .succ .id)

def Val.weaken : (V : @Val Γ A M) → Val (M.weaken (A' := A')) :=
  rename (.map .succ .id)

inductive Subst (Γ : Ctx) : (Γ' : Ctx) → Type
 | nil                                    : Subst Γ .nil
 | cons (γ : Subst Γ Γ') (V : @Val Γ A M) : Subst Γ (Γ'.cons A)

def Subst.map {f : ∀ {A}, (M : Exp Γ A) → Exp Γ'' A} (g : ∀ {A M}, (V : Val M) → Val (@f A M)) : (γ : Subst Γ Γ') → Subst Γ'' Γ'
  | nil      => nil
  | cons γ M => cons (γ.map (f := @f) @g) (g M)

def Subst.weaken (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A) :=
  cons (γ.map .weaken) (.var .zero)

@[simp]
def Subst.ofRenaming {f : ∀ {A}, (x : Var A Γ) → Exp Γ'' A} (g : ∀ {A}, (x : Var A Γ) → Val (f x)) : (γ : Renaming Γ Γ') → Subst Γ'' Γ'
  | .nil      => nil
  | .cons γ x => cons (ofRenaming (f := @f) @g γ) (g x)

@[simp]
theorem Subst.ofRenaming_map : ofRenaming f (γ.map g) = ofRenaming (f <| g ·) γ :=
  by induction γ <;> simp [*]

@[simp]
def Var.subst : (γ : Subst Γ Γ') → (x : Var A Γ') → Exp Γ A
  | .cons (M := M) .., zero   => M
  | .cons γ _,         succ x => x.subst γ

@[simp]
def Exp.subst (γ : Subst Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .var x    => x.subst γ
  | .let M M' => .let (M.subst γ) (M'.subst γ.weaken)

  | absurd M       => absurd (M.subst γ)
  | triv           => triv
  | inl    M       => inl    (M.subst γ)
  | inr    M       => inr    (M.subst γ)
  | case   M M₁ M₂ => case   (M.subst γ) (M₁.subst γ.weaken) (M₂.subst γ.weaken)
  | pair   M₁ M₂   => pair   (M₁.subst γ) (M₂.subst γ)
  | fst    M       => fst    (M.subst γ)
  | snd    M       => snd    (M.subst γ)
  | lam    M       => lam    (M.subst γ.weaken)
  | ap     M M₁    => ap     (M.subst γ) (M₁.subst γ)
  | zero           => zero
  | succ   M       => succ   (M.subst γ)
  | iter   M M₁ M₂ => iter   (M.subst γ) (M₁.subst γ) (M₂.subst γ.weaken)

  | print M => print (M.subst γ)
  | read    => read

def Exp.sub (M : Exp (Γ.cons A') A) {M' : Exp Γ A'} (V : Val M') : Exp Γ A :=
  subst (.cons (.ofRenaming .var .id) V) M

def Exp.ofNat : (n : Nat) → Exp Γ .nat
  | .zero   => zero
  | .succ n => succ (ofNat n)

def Val.ofNat : (n : Nat) → Val (.ofNat (Γ := Γ) n)
  | .zero   => zero
  | .succ n => succ (ofNat n)

@[simp]
def Val.toNat : (V : @Val .nil .nat M) → Nat
  | zero   => .zero
  | succ V => .succ V.toNat

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

  | let'      (V : Val M)                 : Steps (I, .let M M',             O) (I, M'.sub V,                O)
  | case_inl  (V : Val M)                 : Steps (I, .case (.inl M) M₁ M₂,  O) (I, M₁.sub V,                O)
  | case_inr  (V : Val M)                 : Steps (I, .case (.inr M) M₁ M₂,  O) (I, M₂.sub V,                O)
  | fst_pair  (V₁ : Val M₁) (V₂ : Val M₂) : Steps (I, .fst (.pair M₁ M₂),    O) (I, M₁,                      O)
  | snd_pair  (V₁ : Val M₁) (V₂ : Val M₂) : Steps (I, .snd (.pair M₁ M₂),    O) (I, M₂,                      O)
  | ap_lam    (V₁ : Val M₁)               : Steps (I, .ap (.lam M) M₁,       O) (I, M.sub V₁,                O)
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

inductive Progress (S : State A)
  | final (V : Final S)
  | steps (s : Steps S S')

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

instance : Subsingleton (Progress S) where
  allEq
    | .final V₁, .final V₂ => match Subsingleton.allEq (α := Val _) V₁ V₂ with | rfl => rfl
    | .final V₁, .steps s₂ => nomatch V₁.not_steps s₂
    | .steps s₁, .final V₂ => nomatch V₂.not_steps s₁
    | .steps s₁, .steps s₂ => match Subsingleton.allEq (α := Σ _, _) ⟨_, s₁⟩ ⟨_, s₂⟩ with | rfl => rfl

def Progress.then (f : Exp _ A → Exp _ A')
  (steps : ∀ {I₁' M₁' O₁'}, Steps (I₁, M₁, O₁) (I₁', M₁', O₁') → Steps (I₁, f M₁, O₁) (I₁', f M₁', O₁'))
  (final : Final (I₁, M₁, O₁) → Progress (I₁, f M₁, O₁))
: Progress (I₁, M₁, O₁) → Progress (I₁, f M₁, O₁)
  | .steps s => .steps (steps s)
  | .final V => final V

def progress : (S : State A) → Progress S
  | (_, M, _) => progress M
  where progress {A I O} : (M : Exp _ A) → Progress (I, M, O)
    | .let M _ => progress M |>.then (.let · _) .let fun V => .steps <| .let' V

    | .absurd M     => progress M |>.then .absurd .absurd nofun
    | .triv         => .final .triv
    | .inl    M     => progress M |>.then .inl .inl fun V => .final <| .inl V
    | .inr    M     => progress M |>.then .inr .inr fun V => .final <| .inr V
    | .case   M ..  => progress M |>.then (.case · ..) .case fun | .inl V => .steps <| .case_inl V | .inr V => .steps <| .case_inr V
    | .pair   M₁ M₂ => progress M₁ |>.then (.pair · _) .pair₁ fun V₁ => progress M₂ |>.then (.pair _) (.pair₂ V₁) fun V₂ => .final <| .pair V₁ V₂
    | .fst    M     => progress M |>.then .fst .fst fun | .pair V₁ V₂ => .steps <| .fst_pair V₁ V₂
    | .snd    M     => progress M |>.then .snd .snd fun | .pair V₁ V₂ => .steps <| .snd_pair V₁ V₂
    | .lam    M     => .final <| .lam M
    | .ap     M M₁  => progress M |>.then (.ap · _) .ap₁ fun | V@(.lam _) => progress M₁ |>.then (.ap _) (.ap₂ V) fun V₁ => .steps <| .ap_lam V₁
    | .zero         => .final .zero
    | .succ   M     => progress M |>.then .succ .succ fun V => .final <| .succ V
    | .iter   M ..  => progress M |>.then (.iter · ..) .iter fun | .zero => .steps .iter_zero | .succ V => .steps <| .iter_succ V

    | .print M => progress M |>.then .print .print fun V => .steps <| .print' V
    | .read    => match I with
                  | []     => .steps .read₁
                  | _ :: _ => .steps .read₂

end CBV

namespace Modal

export CBV (Typ Ctx Var Renaming)

mutual

inductive Val : (Γ : Ctx) → (A : Typ) → Type
  | var (x : Var A Γ) : Val Γ A

  | triv                                 : Val Γ .unit
  | inl  (V : Val Γ A₁)                  : Val Γ (.sum A₁ A₂)
  | inr  (V : Val Γ A₂)                  : Val Γ (.sum A₁ A₂)
  | pair (V₁ : Val Γ A₁) (V₂ : Val Γ A₂) : Val Γ (.prod A₁ A₂)
  | lam  (M : Exp (Γ.cons A₁) A₂)        : Val Γ (.arr A₁ A₂)
  | zero                                 : Val Γ .nat
  | succ (V : Val Γ .nat)                : Val Γ .nat

inductive Exp : (Γ : Ctx) → (A : Typ) → Type
  | ret (V : Val Γ A)                          : Exp Γ A
  | let (M : Exp Γ A) (M' : Exp (Γ.cons A) A') : Exp Γ A'

  | absurd (V : Val Γ .void)                                                          : Exp Γ A
  | case   (V : Val Γ (.sum A₁ A₂)) (M₁ : Exp (Γ.cons A₁) A) (M₂ : Exp (Γ.cons A₂) A) : Exp Γ A
  | fst    (V : Val Γ (.prod A₁ A₂))                                                  : Exp Γ A₁
  | snd    (V : Val Γ (.prod A₁ A₂))                                                  : Exp Γ A₂
  | ap     (V : Val Γ (.arr A₁ A₂)) (V₁ : Val Γ A₁)                                   : Exp Γ A₂
  | iter   (V : Val Γ .nat) (M₁ : Exp Γ A) (M₂ : Exp (Γ.cons A) A)                    : Exp Γ A

  | print (V : Val Γ .nat) : Exp Γ .unit
  | read                   : Exp Γ (.sum .unit .nat)

end

set_option linter.unusedVariables false in
@[structural]
mutual

@[simp]
def Val.rename (γ : Renaming Γ Γ') : (V : Val Γ' A) → Val Γ A
  | .var x => .var (x.rename γ)

  | .triv       => .triv
  | .inl  V     => .inl  (V.rename γ)
  | .inr  V     => .inr  (V.rename γ)
  | .pair V₁ V₂ => .pair (V₁.rename γ) (V₂.rename γ)
  | .lam  M     => .lam  (M.rename γ.weaken)
  | .zero       => .zero
  | .succ V     => .succ (V.rename γ)

@[simp]
def Exp.rename (γ : Renaming Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .ret V    => .ret (V.rename γ)
  | .let M M' => .let (M.rename γ) (M'.rename γ.weaken)

  | .absurd V       => .absurd (V.rename γ)
  | .case   V M₁ M₂ => .case   (V.rename γ) (M₁.rename γ.weaken) (M₂.rename γ.weaken)
  | .fst    V       => .fst    (V.rename γ)
  | .snd    V       => .snd    (V.rename γ)
  | .ap     V V₁    => .ap     (V.rename γ) (V₁.rename γ)
  | .iter   V M₁ M₂ => .iter   (V.rename γ) (M₁.rename γ) (M₂.rename γ.weaken)

  | .print V => .print (V.rename γ)
  | .read    => .read

end

@[simp]
theorem Val.rename_rename {γ : Renaming Γ Γ'} {γ' : Renaming Γ' Γ''} : (rename γ' V).rename γ = V.rename (γ'.map (·.rename γ)) := by
  induction V
    using Val.rec (motive_2 := fun Γ'' A M => ∀ {Γ Γ'}, {γ : Renaming Γ Γ'} → {γ' : Renaming Γ' Γ''} → (M.rename γ').rename γ = M.rename (γ'.map (·.rename γ)))
    generalizing Γ Γ'
    <;> simp [*]

@[simp]
theorem Exp.rename_rename {γ : Renaming Γ Γ'} {γ' : Renaming Γ' Γ''} : (rename γ' M).rename γ = M.rename (γ'.map (·.rename γ)) := by
  induction M
    using Exp.rec (motive_1 := fun Γ'' A V => ∀ {Γ Γ'}, {γ : Renaming Γ Γ'} → {γ' : Renaming Γ' Γ''} → (V.rename γ').rename γ = V.rename (γ'.map (·.rename γ)))
    generalizing Γ Γ'
    <;> simp [*]

@[simp]
def Val.weaken : (V : Val Γ A) → Val (Γ.cons A') A :=
  rename (.map .succ .id)

@[simp]
def Exp.weaken : (M : Exp Γ A) → Exp (Γ.cons A') A :=
  rename (.map .succ .id)

@[simp]
def Exp.weaken₁ : (M : Exp (.cons Γ A') A) → Exp ((Γ.cons A'').cons A') A :=
  rename (.cons (.map (·.succ.succ) .id) .zero)

inductive Subst (Γ : Ctx) : (Γ' : Ctx) → Type
 | nil                                 : Subst Γ .nil
 | cons (γ : Subst Γ Γ') (M : Val Γ A) : Subst Γ (Γ'.cons A)

@[simp]
def Subst.map (f : ∀ {A}, (M : Val Γ A) → Val Γ'' A) : (γ : Subst Γ Γ') → Subst Γ'' Γ'
  | nil      => nil
  | cons γ M => cons (γ.map @f) (f M)

@[simp]
def Subst.weaken (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A) :=
  cons (γ.map .weaken) (.var .zero)

@[simp]
def Subst.ofRenaming (f : ∀ {A}, Var A Γ → Val Γ'' A) : (γ : Renaming Γ Γ') → Subst Γ'' Γ'
  | .nil      => nil
  | .cons γ x => cons (ofRenaming @f γ) (f x)

@[simp]
theorem Subst.ofRenaming_map : ofRenaming f (γ.map g) = ofRenaming (f <| g ·) γ :=
  by induction γ <;> simp [*]

@[simp]
theorem Subst.map_ofRenaming : (ofRenaming g γ).map f = ofRenaming (f <| g ·) γ :=
  by induction γ <;> simp [*]

@[simp]
theorem Subst.map_map : map f (map g γ) = γ.map (f <| g ·) :=
  by induction γ <;> simp [*]

@[simp]
def Var.subst : (γ : Subst Γ Γ') → (x : Var A Γ') → Val Γ A
  | .cons _ M, .zero   => M
  | .cons γ _, .succ x => subst γ x

@[simp]
theorem Var.subst_ofRenaming : subst (.ofRenaming f γ) x = f (x.rename γ) :=
  by induction x <;> cases γ <;> apply_assumption

@[simp]
theorem Var.subst_map : subst (.map f γ) x = f (subst γ x) :=
  by induction x <;> cases γ <;> apply_assumption

@[simp]
theorem Subst.ofRenaming_subst {γ : Subst Γ Γ'} : ofRenaming (f <| Var.subst γ ·) .id = .map f γ :=
  by induction γ <;> simp [*]

set_option linter.unusedVariables false in
@[structural]
mutual

@[simp]
def Val.subst (γ : Subst Γ Γ') : (V : Val Γ' A) → Val Γ A
  | .var x => Var.subst γ x

  | .triv       => .triv
  | .inl  V     => .inl  (V.subst γ)
  | .inr  V     => .inr  (V.subst γ)
  | .pair V₁ V₂ => .pair (V₁.subst γ) (V₂.subst γ)
  | .lam  M     => .lam  (M.subst γ.weaken)
  | .zero       => .zero
  | .succ V     => .succ (V.subst γ)

@[simp]
def Exp.subst (γ : Subst Γ Γ') : (M : Exp Γ' A) → Exp Γ A
  | .ret V    => .ret (V.subst γ)
  | .let M M' => .let (M.subst γ) (M'.subst γ.weaken)

  | .absurd V       => .absurd (V.subst γ)
  | .case   V M₁ M₂ => .case   (V.subst γ) (M₁.subst γ.weaken) (M₂.subst γ.weaken)
  | .fst    V       => .fst    (V.subst γ)
  | .snd    V       => .snd    (V.subst γ)
  | .ap     V V₁    => .ap     (V.subst γ) (V₁.subst γ)
  | .iter   V M₁ M₂ => .iter   (V.subst γ) (M₁.subst γ) (M₂.subst γ.weaken)

  | .print V => .print (V.subst γ)
  | .read    => .read

end

@[simp]
theorem Val.subst_id : subst (.ofRenaming .var .id) V = V := by
  induction V
    using Val.rec (motive_2 := fun Γ A M => M.subst (.ofRenaming .var .id) = M)
    <;> simp_all

@[simp]
theorem Exp.subst_id : subst (.ofRenaming .var .id) M = M := by
  induction M
    using Exp.rec (motive_1 := fun Γ A V => V.subst (.ofRenaming .var .id) = V)
    <;> simp_all

@[simp]
theorem Val.subst_nil : subst .nil V = V :=
  subst_id

@[simp]
theorem Exp.subst_nil : subst .nil M = M :=
  subst_id

@[simp]
theorem Exp.subst_cons_nil_zero : subst (.cons .nil (.var .zero)) M = M :=
  subst_id

@[simp]
theorem Val.subst_rename {γ : Subst Γ Γ'} {γ' : Renaming Γ' Γ''} : (rename γ' V).subst γ = V.subst (.ofRenaming (Var.subst γ) γ') := by
  induction V
    using Val.rec (motive_2 := fun Γ'' A M => ∀ {Γ Γ'}, {γ : Subst Γ Γ'} → {γ' : Renaming Γ' Γ''} → (M.rename γ').subst γ = M.subst (.ofRenaming (Var.subst γ) γ'))
    generalizing Γ Γ'
    <;> simp [*]

@[simp]
theorem Exp.subst_rename {γ : Subst Γ Γ'} {γ' : Renaming Γ' Γ''} : (rename γ' M).subst γ = M.subst (.ofRenaming (Var.subst γ) γ') := by
  induction M
    using Exp.rec (motive_1 := fun Γ'' A V => ∀ {Γ Γ'}, {γ : Subst Γ Γ'} → {γ' : Renaming Γ' Γ''} → (V.rename γ').subst γ = V.subst (.ofRenaming (Var.subst γ) γ'))
    generalizing Γ Γ'
    <;> simp [*]

@[simp]
theorem Val.rename_subst {γ : Renaming Γ Γ'} {γ' : Subst Γ' Γ''} : (subst γ' V).rename γ = V.subst (.map (.rename γ) γ') := by
  induction V
    using Val.rec (motive_2 := fun Γ'' A M => ∀ {Γ Γ'}, {γ : Renaming Γ Γ'} → {γ' : Subst Γ' Γ''} → (M.subst γ').rename γ = M.subst (.map (.rename γ) γ'))
    generalizing Γ Γ'
    <;> simp [*]

@[simp]
theorem Exp.rename_subst {γ : Renaming Γ Γ'} {γ' : Subst Γ' Γ''} : (subst γ' M).rename γ = M.subst (.map (.rename γ) γ') := by
  induction M
    using Exp.rec (motive_1 := fun Γ'' A V => ∀ {Γ Γ'}, {γ : Renaming Γ Γ'} → {γ' : Subst Γ' Γ''} → (V.subst γ').rename γ = V.subst (.map (.rename γ) γ'))
    generalizing Γ Γ'
    <;> simp [*]

@[simp]
def Exp.sub (M : Exp (.cons Γ A') A) (V : Val Γ A') : Exp Γ A :=
  subst (.cons (.ofRenaming .var .id) V) M

def Val.ofNat : (n : Nat) → Val Γ .nat
  | .zero   => zero
  | .succ n => succ (ofNat n)

@[simp]
def Val.toNat : (V : Val .nil .nat) → Nat
  | zero   => .zero
  | succ V => .succ V.toNat

def State (A : Typ) : Type :=
  List Nat × Exp .nil A × List Nat

inductive Steps : (S S' : State A) → Type
  | let₁ (s : Steps (I, M, O) (I', M', O')) : Steps (I, .let M M'',      O) (I', .let M' M'', O')
  | let₂                                    : Steps (I, .let (.ret V) M, O) (I, M.sub V,      O)

  | case_inl  : Steps (I, .case (.inl V) M₁ M₂,  O) (I, M₁.sub V,                O)
  | case_inr  : Steps (I, .case (.inr V) M₁ M₂,  O) (I, M₂.sub V,                O)
  | fst_pair  : Steps (I, .fst (.pair V₁ V₂),    O) (I, .ret V₁,                 O)
  | snd_pair  : Steps (I, .snd (.pair V₁ V₂),    O) (I, .ret V₂,                 O)
  | ap_lam    : Steps (I, .ap (.lam M) V₁,       O) (I, M.sub V₁,                O)
  | iter_zero : Steps (I, .iter .zero M₁ M₂,     O) (I, M₁,                      O)
  | iter_succ : Steps (I, .iter (.succ V) M₁ M₂, O) (I, .let (.iter V M₁ M₂) M₂, O)

  | print : Steps (I,      .print V, O) (I,  .ret .triv,             V.toNat :: O)
  | read₁ : Steps ([],     .read,    O) ([], .ret (.inl .triv),      O)
  | read₂ : Steps (n :: I, .read,    O) (I,  .ret (.inr (.ofNat n)), O)

inductive Final : (S : State A) → Type
  | ret : Final (I, .ret V, O)

instance : Subsingleton (Final S) where
  allEq
    | .ret, .ret => rfl

theorem Final.not_steps : (V : Final S) → (s : Steps S S') → False := nofun

inductive Progress (S : State A)
  | final (r : Final S)
  | steps (s : Steps S S')

instance : Subsingleton (Σ S', Steps S S') where
  allEq := by
    intro ⟨S', s⟩ ⟨S'', s'⟩
    induction s
      <;> rename_i ih
      <;> cases s'
      <;> (try cases ih _ ‹_›)
      <;> (try rfl)
      <;> nomatch Final.not_steps .ret ‹_›

instance : Subsingleton (Progress S) where
  allEq
    | .final r₁, .final r₂ => match Subsingleton.allEq r₁ r₂ with | rfl => rfl
    | .final r₁, .steps s₂ => nomatch r₁.not_steps s₂
    | .steps s₁, .final r₂ => nomatch r₂.not_steps s₁
    | .steps s₁, .steps s₂ => match Subsingleton.allEq (α := Σ _, _) ⟨_, s₁⟩ ⟨_, s₂⟩ with | rfl => rfl

def progress : (S : State A) → Progress S
  | (_, M, _) => progress M
  where progress {A I O} : (M : Exp _ A) → Progress (I, M, O)
    | .ret V    => .final .ret
    | .let M M' => match M, progress M with
                   | _, .steps s    => .steps (.let₁ s)
                   | _, .final .ret => .steps .let₂

    | .case (.inl _) ..  => .steps .case_inl
    | .case (.inr _) ..  => .steps .case_inr
    | .fst  (.pair ..)   => .steps .fst_pair
    | .snd  (.pair ..)   => .steps .snd_pair
    | .ap   (.lam _) _   => .steps .ap_lam
    | .iter .zero ..     => .steps .iter_zero
    | .iter (.succ _) .. => .steps .iter_succ

    | .print _ => .steps .print
    | .read    => match I with
                  | []     => .steps .read₁
                  | _ :: _ => .steps .read₂

inductive Reduces : (S S' : State A) → Type
  | refl                                       : Reduces S S
  | step (s : Steps S S') (r : Reduces S' S'') : Reduces S S''

namespace Reduces

def trans : (r : Reduces S S') → (r' : Reduces S' S'') → Reduces S S''
  | refl,     r' => r'
  | step s r, r' => step s (r.trans r')

def lift {F : (S : State A) → State A'} (f : ∀ {S S'}, (s : Steps S S') → Steps (F S) (F S')) : (r : Reduces S S') → Reduces (F S) (F S')
  | refl     => refl
  | step s r => step (f s) (r.lift @f)

end Reduces

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

  | .print M => .let (translateExp M) (.print (.var .zero))
  | .read    => .read

def translateState : (S : CBV.State A) → Modal.State A
  | (I, M, O) => (I, translateExp M, O)

inductive TranslateSteps (S S' : CBV.State A)
  | mk (r : Modal.Reduces (translateState S) S'') (r' : Modal.Reduces (translateState S') S'')

def translateSteps : (s : CBV.Steps S S') → TranslateSteps S S'
  | .let    s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .absurd s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .inl    s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .inr    s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .case   s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .fst    s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .snd    s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .succ   s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .iter   s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩
  | .print  s => let ⟨r, r'⟩ := translateSteps s; ⟨.lift .let₁ r, .lift .let₁ r'⟩

  | .pair₁    s₁ => sorry
  | .pair₂ V₁ s₂ => sorry
  | .ap₁      s  => sorry
  | .ap₂   V  s₁ => sorry

  | .let'      V     => sorry
  | .case_inl  V     => sorry
  | .case_inr  V     => sorry
  | .fst_pair  V₁ V₂ => sorry
  | .snd_pair  V₁ V₂ => sorry
  | .ap_lam    V₁    => sorry
  | .iter_zero       => sorry
  | .iter_succ V     => sorry

  | .print' V => sorry
  | .read₁    => ⟨.step .read₁ .refl, .step .let₂ .refl⟩
  | .read₂    => sorry

end CBV_to_Modal

namespace CBV_to_Modal'

inductive TranslateExp Γ A
  | val (V : Modal.Val Γ A)
  | exp (M : Modal.Exp Γ A)

@[simp]
def TranslateExp.rename (γ : Modal.Renaming Γ Γ') : (M : TranslateExp Γ' A) → TranslateExp Γ A
  | val V => val (V.rename γ)
  | exp M => exp (M.rename γ)

@[simp]
def TranslateExp.subst (γ : Modal.Subst Γ Γ') : (M : TranslateExp Γ' A) → TranslateExp Γ A
  | val V => val (V.subst γ)
  | exp M => exp (M.subst γ)

@[simp]
def TranslateExp.toExp : (M : TranslateExp Γ A) → Modal.Exp Γ A
  | val V => .ret V
  | exp M => M

@[simp]
def TranslateExp.then
  (val : (V : Modal.Val Γ A) → TranslateExp Γ' A')
  (exp : (M : Modal.Exp Γ A) → Modal.Exp Γ' A')
: (M : TranslateExp Γ A) → TranslateExp Γ' A'
  | .val V => val V
  | .exp M => .exp (exp M)

@[simp]
def TranslateExp.then'
  (val : (V : Modal.Val Γ A) → Modal.Exp Γ' A')
  (exp : (M : Modal.Exp Γ A) → Modal.Exp Γ' A')
: (M : TranslateExp Γ A) → Modal.Exp Γ' A'
  | .val V => val V
  | .exp M => exp M

@[simp]
def translateExp : (M : CBV.Exp Γ A) → TranslateExp Γ A
  | .var x    => .val <| .var x
  | .let M M' => .exp <| .let (translateExp M).toExp (translateExp M').toExp

  | .absurd M       => .exp <| translateExp M |>.then' .absurd (.let · (.absurd (.var .zero)))
  | .triv           => .val .triv
  | .inl    M       => translateExp M |>.then (.val <| .inl ·) (.let · (.ret (.inl (.var .zero))))
  | .inr    M       => translateExp M |>.then (.val <| .inr ·) (.let · (.ret (.inr (.var .zero))))
  | .case   M M₁ M₂ => .exp <| translateExp M |>.then'
                         (.case · (translateExp M₁).toExp (translateExp M₂).toExp)
                         (.let · (.case (.var .zero) (translateExp M₁).toExp.weaken₁ (translateExp M₂).toExp.weaken₁))
  | .pair   M₁ M₂   => translateExp M₁ |>.then
                         (fun V₁ => translateExp M₂ |>.then (.val <| .pair V₁ ·) (.let · (.ret (.pair V₁.weaken (.var .zero)))))
                         (.let · <| translateExp M₂ |>.then'
                           (.ret <| .pair (.var .zero) ·.weaken)
                           (.let ·.weaken (.ret (.pair (.var (.succ .zero)) (.var .zero)))))
  | .fst    M       => .exp <| translateExp M |>.then' .fst (.let · (.fst (.var .zero)))
  | .snd    M       => .exp <| translateExp M |>.then' .snd (.let · (.snd (.var .zero)))
  | .lam    M       => .val <| .lam (translateExp M).toExp
  | .ap     M M₁    => .exp <| translateExp M |>.then'
                         (fun V => translateExp M₁ |>.then' (.ap V ·) (.let · (.ap V.weaken (.var .zero))))
                         (.let · <| translateExp M₁ |>.then'
                           (.ap (.var .zero) ·.weaken)
                           (.let ·.weaken (.ap (.var (.succ .zero)) (.var .zero))))
  | .zero           => .val .zero
  | .succ   M       => translateExp M |>.then (.val <| .succ ·) (.let · (.ret (.succ (.var .zero))))
  | .iter   M M₁ M₂ => .exp <| translateExp M |>.then'
                         (.iter · (translateExp M₁).toExp (translateExp M₂).toExp)
                         (.let · (.iter (.var .zero) (translateExp M₁).toExp.weaken (translateExp M₂).toExp.weaken₁))

  | .print M => .exp <| translateExp M |>.then' .print (.let · (.print (.var .zero)))
  | .read    => .exp .read

@[simp]
def translateVal : (V : @CBV.Val Γ A M) → Modal.Val Γ A
  | .var  x     => .var x
  | .triv       => .triv
  | .inl  V     => .inl  (translateVal V)
  | .inr  V     => .inr  (translateVal V)
  | .pair V₁ V₂ => .pair (translateVal V₁) (translateVal V₂)
  | .lam  M     => .lam  (translateExp M).toExp
  | .zero       => .zero
  | .succ V     => .succ (translateVal V)

theorem translateExpVal (V : CBV.Val M) : translateExp M = .val (translateVal V) :=
  by induction V <;> simp [*]

def ofTranslateVal (isVal : translateExp M = .val V) : CBV.Val M :=
  match M with
  | .var  x     => .var x
  | .triv       => .triv
  | .inl  M     => match h : translateExp M with
                   | .val V => .inl (ofTranslateVal h)
                   | .exp M => by rw [translateExp, h] at isVal; nomatch isVal
  | .inr  M     => match h : translateExp M with
                   | .val V => .inr (ofTranslateVal h)
                   | .exp M => by rw [translateExp, h] at isVal; nomatch isVal
  | .pair M₁ M₂ => match h₁ : translateExp M₁, h₂ : translateExp M₂ with
                   | .val V₁, .val V₂ => .pair (ofTranslateVal h₁) (ofTranslateVal h₂)
                   | .val V₁, .exp M₂ | .exp M₁, _ => by rw [translateExp, h₁, h₂] at isVal; nomatch isVal
  | .lam  M     => .lam M
  | .zero       => .zero
  | .succ M     => match h : translateExp M with
                   | .val V => .succ (ofTranslateVal h)
                   | .exp M => by rw [translateExp, h] at isVal; nomatch isVal

@[simp]
def translateState : (S : CBV.State A) → Modal.State A
  | (I, M, O) => (I, (translateExp M).toExp, O)

@[simp]
def translateSubst : (γ : CBV.Subst Γ Γ') → Modal.Subst Γ Γ'
  | .nil      => .nil
  | .cons γ M => .cons (translateSubst γ) (translateVal M)

@[simp]
theorem translateExp_rename {γ : CBV.Renaming Γ Γ'} : translateExp (M.rename γ) = (translateExp M).rename γ := by
  induction M generalizing Γ
    <;> simp [*]
  repeat all_goals split <;> split at ‹_› <;> cases ‹_› <;> simp
  all_goals simp [CBV.Renaming.map_rename.symm]

@[simp]
theorem translateVal_rename : translateVal (V.rename γ) = (translateVal V).rename γ := by
  induction V
    <;> simp [*]
  case lam M => cases translateExp M <;> rfl

@[simp]
theorem translateSubst_map_weaken : translateSubst (γ.map .weaken) = (translateSubst γ).map (.weaken (A' := A)) := by
  induction γ with
  | nil => rfl
  | cons ih => simp [*]; simp [CBV.Val.weaken]

@[simp]
theorem translateExp_substVar : translateExp (CBV.Var.subst γ x) = .val (Modal.Var.subst (translateSubst γ) x) :=
  by induction x <;> cases γ <;> simp [*, translateExpVal ‹_›]

@[simp]
theorem translateExp_subst {γ : CBV.Subst Γ Γ'} : translateExp (M.subst γ) = (translateExp M).subst (translateSubst γ) := by
  induction M generalizing Γ
    <;> simp [*]
    <;> repeat split <;> split at ‹_› <;> cases ‹_› <;> simp

@[simp]
theorem translateSubst_id (f : ∀ {A}, CBV.Var A Γ → CBV.Var A Γ') : translateSubst (.ofRenaming (.var <| f ·) .id) = .ofRenaming (.var <| f ·) .id :=
  by induction Γ <;> simp [*]

@[simp]
theorem translateExp_sub : (translateExp (M.sub V)).toExp = (translateExp M).toExp.sub (translateVal V) := by
  simp [CBV.Exp.sub, translateSubst_id (·)]
  cases translateExp M <;> rfl

@[simp]
theorem translateExp_ofNat : translateExp (.ofNat n) = .val (.ofNat (Γ := Γ) n) :=
  by induction n <;> simp! [*]

@[simp]
theorem translateVal_toNat : (translateVal V).toNat = V.toNat :=
  match V with
  | .zero   => rfl
  | .succ _ => by simp; exact translateVal_toNat

def translateSteps : (s : CBV.Steps S S') → Modal.Reduces (translateState S) (translateState S')
  | .let    s => .lift .let₁ <| translateSteps s
  | .absurd s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ .refl)
                     . exact .lift .let₁ this
  | .inl    s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ .refl)
                     . exact .lift .let₁ this
  | .inr    s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ .refl)
                     . exact .lift .let₁ this
  | .case   s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                     . exact .lift .let₁ this
  | .fst    s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ .refl)
                     . exact .lift .let₁ this
  | .snd    s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ .refl)
                     . exact .lift .let₁ this
  | .succ   s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ .refl)
                     . exact .lift .let₁ this
  | .iter   s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                     . exact .lift .let₁ this
  | .print  s => by
                   have := translateSteps s
                   dsimp at this ⊢
                   split at this
                   . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                   . split at this
                     . exact .trans (.lift .let₁ this) (.step .let₂ .refl)
                     . exact .lift .let₁ this

  | .pair₁    s₁ => by
                      have := translateSteps s₁
                      dsimp at this ⊢
                      split at this
                      . nomatch flip CBV.Final.not_steps s₁ (ofTranslateVal ‹_›)
                      . split at this
                        . split
                          . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                          . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                        . exact .lift .let₁ this
  | .pair₂ V₁ s₂ => by
                      have := translateSteps s₂
                      simp [translateExpVal V₁] at this ⊢
                      split at this
                      . nomatch flip CBV.Final.not_steps s₂ (ofTranslateVal ‹_›)
                      . split at this
                        . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                        . exact .lift .let₁ this
  | .ap₁      s  => by
                      have := translateSteps s
                      dsimp at this ⊢
                      split at this
                      . nomatch flip CBV.Final.not_steps s (ofTranslateVal ‹_›)
                      . split at this
                        . split
                          . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                          . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                        . exact .lift .let₁ this
  | .ap₂   V  s₁ => by
                      have := translateSteps s₁
                      simp [translateExpVal V] at this ⊢
                      split at this
                      . nomatch flip CBV.Final.not_steps s₁ (ofTranslateVal ‹_›)
                      . split at this
                        . exact .trans (.lift .let₁ this) (.step .let₂ <| by simp; exact .refl)
                        . exact .lift .let₁ this

  | .let'      V     => by
                          simp [translateExpVal V, -TranslateExp.toExp]
                          exact .step .let₂ .refl
  | .case_inl  V     => by
                          simp [translateExpVal V, -TranslateExp.toExp]
                          exact .step .case_inl .refl
  | .case_inr  V     => by
                          simp [translateExpVal V, -TranslateExp.toExp]
                          exact .step .case_inr .refl
  | .fst_pair  V₁ V₂ => by
                          simp [translateExpVal V₁, translateExpVal V₂]
                          exact .step .fst_pair .refl
  | .snd_pair  V₁ V₂ => by
                          simp [translateExpVal V₁, translateExpVal V₂]
                          exact .step .snd_pair .refl
  | .ap_lam    V₁    => by
                          simp [translateExpVal V₁, -TranslateExp.toExp]
                          exact .step .ap_lam .refl
  | .iter_zero       => .step .iter_zero .refl
  | .iter_succ V     => by
                          simp [translateExpVal V]
                          exact .step .iter_succ .refl

  | .print' V => by
                   simp [translateExpVal V]
                   exact .step .print <| by simp; exact .refl
  | .read₁    => .step .read₁ .refl
  | .read₂    => .step .read₂ <| by simp; exact .refl

end CBV_to_Modal'
