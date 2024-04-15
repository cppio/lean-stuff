inductive TypCtx
  | nil
  | cons (Δ : TypCtx)

inductive TypVar : (Δ : TypCtx) → Type
  | zero                : TypVar (.cons Δ)
  | succ (X : TypVar Δ) : TypVar (.cons Δ)

inductive Typ : (Δ : TypCtx) → Type
  | var (X : TypVar Δ)   : Typ Δ
  | arr (A₁ A₂ : Typ Δ)  : Typ Δ
  | all (A : Typ Δ.cons) : Typ Δ

inductive Ctx (Δ : TypCtx)
  | nil
  | cons (Γ : Ctx Δ) (A : Typ Δ)

def TypRenaming (Δ Δ' : TypCtx) : Type :=
  (X : TypVar Δ') → TypVar Δ

@[simp]
def TypRenaming.cons (δ : TypRenaming Δ Δ') : TypRenaming Δ.cons Δ'.cons
  | .zero   => .zero
  | .succ X => .succ (δ X)

@[simp]
def TypRenaming.rename (δ : TypRenaming Δ Δ') : (A : Typ Δ') → Typ Δ
  | .var X     => .var (δ X)
  | .arr A₁ A₂ => .arr (δ.rename A₁) (δ.rename A₂)
  | .all A     => .all (δ.cons.rename A)

@[simp]
def TypRenaming.renameCtx (δ : TypRenaming Δ Δ') : (Γ : Ctx Δ') → Ctx Δ
  | .nil      => .nil
  | .cons Γ A => .cons (δ.renameCtx Γ) (δ.rename A)

def Typ.weaken : (A : Typ Δ) → Typ Δ.cons :=
  TypRenaming.rename .succ

def Ctx.weaken : (Γ : Ctx Δ) → Ctx Δ.cons :=
  TypRenaming.renameCtx .succ

def TypSubst (Δ Δ' : TypCtx) : Type :=
  (X : TypVar Δ') → Typ Δ

@[simp]
def TypSubst.cons (δ : TypSubst Δ Δ') : TypSubst Δ.cons Δ'.cons
  | .zero   => .var .zero
  | .succ X => .weaken (δ X)

@[simp]
def TypSubst.subst (δ : TypSubst Δ Δ') : (A : Typ Δ') → Typ Δ
  | .var X     => δ X
  | .arr A₁ A₂ => .arr (δ.subst A₁) (δ.subst A₂)
  | .all A     => .all (δ.cons.subst A)

@[simp]
def TypSubst.substCtx (δ : TypSubst Δ Δ') : (Γ : Ctx Δ') → Ctx Δ
  | .nil      => .nil
  | .cons Γ A => .cons (δ.substCtx Γ) (δ.subst A)

def Typ.subst (A : Typ Δ.cons) (A' : Typ Δ) : Typ Δ :=
  TypSubst.subst (Δ' := Δ.cons) (fun | .zero => A' | .succ X => .var X) A

def Ctx.subst (Γ : Ctx Δ.cons) (A' : Typ Δ) : Ctx Δ :=
  TypSubst.substCtx (Δ' := Δ.cons) (fun | .zero => A' | .succ X => .var X) Γ

@[simp]
theorem TypRenaming.rename_rename (δ : TypRenaming Δ Δ') (δ' : TypRenaming Δ' Δ'') : δ.rename (δ'.rename A) = rename (fun X => δ (δ' X)) A := by
  induction A generalizing Δ Δ'
    <;> simp [*]
    <;> congr
    <;> funext X
    <;> cases X
    <;> simp

@[simp]
theorem TypRenaming.renameCtx_renameCtx (δ : TypRenaming Δ Δ') (δ' : TypRenaming Δ' Δ'') : δ.renameCtx (δ'.renameCtx Γ) = renameCtx (fun X => δ (δ' X)) Γ := by
  induction Γ <;> simp [*]

@[simp]
theorem TypSubst.subst_rename (δ : TypSubst Δ Δ') (δ' : TypRenaming Δ' Δ'') : δ.subst (δ'.rename A) = subst (fun X => δ (δ' X)) A := by
  induction A generalizing Δ Δ'
    <;> simp [*]
    <;> congr
    <;> funext X
    <;> cases X
    <;> simp

@[simp]
theorem TypSubst.substCtx_renameCtx (δ : TypSubst Δ Δ') (δ' : TypRenaming Δ' Δ'') : δ.substCtx (δ'.renameCtx Γ) = substCtx (fun X => δ (δ' X)) Γ := by
  induction Γ <;> simp [*]

@[simp]
theorem TypSubst.rename_subst (δ : TypRenaming Δ Δ') (δ' : TypSubst Δ' Δ'') : δ.rename (δ'.subst A) = subst (fun X => δ.rename (δ' X)) A := by
  induction A generalizing Δ Δ'
    <;> simp [*]
    <;> congr
    <;> funext X
    <;> cases X
    <;> simp [Typ.weaken]

@[simp]
theorem TypSubst.renameCtx_substCtx (δ : TypRenaming Δ Δ') (δ' : TypSubst Δ' Δ'') : δ.renameCtx (δ'.substCtx Γ) = substCtx (fun X => δ.rename (δ' X)) Γ := by
  induction Γ <;> simp [*]

@[simp]
theorem TypSubst.subst_subst (δ : TypSubst Δ Δ') (δ' : TypSubst Δ' Δ'') : δ.subst (δ'.subst A) = subst (fun X => δ.subst (δ' X)) A := by
  induction A generalizing Δ Δ'
    <;> simp [*]
    <;> congr
    <;> funext X
    <;> cases X
    <;> simp [Typ.weaken]

@[simp]
theorem TypSubst.substCtx_substCtx (δ : TypSubst Δ Δ') (δ' : TypSubst Δ' Δ'') : δ.substCtx (δ'.substCtx Γ) = substCtx (fun X => δ.subst (δ' X)) Γ := by
  induction Γ <;> simp [*]

@[simp]
theorem TypSubst.cons_var : cons (Δ := Δ) .var = .var := by
  funext X
  cases X
    <;> simp [Typ.weaken]

@[simp]
theorem TypSubst.subst_var : subst .var A = A := by
  induction A <;> simp [*]

inductive Var Δ (A : Typ Δ) : (Γ : Ctx Δ) → Type
  | zero                 : Var Δ A (.cons Γ A)
  | succ (x : Var Δ A Γ) : Var Δ A (.cons Γ A')

inductive Exp : ∀ Δ, (Γ : Ctx Δ) → (A : Typ Δ) → Type
  | var  (x : Var Δ A Γ)                              : Exp Δ Γ A
  | lam  (M : Exp Δ (Γ.cons A₁) A₂)                   : Exp Δ Γ (.arr A₁ A₂)
  | ap   (M : Exp Δ Γ (.arr A₁ A₂)) (M₁ : Exp Δ Γ A₁) : Exp Δ Γ A₂
  | tlam (M : Exp (.cons Δ) Γ.weaken A)               : Exp Δ Γ (.all A)
  | tap  (M : Exp Δ Γ (.all A)) (A' : Typ Δ)          : Exp Δ Γ (A.subst A')

@[simp]
def TypRenaming.renameVar (δ : TypRenaming Δ Δ') : (x : Var Δ' A Γ) → Var Δ (δ.rename A) (δ.renameCtx Γ)
  | .zero   => .zero
  | .succ x => .succ (δ.renameVar x)

@[simp]
def TypRenaming.renameExp (δ : TypRenaming Δ Δ') : (M : Exp Δ' Γ A) → Exp Δ (δ.renameCtx Γ) (δ.rename A)
  | .var x    => .var (δ.renameVar x)
  | .lam M    => .lam (δ.renameExp M)
  | .ap M M₁  => .ap (δ.renameExp M) (δ.renameExp M₁)
  | .tlam M   => .tlam (cast (by simp [Ctx.weaken]) <| δ.cons.renameExp M)
  | .tap M A' => cast (by simp [Typ.subst]; congr; funext X; cases X <;> simp) <| Exp.tap (δ.renameExp M) (δ.rename A')

def Var.tweaken : (x : Var Δ A Γ) → Var Δ.cons A.weaken Γ.weaken :=
  TypRenaming.renameVar .succ

def Exp.tweaken : (M : Exp Δ Γ A) → Exp Δ.cons Γ.weaken A.weaken :=
  TypRenaming.renameExp .succ

@[simp]
def TypSubst.substVar (δ : TypSubst Δ Δ') : (x : Var Δ' A Γ) → Var Δ (δ.subst A) (δ.substCtx Γ)
  | .zero   => .zero
  | .succ x => .succ (δ.substVar x)

@[simp]
def TypSubst.substExp (δ : TypSubst Δ Δ') : (M : Exp Δ' Γ A) → Exp Δ (δ.substCtx Γ) (δ.subst A)
  | .var x    => .var (δ.substVar x)
  | .lam M    => .lam (δ.substExp M)
  | .ap M M₁  => .ap (δ.substExp M) (δ.substExp M₁)
  | .tlam M   => .tlam (cast (by simp [Ctx.weaken, Typ.weaken]) <| δ.cons.substExp M)
  | .tap M A' => cast (by simp [Typ.subst]; congr; funext X; cases X <;> simp [Typ.weaken]) <| Exp.tap (δ.substExp M) (δ.subst A')

def Var.tsubst (x : Var (.cons Δ) A Γ) (A' : Typ Δ) : Var Δ (A.subst A') (Γ.subst A') :=
  TypSubst.substVar (A := A) (fun | .zero => A' | .succ X => .var X) x

def Exp.tsubst (M : Exp (.cons Δ) Γ A) (A' : Typ Δ) : Exp Δ (Γ.subst A') (A.subst A') :=
  TypSubst.substExp (A := A) (fun | .zero => A' | .succ X => .var X) M

/-
theorem Var.cast (eq : Var Δ A (.cons Γ A) = Var Δ' A' (.cons Γ' A')) : cast eq .zero = .zero := by
  sorry

@[simp]
theorem TypRenaming.renameVar_renameVar (δ : TypRenaming Δ Δ') (δ' : TypRenaming Δ' Δ'') (x : Var Δ'' A Γ) : δ.renameVar (δ'.renameVar x) = cast (congr (congrArg (Var Δ) (by simp)) (by simp)) (renameVar (fun X => δ (δ' X)) x) := by
  induction x <;> simp [*]

@[simp]
theorem TypSubst.substVar_renameVar (δ : TypSubst Δ Δ') (δ' : TypRenaming Δ' Δ'') (x : Var Δ'' A Γ) : δ.substVar (δ'.renameVar x) = cast sorry (substVar (fun X => δ (δ' X)) x) := by
  induction x <;> simp [*]

@[simp]
theorem TypSubst.renameVar_substVar (δ : TypRenaming Δ Δ') (δ' : TypSubst Δ' Δ'') (x : Var Δ'' A Γ) : δ.renameVar (δ'.substVar x) = cast sorry (substVar (fun X => δ.rename (δ' X)) x) := by
  induction x <;> simp [*]

@[simp]
theorem TypSubst.substVar_substVar (δ : TypSubst Δ Δ') (δ' : TypSubst Δ' Δ'') (x : Var Δ'' A Γ) : δ.substVar (δ'.substVar x) = cast sorry (substVar (fun X => δ.subst (δ' X)) x) := by
  induction x <;> simp [*]
-/

def Renaming Δ (Γ Γ' : Ctx Δ) : Type :=
  ∀ {{A}}, (x : Var Δ A Γ') → Var Δ A Γ

@[simp]
def Renaming.cons (γ : Renaming Δ Γ Γ') : Renaming Δ (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .zero
  | _, .succ x => .succ (γ x)

@[simp]
def TypRenaming.renameRenaming (δ : TypRenaming Δ Δ') : ∀ {Γ'}, (γ : Renaming Δ' Γ Γ') → Renaming Δ (δ.renameCtx Γ) (δ.renameCtx Γ')
  | .cons _ _, γ, _, .zero   => δ.renameVar (γ .zero)
  | .cons _ _, γ, _, .succ x => δ.renameRenaming (fun _ x => γ (.succ x)) x

def Renaming.weaken : (γ : Renaming Δ Γ Γ') → Renaming Δ.cons Γ.weaken Γ'.weaken :=
  TypRenaming.renameRenaming .succ

@[simp]
def Renaming.rename (γ : Renaming Δ Γ Γ') : (M : Exp Δ Γ' A) → Exp Δ Γ A
  | .var x    => .var (γ x)
  | .lam M    => .lam (γ.cons.rename M)
  | .ap M M₁  => .ap (γ.rename M) (γ.rename M₁)
  | .tlam M   => .tlam (γ.weaken.rename M)
  | .tap M A' => .tap (γ.rename M) A'

def Exp.weaken : (M : Exp Δ Γ A) → Exp Δ (Γ.cons A') A :=
  Renaming.rename fun _ => .succ

def Subst Δ (Γ Γ' : Ctx Δ) : Type :=
  ∀ {{A}}, (x : Var Δ A Γ') → Exp Δ Γ A

@[simp]
def Subst.cons (γ : Subst Δ Γ Γ') : Subst Δ (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .var .zero
  | _, .succ x => .weaken (γ x)

@[simp]
def TypRenaming.renameSubst (δ : TypRenaming Δ Δ') : ∀ {Γ'}, (γ : Subst Δ' Γ Γ') → Subst Δ (δ.renameCtx Γ) (δ.renameCtx Γ')
  | .cons _ _, γ, _, .zero   => δ.renameExp (γ .zero)
  | .cons _ _, γ, _, .succ x => δ.renameSubst (fun _ x => γ (.succ x)) x

def Subst.weaken : (γ : Subst Δ Γ Γ') → Subst Δ.cons Γ.weaken Γ'.weaken :=
  TypRenaming.renameSubst .succ

@[simp]
def Subst.subst (γ : Subst Δ Γ Γ') : (M : Exp Δ Γ' A) → Exp Δ Γ A
  | .var x    => γ x
  | .lam M    => .lam (γ.cons.subst M)
  | .ap M M₁  => .ap (γ.subst M) (γ.subst M₁)
  | .tlam M   => .tlam (γ.weaken.subst M)
  | .tap M A' => .tap (γ.subst M) A'

def Exp.subst (M : Exp Δ (Γ.cons A') A) (M' : Exp Δ Γ A') : Exp Δ Γ A :=
  Subst.subst (Γ' := Γ.cons A') (fun | _, .zero => M' | _, .succ x => .var x) M

@[simp]
theorem Renaming.rename_rename (γ : Renaming Δ Γ Γ') (γ' : Renaming Δ Γ' Γ'') : γ.rename (γ'.rename M) = rename (fun _ x => γ (γ' x)) M := by
  induction M
    <;> simp [*]
    <;> congr
    <;> funext _ x
  . cases x
      <;> simp
  case tlam ih _ =>
    simp [weaken]
    sorry

@[simp]
theorem Subst.subst_rename (γ : Subst Δ Γ Γ') (γ' : Renaming Δ Γ' Γ'') : γ.subst (γ'.rename M) = subst (fun _ x => γ (γ' x)) M := by
  induction M
    <;> simp [*]
    <;> congr
    <;> funext _ x
  . cases x
      <;> simp
  sorry

@[simp]
theorem Subst.rename_subst (γ : Renaming Δ Γ Γ') (γ' : Subst Δ Γ' Γ'') : γ.rename (γ'.subst M) = subst (fun _ x => γ.rename (γ' x)) M := by
  induction M
    <;> simp [*]
    <;> congr
    <;> funext _ x
  . cases x
      <;> simp
  sorry

@[simp]
theorem Subst.subst_subst (γ : Subst Δ Γ Γ') (γ' : Subst Δ Γ' Γ'') : γ.subst (γ'.subst M) = subst (fun _ x => γ.subst (γ' x)) M := by
  induction M
    <;> simp [*]
    <;> congr
    <;> funext _ x
  . cases x
      <;> simp
  sorry

inductive Steps : (M M' : Exp .nil .nil A) → Type
  | ap  : Steps M M' → Steps (.ap M M₁)  (.ap M' M₁)
  | tap : Steps M M' → Steps (.tap M A') (.tap M' A')

  | ap_lam   : Steps (.ap (.lam M) M₁)   (M.subst M₁)
  | tap_tlam : Steps (.tap (.tlam M) A') (M.tsubst A')

inductive Reduces : (M M' : Exp .nil .nil A) → Type
  | refl : Reduces M M
  | step : Steps M M' → Reduces M' M'' → Reduces M M''

def Reduces.trans : Reduces M M' → Reduces M' M'' → Reduces M M''
  | .refl,     r' => r'
  | .step s r, r' => .step s (r.trans r')

def Reduces.step' (r : Reduces M M') (s : Steps M' M'') : Reduces M M'' :=
  r.trans (.step s .refl)

def Reduces.comp {F : Exp .nil .nil A → Exp .nil .nil B} (f : ∀ {M M'}, Steps M M' → Steps (F M) (F M')) : Reduces M M' → Reduces (F M) (F M')
  | .refl     => .refl
  | .step s r => .step (f s) (r.comp f)

def HT (Δ : TypCtx) (δ : TypSubst .nil Δ) (η : (X : TypVar Δ) → Exp .nil .nil (δ X) → Prop) (η_cand : ∀ X M₁ M₂, Reduces M₁ M₂ → η X M₂ → η X M₁) : (A : Typ Δ) → (M : Exp .nil .nil (δ.subst A)) → Prop
  | .var X,     M => η X M
  | .arr A₁ A₂, M => ∃ M₂, ∃ _ : Reduces M (.lam M₂), ∀ M₁, HT Δ δ η η_cand A₁ M₁ → HT Δ δ η η_cand A₂ (M₂.subst M₁)
  | .all A,     M => ∃ M', ∃ _ : Reduces M (.tlam M'), ∀ A' η_A' η_cand_A', HT Δ.cons (fun | .zero => A' | .succ X => δ X) (fun | .zero => η_A' | .succ X => η X) (fun | .zero => η_cand_A' | .succ X => η_cand X) A (cast (by simp [Ctx.subst, Typ.subst]; congr; funext X; cases X <;> simp [Typ.weaken]) <| M'.tsubst A')

theorem HT.expand : ∀ {A M₁ M₂}, Reduces M₁ M₂ → HT Δ δ η η_cand A M₂ → HT Δ δ η η_cand A M₁
  | .var X,       M₁, M₂, r,  ht           => η_cand X M₁ M₂ r ht
  | .arr _A₁ _A₂, _,  _,  r₁, ⟨M₂, r₂, ht⟩ => ⟨M₂, r₁.trans r₂, ht⟩
  | .all _A,      _,  _,  r₁, ⟨M', r₂, ht⟩ => ⟨M', r₁.trans r₂, ht⟩

def HTSubst (Δ : TypCtx) (δ : TypSubst .nil Δ) (η : (X : TypVar Δ) → Exp .nil .nil (δ X) → Prop) (η_cand : ∀ X M₁ M₂, Reduces M₁ M₂ → η X M₂ → η X M₁) (Γ : Ctx Δ) (γ : Subst .nil .nil (δ.substCtx Γ)) : Prop :=
  ∀ {{A}}, (x : Var Δ A Γ) → HT Δ δ η η_cand A (γ (δ.substVar x))

def HT' (Δ : TypCtx) (Γ : Ctx Δ) (A : Typ Δ) (M : Exp Δ Γ A) : Prop :=
  (δ : TypSubst .nil Δ) → (η : (X : TypVar Δ) → Exp .nil .nil (δ X) → Prop) → (η_cand : ∀ X M₁ M₂, Reduces M₁ M₂ → η X M₂ → η X M₁) → (γ : Subst .nil .nil (δ.substCtx Γ)) → HTSubst Δ δ η η_cand Γ γ → HT Δ δ η η_cand A (γ.subst (δ.substExp M))

theorem ftlr : ∀ M, HT' Δ Γ A M
  | .var x,    δ, η, η_cand, γ, ht_γ => ht_γ x
  | .lam M,    δ, η, η_cand, γ, ht_γ => ⟨γ.cons.subst (δ.substExp M), .refl, fun M₁ ht_M₁ => cast (by congr 1; simp [Exp.subst]; sorry) <| ftlr M δ η η_cand (fun | _, .zero => M₁ | _, .succ x => γ x) (fun | _, .zero => ht_M₁ | _, .succ x => ht_γ x)⟩
  | .ap M M₁,  δ, η, η_cand, γ, ht_γ => match ftlr M δ η η_cand γ ht_γ with
                                        | ⟨_, r, ht_M₂⟩ => .expand (.step' (.comp (M := γ.subst (δ.substExp M)) .ap r) .ap_lam) <| ht_M₂ (γ.subst (δ.substExp M₁)) (ftlr M₁ δ η η_cand γ ht_γ)
  | .tlam M,   δ, η, η_cand, γ, ht_γ => ⟨γ.weaken.subst (cast _ <| δ.cons.substExp M), .refl, fun A' η_A' η_cand_A' => sorry⟩
  | .tap M A', δ, η, η_cand, γ, ht_γ => match ftlr M δ η η_cand γ ht_γ with
                                        | ⟨_, r, ht_M'⟩ => cast (by dsimp; sorry) <| ht_M' (δ.subst A') (HT Δ δ η η_cand A') fun _ _ => HT.expand
