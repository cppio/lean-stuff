inductive Typ
  | arr  (τ₁ τ₂ : Typ)
  | unit
  | prod (τ₁ τ₂ : Typ)
  | void
  | sum  (τ₁ τ₂ : Typ)

/-
inductive Exp''
  | var   (x : Nat)
  | lam   (e₂ : Exp'')
  | ap    (e e₁ : Exp'')
  | triv
  | pair  (e₁ e₂ : Exp'')
  | prl   (e : Exp'')
  | prr   (e : Exp'')
  | abort (e : Exp'')
  | inl   (e : Exp'')
  | inr   (e : Exp'')
  | case  (e e₁ e₂ : Exp'')

inductive Exp''.HasType.Var (τ : Typ) : (Γ : List Typ) → (x : Nat) → Type
  | head : Var τ (τ :: Γ) .zero
  | tail : Var τ Γ n → Var τ (τ' :: Γ) n.succ

inductive Exp''.HasType : (Γ : List Typ) → (e : Exp'') → (τ : Typ) → Type
  | var   : HasType.Var τ Γ x → HasType Γ (var x) τ
  | lam   : HasType (τ₁ :: Γ) e₂ τ₂ → HasType Γ (lam e₂) (.arr τ₁ τ₂)
  | ap    : HasType Γ e (.arr τ₁ τ₂) → HasType Γ e₁ τ₁ → HasType Γ (ap e e₁) τ₂
  | triv  : HasType Γ triv .unit
  | pair  : HasType Γ e₁ τ₁ → HasType Γ e₂ τ₂ → HasType Γ (pair e₁ e₂) (.prod τ₁ τ₂)
  | prl   : HasType Γ e (.prod τ₁ τ₂) → HasType Γ (prl e) τ₁
  | prr   : HasType Γ e (.prod τ₁ τ₂) → HasType Γ (prr e) τ₂
  | abort : HasType Γ e .void → HasType Γ (abort e) τ
  | inl   : HasType Γ e τ₁ → HasType Γ (inl e) (.sum τ₁ τ₂)
  | inr   : HasType Γ e τ₂ → HasType Γ (inr e) (.sum τ₁ τ₂)
  | case  : HasType Γ e (.sum τ₁ τ₂) → HasType (τ₁ :: Γ) e₁ τ → HasType (τ₂ :: Γ) e₂ τ → HasType Γ (case e e₁ e₂) τ

inductive Exp' : (τ : Typ) → Type
  | var   (x : Nat)                                             : Exp' τ
  | lam   (e₂ : Exp'  τ₂)                                       : Exp' (.arr τ₁ τ₂)
  | ap    (e : Exp' (.arr τ₁ τ₂)) (e₁ : Exp' τ₁)                : Exp' τ₂
  | triv                                                        : Exp' .unit
  | pair  (e₁ : Exp' τ₁) (e₂ : Exp' τ₂)                         : Exp' (.prod τ₁ τ₂)
  | prl   (e : Exp' (.prod τ₁ τ₂))                              : Exp' τ₁
  | prr   (e : Exp' (.prod τ₁ τ₂))                              : Exp' τ₂
  | abort (e : Exp' .void)                                      : Exp' τ
  | inl   (e : Exp' τ₁)                                         : Exp' (.sum τ₁ τ₂)
  | inr   (e : Exp' τ₂)                                         : Exp' (.sum τ₁ τ₂)
  | case  (e : Exp' (.sum τ₁ τ₂)) (e₁ : Exp'  τ) (e₂ : Exp'  τ) : Exp' τ

inductive Exp'.HasType : (Γ : List Typ) → (e : Exp' τ) → Type
  | var   : Exp''.HasType.Var τ Γ x → HasType Γ (var (τ := τ) x)
  | lam   : HasType (τ₁ :: Γ) e₂ → HasType Γ (lam (τ₁ := τ₁) e₂)
  | ap    : HasType Γ e → HasType Γ e₁ → HasType Γ (ap e e₁)
  | triv  : HasType Γ triv
  | pair  : HasType Γ e₁ → HasType Γ e₂ → HasType Γ (pair e₁ e₂)
  | prl   : HasType Γ e → HasType Γ (prl e)
  | prr   : HasType Γ e → HasType Γ (prr e)
  | abort : HasType Γ e → HasType Γ (abort e)
  | inl   : HasType Γ e → HasType Γ (inl e)
  | inr   : HasType Γ e → HasType Γ (inr e)
  | case  : HasType (τ := .sum τ₁ τ₂) Γ e → HasType (τ₁ :: Γ) e₁ → HasType (τ₂ :: Γ) e₂ → HasType Γ (case e e₁ e₂)
-/

inductive Exp.Var (τ : Typ) : (Γ : List Typ) → Type
  | head               : Var τ (τ :: Γ)
  | tail (x : Var τ Γ) : Var τ (τ' :: Γ)

inductive Exp : (Γ : List Typ) → (τ : Typ) → Type
  | var   (x : Exp.Var τ Γ)                                                      : Exp Γ τ
  | lam   (e₂ : Exp (τ₁ :: Γ) τ₂)                                                : Exp Γ (.arr τ₁ τ₂)
  | ap    (e : Exp Γ (.arr τ₁ τ₂)) (e₁ : Exp Γ τ₁)                               : Exp Γ τ₂
  | triv                                                                         : Exp Γ .unit
  | pair  (e₁ : Exp Γ τ₁) (e₂ : Exp Γ τ₂)                                        : Exp Γ (.prod τ₁ τ₂)
  | prl   (e : Exp Γ (.prod τ₁ τ₂))                                              : Exp Γ τ₁
  | prr   (e : Exp Γ (.prod τ₁ τ₂))                                              : Exp Γ τ₂
  | abort (e : Exp Γ .void)                                                      : Exp Γ τ
  | inl   (e : Exp Γ τ₁)                                                         : Exp Γ (.sum τ₁ τ₂)
  | inr   (e : Exp Γ τ₂)                                                         : Exp Γ (.sum τ₁ τ₂)
  | case  (e : Exp Γ (.sum τ₁ τ₂)) (e₁ : Exp (τ₁ :: Γ) τ) (e₂ : Exp (τ₂ :: Γ) τ) : Exp Γ τ

namespace Exp

@[simp]
def Var.cast : ∀ {Γ'} (eq : Γ = Γ') (x : Var τ Γ), Var τ Γ'
  | _ :: _, eq, head   => (List.cons.inj eq).left ▸ head
  | _ :: _, eq, tail x => tail (x.cast (List.cons.inj eq).right)

@[simp]
def cast (eq : Γ = Γ') : (e : Exp Γ τ) → Exp Γ' τ
  | var x        => var (x.cast eq)
  | lam e₂       => lam (e₂.cast (eq ▸ rfl))
  | ap e e₁      => ap (e.cast eq) (e₁.cast eq)
  | triv         => triv
  | pair e₁ e₂   => pair (e₁.cast eq) (e₂.cast eq)
  | prl e        => prl (e.cast eq)
  | prr e        => prr (e.cast eq)
  | abort e      => abort (e.cast eq)
  | inl e        => inl (e.cast eq)
  | inr e        => inr (e.cast eq)
  | case e e₁ e₂ => case (e.cast eq) (e₁.cast (eq ▸ rfl)) (e₂.cast (eq ▸ rfl))

@[simp] theorem Var.cast_rfl : cast rfl x = x := by induction x <;> simp [*]
@[simp] theorem cast_rfl : cast rfl e = e := by induction e <;> simp [*]

@[simp]
def Var.weaken : ∀ {Γ₁} (x : Var τ (Γ₁ ++ Γ₂)), Var τ (Γ₁ ++ τ' :: Γ₂)
  | [],     x      => tail x
  | _ :: _, head   => head
  | _ :: _, tail x => tail x.weaken

@[simp]
def weaken : (e : Exp (Γ₁ ++ Γ₂) τ) → Exp (Γ₁ ++ τ' :: Γ₂) τ
  | var x        => var x.weaken
  | lam e₂       => lam (e₂.weaken (Γ₁ := _ :: _))
  | ap e e₁      => ap e.weaken e₁.weaken
  | triv         => triv
  | pair e₁ e₂   => pair e₁.weaken e₂.weaken
  | prl e        => prl e.weaken
  | prr e        => prr e.weaken
  | abort e      => abort e.weaken
  | inl e        => inl e.weaken
  | inr e        => inr e.weaken
  | case e e₁ e₂ => case e.weaken (e₁.weaken (Γ₁ := _ :: _)) (e₂.weaken (Γ₁ := _ :: _))

@[simp]
def weaken₀ : (e : Exp Γ τ) → Exp (τ' :: Γ) τ := weaken (Γ₁ := [])

@[simp]
def Var.subst : ∀ {Γ₁ τ'} (x : Var τ (Γ₁ ++ τ' :: Γ₂)), Var τ (Γ₁ ++ Γ₂) ⊕' τ = τ'
  | [],     _, head   => .inr rfl
  | [],     _, tail x => .inl x
  | _ :: _, _, head   => .inl head
  | _ :: _, _, tail x => match subst x with
                         | .inl x  => .inl x.tail
                         | .inr eq => .inr eq

@[simp]
def subst (e' : Exp (Γ₁ ++ Γ₂) τ') : (e : Exp (Γ₁ ++ τ' :: Γ₂) τ) → Exp (Γ₁ ++ Γ₂) τ
  | var x        => match x.subst with
                    | .inl x   => var x
                    | .inr rfl => e'
  | lam e₂       => lam (subst (Γ₁ := _ :: _) e'.weaken₀ e₂)
  | ap e e₁      => ap (subst e' e) (subst e' e₁)
  | triv         => triv
  | pair e₁ e₂   => pair (subst e' e₁) (subst e' e₂)
  | prl e        => prl (subst e' e)
  | prr e        => prr (subst e' e)
  | abort e      => abort (subst e' e)
  | inl e        => inl (subst e' e)
  | inr e        => inr (subst e' e)
  | case e e₁ e₂ => case (subst e' e) (subst (Γ₁ := _ :: _) e'.weaken₀ e₁) (subst (Γ₁ := _ :: _) e'.weaken₀ e₂)

@[simp]
def subst₀ : (e' : Exp Γ τ') → (e : Exp (τ' :: Γ) τ) → Exp Γ τ := subst (Γ₁ := [])

theorem weaken_weaken_var_L₁₁ : ∀ {Γ₁ Γ Γ₂} (x : Var τ (Γ₁ ++ Γ ++ Γ₂)), (Var.cast (List.append_assoc Γ₁ (τ' :: Γ) (τ'' :: Γ₂)) <| @Var.weaken τ Γ₂ τ'' (Γ₁ ++ τ' :: Γ) <| Var.cast (List.append_assoc Γ₁ (τ' :: Γ) Γ₂).symm <| @Var.weaken τ (Γ ++ Γ₂) τ' Γ₁ <| Var.cast (List.append_assoc Γ₁ Γ Γ₂) x) = (@Var.weaken τ (Γ ++ τ'' :: Γ₂) τ' Γ₁ <| Var.cast (List.append_assoc Γ₁ Γ (τ'' :: Γ₂)) <| @Var.weaken τ Γ₂ τ'' (Γ₁ ++ Γ) x)
  | _ :: _, _,      _, .head   => by simp
  | _ :: _, _,      _, .tail x => by simp; exact weaken_weaken_var_L₁₁ x
  | [],     _ :: _, _, _       => by simp
  | [],     [],     _, _       => by simp

/-
theorem weaken_weaken_L₁₁ : (e : Exp (Γ₁ ++ Γ ++ Γ₂) τ) → (cast (List.append_assoc Γ₁ (τ' :: Γ) (τ'' :: Γ₂)) <| @weaken (Γ₁ ++ τ' :: Γ) Γ₂ τ τ'' <| cast (List.append_assoc Γ₁ (τ' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ' <| cast (List.append_assoc Γ₁ Γ Γ₂) e) = (@weaken Γ₁ (Γ ++ τ'' :: Γ₂) τ τ' <| cast (List.append_assoc Γ₁ Γ (τ'' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ'' e)
  | var x        => by simp; exact weaken_weaken_var_L₁₁ x
  | lam e₂       => by simp; exact weaken_weaken_L₁₁ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_L₁₁ e, weaken_weaken_L₁₁ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_L₁₁ e₁, weaken_weaken_L₁₁ e₂⟩
  | prl e        => by simp; exact weaken_weaken_L₁₁ e
  | prr e        => by simp; exact weaken_weaken_L₁₁ e
  | abort e      => by simp; exact weaken_weaken_L₁₁ e
  | inl e        => by simp; exact weaken_weaken_L₁₁ e
  | inr e        => by simp; exact weaken_weaken_L₁₁ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_L₁₁ e, weaken_weaken_L₁₁ (Γ₁ := _ :: _) e₁, weaken_weaken_L₁₁ (Γ₁ := _ :: _) e₂⟩

theorem weaken_weaken_L₁₂ : (e : Exp (Γ₁ ++ (Γ ++ Γ₂)) τ) → (cast (List.append_assoc Γ₁ (τ' :: Γ) (τ'' :: Γ₂)) <| @weaken (Γ₁ ++ τ' :: Γ) Γ₂ τ τ'' <| cast (List.append_assoc Γ₁ (τ' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ' e) = (@weaken Γ₁ (Γ ++ τ'' :: Γ₂) τ τ' <| cast (List.append_assoc Γ₁ Γ (τ'' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ'' <| cast (List.append_assoc Γ₁ Γ Γ₂).symm e)
  | var x        => sorry
  | lam e₂       => by simp; exact weaken_weaken_L₁₂ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_L₁₂ e, weaken_weaken_L₁₂ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_L₁₂ e₁, weaken_weaken_L₁₂ e₂⟩
  | prl e        => by simp; exact weaken_weaken_L₁₂ e
  | prr e        => by simp; exact weaken_weaken_L₁₂ e
  | abort e      => by simp; exact weaken_weaken_L₁₂ e
  | inl e        => by simp; exact weaken_weaken_L₁₂ e
  | inr e        => by simp; exact weaken_weaken_L₁₂ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_L₁₂ e, weaken_weaken_L₁₂ (Γ₁ := _ :: _) e₁, weaken_weaken_L₁₂ (Γ₁ := _ :: _) e₂⟩

theorem weaken_weaken_L₂₁ : (e : Exp (Γ₁ ++ Γ ++ Γ₂) τ) → (@weaken (Γ₁ ++ τ' :: Γ) Γ₂ τ τ'' <| cast (List.append_assoc Γ₁ (τ' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ' <| cast (List.append_assoc Γ₁ Γ Γ₂) e) = (cast (List.append_assoc Γ₁ (τ' :: Γ) (τ'' :: Γ₂)).symm <| @weaken Γ₁ (Γ ++ τ'' :: Γ₂) τ τ' <| cast (List.append_assoc Γ₁ Γ (τ'' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ'' e)
  | var x        => sorry
  | lam e₂       => by simp; exact weaken_weaken_L₂₁ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_L₂₁ e, weaken_weaken_L₂₁ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_L₂₁ e₁, weaken_weaken_L₂₁ e₂⟩
  | prl e        => by simp; exact weaken_weaken_L₂₁ e
  | prr e        => by simp; exact weaken_weaken_L₂₁ e
  | abort e      => by simp; exact weaken_weaken_L₂₁ e
  | inl e        => by simp; exact weaken_weaken_L₂₁ e
  | inr e        => by simp; exact weaken_weaken_L₂₁ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_L₂₁ e, weaken_weaken_L₂₁ (Γ₁ := _ :: _) e₁, weaken_weaken_L₂₁ (Γ₁ := _ :: _) e₂⟩

theorem weaken_weaken_L₂₂ : (e : Exp (Γ₁ ++ (Γ ++ Γ₂)) τ) → (@weaken (Γ₁ ++ τ' :: Γ) Γ₂ τ τ'' <| cast (List.append_assoc Γ₁ (τ' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ' e) = (cast (List.append_assoc Γ₁ (τ' :: Γ) (τ'' :: Γ₂)).symm <| @weaken Γ₁ (Γ ++ τ'' :: Γ₂) τ τ' <| cast (List.append_assoc Γ₁ Γ (τ'' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ'' <| cast (List.append_assoc Γ₁ Γ Γ₂).symm e)
  | var x        => sorry
  | lam e₂       => by simp; exact weaken_weaken_L₂₂ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_L₂₂ e, weaken_weaken_L₂₂ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_L₂₂ e₁, weaken_weaken_L₂₂ e₂⟩
  | prl e        => by simp; exact weaken_weaken_L₂₂ e
  | prr e        => by simp; exact weaken_weaken_L₂₂ e
  | abort e      => by simp; exact weaken_weaken_L₂₂ e
  | inl e        => by simp; exact weaken_weaken_L₂₂ e
  | inr e        => by simp; exact weaken_weaken_L₂₂ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_L₂₂ e, weaken_weaken_L₂₂ (Γ₁ := _ :: _) e₁, weaken_weaken_L₂₂ (Γ₁ := _ :: _) e₂⟩

theorem weaken_weaken_R₁₁ : (e : Exp (Γ₁ ++ Γ ++ Γ₂) τ) → (cast (List.append_assoc Γ₁ (τ'' :: Γ) (τ' :: Γ₂)).symm <| @weaken Γ₁ (Γ ++ τ' :: Γ₂) τ τ'' <| cast (List.append_assoc Γ₁ Γ (τ' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ' e) = (@weaken (Γ₁ ++ τ'' :: Γ) Γ₂ τ τ' <| cast (List.append_assoc Γ₁ (τ'' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ'' <| cast (List.append_assoc Γ₁ Γ Γ₂) e)
  | var x        => sorry
  | lam e₂       => by simp; exact weaken_weaken_R₁₁ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_R₁₁ e, weaken_weaken_R₁₁ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_R₁₁ e₁, weaken_weaken_R₁₁ e₂⟩
  | prl e        => by simp; exact weaken_weaken_R₁₁ e
  | prr e        => by simp; exact weaken_weaken_R₁₁ e
  | abort e      => by simp; exact weaken_weaken_R₁₁ e
  | inl e        => by simp; exact weaken_weaken_R₁₁ e
  | inr e        => by simp; exact weaken_weaken_R₁₁ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_R₁₁ e, weaken_weaken_R₁₁ (Γ₁ := _ :: _) e₁, weaken_weaken_R₁₁ (Γ₁ := _ :: _) e₂⟩

theorem weaken_weaken_R₁₂ : (e : Exp (Γ₁ ++ (Γ ++ Γ₂)) τ) → (cast (List.append_assoc Γ₁ (τ'' :: Γ) (τ' :: Γ₂)).symm <| @weaken Γ₁ (Γ ++ τ' :: Γ₂) τ τ'' <| cast (List.append_assoc Γ₁ Γ (τ' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ' <| cast (List.append_assoc Γ₁ Γ Γ₂).symm e) = (@weaken (Γ₁ ++ τ'' :: Γ) Γ₂ τ τ' <| cast (List.append_assoc Γ₁ (τ'' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ'' e)
  | var x        => sorry
  | lam e₂       => by simp; exact weaken_weaken_R₁₂ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_R₁₂ e, weaken_weaken_R₁₂ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_R₁₂ e₁, weaken_weaken_R₁₂ e₂⟩
  | prl e        => by simp; exact weaken_weaken_R₁₂ e
  | prr e        => by simp; exact weaken_weaken_R₁₂ e
  | abort e      => by simp; exact weaken_weaken_R₁₂ e
  | inl e        => by simp; exact weaken_weaken_R₁₂ e
  | inr e        => by simp; exact weaken_weaken_R₁₂ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_R₁₂ e, weaken_weaken_R₁₂ (Γ₁ := _ :: _) e₁, weaken_weaken_R₁₂ (Γ₁ := _ :: _) e₂⟩

theorem weaken_weaken_R₂₁ : (e : Exp (Γ₁ ++ Γ ++ Γ₂) τ) → (@weaken Γ₁ (Γ ++ τ' :: Γ₂) τ τ'' <| cast (List.append_assoc Γ₁ Γ (τ' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ' e) = (cast (List.append_assoc Γ₁ (τ'' :: Γ) (τ' :: Γ₂)) <| @weaken (Γ₁ ++ τ'' :: Γ) Γ₂ τ τ' <| cast (List.append_assoc Γ₁ (τ'' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ'' <| cast (List.append_assoc Γ₁ Γ Γ₂) e)
  | var x        => sorry
  | lam e₂       => by simp; exact weaken_weaken_R₂₁ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_R₂₁ e, weaken_weaken_R₂₁ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_R₂₁ e₁, weaken_weaken_R₂₁ e₂⟩
  | prl e        => by simp; exact weaken_weaken_R₂₁ e
  | prr e        => by simp; exact weaken_weaken_R₂₁ e
  | abort e      => by simp; exact weaken_weaken_R₂₁ e
  | inl e        => by simp; exact weaken_weaken_R₂₁ e
  | inr e        => by simp; exact weaken_weaken_R₂₁ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_R₂₁ e, weaken_weaken_R₂₁ (Γ₁ := _ :: _) e₁, weaken_weaken_R₂₁ (Γ₁ := _ :: _) e₂⟩

theorem weaken_weaken_R₂₂ : (e : Exp (Γ₁ ++ (Γ ++ Γ₂)) τ) → (@weaken Γ₁ (Γ ++ τ' :: Γ₂) τ τ'' <| cast (List.append_assoc Γ₁ Γ (τ' :: Γ₂)) <| @weaken (Γ₁ ++ Γ) Γ₂ τ τ' <| cast (List.append_assoc Γ₁ Γ Γ₂).symm e) = (cast (List.append_assoc Γ₁ (τ'' :: Γ) (τ' :: Γ₂)) <| @weaken (Γ₁ ++ τ'' :: Γ) Γ₂ τ τ' <| cast (List.append_assoc Γ₁ (τ'' :: Γ) Γ₂).symm <| @weaken Γ₁ (Γ ++ Γ₂) τ τ'' e)
  | var x        => sorry
  | lam e₂       => by simp; exact weaken_weaken_R₂₂ (Γ₁ := _ :: _) e₂
  | ap e e₁      => by simp; exact ⟨weaken_weaken_R₂₂ e, weaken_weaken_R₂₂ e₁⟩
  | triv         => by simp
  | pair e₁ e₂   => by simp; exact ⟨weaken_weaken_R₂₂ e₁, weaken_weaken_R₂₂ e₂⟩
  | prl e        => by simp; exact weaken_weaken_R₂₂ e
  | prr e        => by simp; exact weaken_weaken_R₂₂ e
  | abort e      => by simp; exact weaken_weaken_R₂₂ e
  | inl e        => by simp; exact weaken_weaken_R₂₂ e
  | inr e        => by simp; exact weaken_weaken_R₂₂ e
  | case e e₁ e₂ => by simp; exact ⟨weaken_weaken_R₂₂ e, weaken_weaken_R₂₂ (Γ₁ := _ :: _) e₁, weaken_weaken_R₂₂ (Γ₁ := _ :: _) e₂⟩
-/

/-

-- TODO: arg names
inductive Eq : Exp Γ τ → Exp Γ τ → Prop
  -- equivalence
  | refl : Eq e e
  | sym : Eq e e' → Eq e' e
  | trans : Eq e e' → Eq e' e'' → Eq e e''
  -- congruence
  | lam : Eq e₂ e₂' → Eq (lam e₂) (lam e₂')
  | ap : Eq e e' → Eq e₁ e₁' → Eq (ap e e₁) (ap e' e₁')
  | triv : Eq triv triv
  | pair : Eq e₁ e₁' → Eq e₂ e₂' → Eq (pair e₁ e₂) (pair e₁' e₂')
  | prl : Eq e e' → Eq (prl e) (prl e')
  | prr : Eq e e' → Eq (prr e) (prr e')
  | abort : Eq e e' → Eq (abort e) (abort e')
  | inl : Eq e e' → Eq (inl e) (inl e')
  | inr : Eq e e' → Eq (inr e) (inr e')
  | case : Eq e e' → Eq e₁ e₁' → Eq e₂ e₂' → Eq (case e e₁ e₂) (case e' e₁' e₂')
  -- beta
  | ap_lam : Eq (ap (lam e₂) e₁) (e₁.subst₀ e₂)
  | prl_pair : Eq (prl (pair e₁ e₂)) e₁
  | prr_pair : Eq (prr (pair e₁ e₂)) e₂
  | case_inl : Eq (case (inl e) e₁ e₂) (e.subst₀ e₁)
  | case_inr : Eq (case (inr e) e₁ e₂) (e.subst₀ e₂)
  -- eta
  | arr : Eq e (lam (ap e.weaken₀ (var head)))
  | unit : Eq e triv
  | prod : Eq e (pair (prl e) (prr e))
  | void : Eq (e'.subst₀ e) (abort e')
  | sum : Eq (e'.subst₀ e) (case e' ((inl (var head)).subst (Γ₁ := _ :: []) e.weaken₀) ((inr (var head)).subst₀ (e.weaken (Γ₁ := _ :: [])))) -- TODO

def InterpTyp : (τ : Typ) → Type
  | arr τ₁ τ₂  => InterpTyp τ₁ → InterpTyp τ₂
  | unit       => Unit
  | prod τ₁ τ₂ => InterpTyp τ₁ × InterpTyp τ₂
  | void       => Empty
  | sum τ₁ τ₂  => InterpTyp τ₁ ⊕ InterpTyp τ₂

def InterpCtx : (Γ : List Typ) → Type
  | []     => Unit
  | τ :: Γ => InterpTyp τ × InterpCtx Γ

def InterpVar : (m : Var τ Γ) → (ρ : InterpCtx Γ) → InterpTyp τ
  | head,   (x, ρ) => x
  | tail m, (x, ρ) => InterpVar m ρ

def InterpExp : (e : Exp Γ τ) → (ρ : InterpCtx Γ) → InterpTyp τ
  | var m,        ρ => InterpVar m ρ
  | lam e₂,       ρ => λ x => InterpExp e₂ (x, ρ)
  | ap e e₁,      ρ => InterpExp e ρ (InterpExp e₁ ρ)
  | triv,         ρ => ()
  | pair e₁ e₂,   ρ => (InterpExp e₁ ρ, InterpExp e₂ ρ)
  | prl e,        ρ => InterpExp e ρ |>.fst
  | prr e,        ρ => InterpExp e ρ |>.snd
  | abort e,      ρ => nomatch InterpExp e ρ
  | inl e,        ρ => .inl (InterpExp e ρ)
  | inr e,        ρ => .inr (InterpExp e ρ)
  | case e e₁ e₂, ρ => match InterpExp e ρ with
                       | .inl x₁ => InterpExp e₁ (x₁, ρ)
                       | .inr x₂ => InterpExp e₂ (x₂, ρ)
-/

/-
def LiftableExp (Γ : List Typ) (τ : Typ) : Type :=
  ∀ Γ', Exp (.reverseAux Γ' Γ) τ

def LiftableExp.lift (e : LiftableExp Γ τ) : LiftableExp (τ' :: Γ) τ
  | Γ' => e (τ' :: Γ')

def LiftableExp.var (m : Exp.Var τ Γ) : LiftableExp Γ τ
  | []      => .var m
  | _ :: Γ' => var m.tail Γ'

def LiftCtx (Γ Γ' : List Typ) : Type :=
  ∀ {τ} (m : Exp.Var τ Γ), LiftableExp Γ' τ

def LiftCtx.lift (ρ : LiftCtx Γ Γ') : LiftCtx (τ :: Γ) (τ :: Γ')
  | _, .head   => LiftableExp.var .head
  | _, .tail m => (ρ m).lift

def Exp.substAll (ρ : LiftCtx Γ Γ') : (e : Exp Γ τ) → Exp Γ' τ
  | var m        => ρ m []
  | lam e₂       => lam (e₂.substAll ρ.lift)
  | ap e e₁      => ap (e.substAll ρ) (e₁.substAll ρ)
  | triv         => triv
  | pair e₁ e₂   => pair (e₁.substAll ρ) (e₂.substAll ρ)
  | prl e        => prl (e.substAll ρ)
  | prr e        => prr (e.substAll ρ)
  | abort e      => abort (e.substAll ρ)
  | inl e        => inl (e.substAll ρ)
  | inr e        => inr (e.substAll ρ)
  | case e e₁ e₂ => case (e.substAll ρ) (e₁.substAll ρ.lift) (e₂.substAll ρ.lift)

def Exp.weaken.ctx : ∀ {Γ₁}, LiftCtx (Γ₁ ++ Γ₂) (Γ₁ ++ τ' :: Γ₂)
  | [],     _, m       => LiftableExp.var m.tail
  | _ :: _, _, .head   => LiftableExp.var .head
  | _ :: _, _, .tail m => (ctx m).lift

def Exp.weaken : (e : Exp (Γ₁ ++ Γ₂) τ) → Exp (Γ₁ ++ τ' :: Γ₂) τ :=
  substAll weaken.ctx
-/
