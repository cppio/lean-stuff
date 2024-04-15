inductive Typ
  | arr  (τ₁ τ₂ : Typ)
  | unit
  | prod (τ₁ τ₂ : Typ)
  | void
  | sum  (τ₁ τ₂ : Typ)

inductive Exp.Var (τ : Typ) : (Γ : List Typ) → Type
  | head               : Var τ (τ :: Γ)
  | tail (x : Var τ Γ) : Var τ (τ' :: Γ)
  deriving Repr

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
  deriving Repr

mutual

inductive Value : (τ : Typ) → Type
  | lam  (ρ : Subst Γ) (e₂ : Exp (τ₁ :: Γ) τ₂) : Value (.arr τ₁ τ₂)
  | triv                                       : Value .unit
  | pair (v₁ : Value τ₁) (v₂ : Value τ₂)       : Value (.prod τ₁ τ₂)
  | inl  (v : Value τ₁)                        : Value (.sum τ₁ τ₂)
  | inr  (v : Value τ₂)                        : Value (.sum τ₁ τ₂)
  deriving Repr

inductive Subst : (Γ : List Typ) → Type
  | nil                              : Subst []
  | cons (v : Value τ) (ρ : Subst Γ) : Subst (τ :: Γ)

end

def evalVar : (ρ : Subst Γ) → (e : Exp.Var τ Γ) → Value τ
  | .cons v ρ, .head   => v
  | .cons v ρ, .tail x => evalVar ρ x

unsafe
def eval (ρ : Subst Γ) : (e : Exp Γ τ) → Value τ
  | .var x        => evalVar ρ x
  | .lam e₂       => .lam ρ e₂
  | .ap e e₁      => match eval ρ e with
                     | .lam ρ' e₂ => eval (.cons (eval ρ e₁) ρ') e₂
  | .triv         => .triv
  | .pair e₁ e₂   => .pair (eval ρ e₁) (eval ρ e₂)
  | .prl e        => match eval ρ e with
                     | .pair v₁ v₂ => v₁
  | .prr e        => match eval ρ e with
                     | .pair v₁ v₂ => v₂
  | .abort e      => nomatch eval ρ e
  | .inl e        => .inl (eval ρ e)
  | .inr e        => .inr (eval ρ e)
  | .case e e₁ e₂ => match eval ρ e with
                     | .inl v => eval (.cons v ρ) e₁
                     | .inr v => eval (.cons v ρ) e₂
