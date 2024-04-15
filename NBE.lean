import Std.Data.Fin.Basic

inductive Exp : ∀ ℓ, Type
  | var (i : Fin ℓ)       : Exp ℓ
  | lam (e₂ : Exp ℓ.succ) : Exp ℓ
  | ap (e e₁ : Exp ℓ)     : Exp ℓ

instance : Inhabited (Exp ℓ) := ⟨.lam (.var 0)⟩

mutual

inductive Neut : ∀ ℓ, Type
  | var (i : Fin ℓ)               : Neut ℓ
  | ap (e : Neut ℓ) (e₁ : Norm ℓ) : Neut ℓ

inductive Norm : ∀ ℓ, Type
  | neut (e : Neut ℓ)      : Norm ℓ
  | lam (e₂ : Norm ℓ.succ) : Norm ℓ

end

instance : Inhabited (Neut (.succ ℓ)) := ⟨.var 0⟩
instance : Inhabited (Norm ℓ) := ⟨.lam (.neut default)⟩

inductive Vec (α : Type u) : (n : Nat) → Type u
  | nil                              : Vec α .zero
  | cons (head : α) (tail : Vec α n) : Vec α n.succ

def Vec.get : (xs : Vec α n) → (i : Fin n) → α
  | cons head _, ⟨.zero, _⟩      => head
  | cons _ tail, ⟨.succ i, isLt⟩ => tail.get ⟨i, Nat.lt_of_succ_lt_succ isLt⟩

mutual

inductive VNeut : ∀ ℓ, Type
  | var (l : Fin ℓ)                 : VNeut ℓ
  | ap (e : VNeut ℓ) (e₁ : VNorm ℓ) : VNeut ℓ

inductive VNorm : ∀ ℓ, Type
  | neut (e : VNeut ℓ)                            : VNorm ℓ
  | lam (ρ : Vec (VNorm ℓ) ℓ') (e₂ : Exp ℓ'.succ) : VNorm ℓ

end

instance : Inhabited (VNeut (.succ ℓ)) := ⟨.var 0⟩
instance : Inhabited (VNorm ℓ) := ⟨.lam .nil default⟩

partial def eval (ρ : Vec (VNorm ℓ) ℓ') : (e : Exp ℓ') → VNorm ℓ
  | .var i   => ρ.get i
  | .lam e₂  => .lam ρ e₂
  | .ap e e₁ =>
    match eval ρ e with
    | .neut e    => .neut (.ap e (eval ρ e₁))
    | .lam ρ' e₂ => eval (.cons (eval ρ e₁) ρ') e₂

-- TODO

mutual

def VNorm.castSucc : (e : VNorm ℓ) → VNorm ℓ.succ
  | .lam ρ e₂ => .lam (VNorm.castSuccVec ρ) e₂
  | .neut e   => .neut e.castSucc

def VNorm.castSuccVec : (es : Vec (VNorm ℓ) ℓ') → Vec (VNorm ℓ.succ) ℓ'
  | .nil            => .nil
  | .cons head tail => .cons head.castSucc (VNorm.castSuccVec tail)

def VNeut.castSucc : (e : VNeut ℓ) → VNeut ℓ.succ
  | .var i   => .var i.castSucc
  | .ap e e₁ => .ap e.castSucc e₁.castSucc

end

instance : (e : VNeut ℓ) → Inhabited (Neut ℓ)
  | .var l  => ⟨.var l⟩
  | .ap e _ => instForAllVNeutInhabitedNeut e

mutual

partial def readback : (n : VNorm ℓ) → Norm ℓ
  | .lam ρ e₂ => .lam (readback (eval (.cons (.neut (.var (Fin.last ℓ))) (VNorm.castSuccVec ρ)) e₂))
  | .neut e   => .neut (readbackNeut e)

partial def readbackNeut : (n : VNeut ℓ) → Neut ℓ
  | .var ℓ   => .var ℓ.rev
  | .ap n n₁ => .ap (readbackNeut n) (readback n₁)

end

def normalize (e : Exp .zero) : Norm .zero := readback (eval .nil e)
