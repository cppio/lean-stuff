set_option autoImplicit false

variable (F : Nat → Type _) (V : Type _)

inductive Term
  | var (x : V)
  | app (n) (f : F n) (t : (i : Fin n) → Term)

open Term

variable {F} {V}

variable [DecidableEq V]

def Term.contains (x : V) : Term F V → Bool
  | var y => y = x
  | app n f t => sorry

variable [∀ n, DecidableEq (F n)]

def unify : List (Term F V × Term F V) → Option (V → Term F V)
  | [] => some var
  | (var x, var y)::tl => if x = y then unify tl else replace_in y (var x) <$> (unify $ subst' (replace y (var x)) tl)
termination_by _ L => Prod.lex (sorry, sorry)

/-\===============================================================================\-/

open Std (Format)

namespace Fin

def tail {n : Nat} {α : Fin n.succ → Sort _} (t : ∀ i, α i) : ∀ i : Fin n, α i.succ :=
λ i => t i.succ

protected def reprTuple : ∀ {n} {α : Fin n → Type _} [∀ i, Repr (α i)], (∀ i, α i) → List Format
  | 0, α, _, t => []
  | n + 1, α, _, t => repr (t 0) :: Fin.reprTuple (Fin.tail t)

end Fin

instance {n} {α : Fin n → Type _} [∀ i, Repr (α i)] : Repr (∀ i, α i) where
  reprPrec t _ := Format.bracket "(" (Format.joinSep (Fin.reprTuple t) ("," ++ Format.line)) ")"

instance : Repr Format where
  reprPrec f _ := f

protected def Term.repr [∀ n, Repr (F n)] [Repr V] : Term F V → Format
  | var x => repr x
  | app 0 f t => repr f
  | app n f t => repr f ++ repr (λ i => Term.repr (t i))

instance [∀ n, Repr (F n)] [Repr V] : Repr (Term F V) where
  reprPrec t _ := t.repr

def V' := Nat

protected def V'.repr (x : V') : String := "?" ++ Nat.repr x

instance : Repr V' where
  reprPrec x _ := x.repr

def F' : Nat → Type
  | 0 => Unit
  | 2 => Unit
  | _ => Empty

protected def F'.repr : ∀ {n}, F' n → String
  | 0, () => "o"
  | 2, () => "fn"

instance {n} : Repr (F' n) where
  reprPrec f _ := f.repr

def var' : Nat → Term F' V' := Term.var

def o : Term F' V' := Term.app 0 () Fin.elim0
def fn (a b : Term F' V') : Term F' V' := Term.app 2 () λ | 0 => a | 1 => b

#eval fn (fn (var' 0) o) (fn o (var' 1))
