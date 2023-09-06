import Mathlib.Logic.Equiv.Defs

class Inductive (α : Type u) (F : Type u → Type v) [Functor F] where
  fold (x : F α) : α
  recursor {τ} (f : F τ → τ) (a : α) : τ
  rec_fold f x : @recursor τ f (fold x) = f (recursor f <$> x)

instance : Inductive Nat Option where
  fold
    | none => .zero
    | some n => .succ n
  recursor f := Nat.rec (f none) λ _ t => f <| some t
  rec_fold _
    | none => rfl
    | some _ => rfl

instance : Functor (Option <| α × ·) where
  map f
    | none => none
    | some (a, x) => some (a, f x)

noncomputable
instance : Inductive (List α) (Option <| α × ·) where
  fold
    | none => .nil
    | some (a, l) => .cons a l
  recursor f := List.rec (f none) λ a _ t => f <| some (a, t)
  rec_fold _
    | none => rfl
    | some _ => rfl
