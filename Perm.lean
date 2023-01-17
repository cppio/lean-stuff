import Mathlib.Data.List.Perm

variable {α : Type u}

inductive Perm : List α → List α → Prop
  | nil : Perm [] []
  | cons x : Perm l (l₁ ++ l₂) → Perm (x :: l) (l₁ ++ x :: l₂)

theorem Perm.refl : (l : List α) → Perm l l
  | [] => .nil
  | x :: l => .cons (l₁ := []) x (refl l)

theorem Perm.trans {l₁ l₂ l₃ : List α} (h₁ : Perm l₁ l₂) (h₂ : Perm l₂ l₃) : Perm l₁ l₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons x h₁ ih₁ =>
    sorry

example : Perm l l' → List.Perm l l'
  | .nil => .nil
  | .cons x h => .trans (.cons x <| _example h) List.perm_middle.symm

example (h : List.Perm l l') : Perm l l' := by
  induction h with
  | nil => exact .nil
  | cons x _ h => exact .cons (l₁ := []) x h
  | swap x y => exact .cons (l₁ := [x]) y <| .refl _
  | trans _ _ h₁ h₂ => exact .trans h₁ h₂
