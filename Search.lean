@[simp]
theorem Subarray.size_popFront (a : Subarray α) : a.popFront.size = a.size.pred := by
  cases h : a.size with
  | zero =>
    have : ¬a.start < a.stop := by
      rw [Nat.not_lt_eq, ← Nat.zero_add a.start]
      exact Nat.le_add_of_sub_le <| Nat.le_of_eq h
    simp [popFront, this]
    exact h
  | succ =>
    rw [← h]
    have : a.start < a.stop := by
      dsimp [size] at h
      have := Nat.le_of_eq h
      sorry
    simp [popFront, this]
    rfl

variable [BEq α] (x : α) (a : Subarray α)

def linsearch (a : Subarray α) : Option Nat :=
  if _ : 0 < a.size
  then
    if a[0] == x
    then some 0
    else linsearch a.popFront
  else none
termination_by _ => a.size

def ilinsearch : Option Nat := Id.run do
  for h : i in [:a.size] do
    if a[i]'h.2 == x then
      return some i
  return none

theorem ilinsearch_eq_linsearch : linsearch x a = ilinsearch x q := by
  unfold linsearch ilinsearch
  dsimp [Id.run]
  sorry
