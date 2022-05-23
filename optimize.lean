import algebra.order.monoid
import data.nat.basic
import data.int.basic

section

variables {α : Type*} [has_lt α] (f : ℕ → α) (x : ℕ)

@[simp]
def concave [has_add α] (f : ℕ → α) :=
∀ x, f x + f (x + 2) < f (x + 1) + f (x + 1)

@[simp]
def increasing_at := f x < f (x + 1)

@[simp]
def decreasing_at := f (x + 1) < f x

end

section

variables {α : Type*} [ordered_cancel_add_comm_monoid α] {f : ℕ → α}

lemma concave_t (h : concave f) (x y) :
  f x + f (x + y + 2) < f (x + 1) + f (x + y + 1) :=
begin
  induction y,
  case nat.zero {
    exact h x,
  },
  case nat.succ : y ih {
    specialize h (x + y + 1),
    apply lt_of_add_lt_add_right,
    apply lt_of_add_lt_add_right,
    calc  f x + f (x + y + 3) + f (x + y + 2) + f (x + y + 1)
        = f x + f (x + y + 2) + (f (x + y + 1) + f (x + y + 3)) : by cc
    ... < f (x + 1) + f (x + y + 1) + (f (x + y + 2) + f (x + y + 2)) : add_lt_add ih h
    ... = f (x + 1) + f (x + y + 2) + f (x + y + 2) + f (x + y + 1) : by cc,
  },
end

lemma concave_t' (h : concave f) {x y} :
  x < y → f x + f (y + 1) < f (x + 1) + f y :=
begin
  intro hxy,
  cases nat.exists_eq_add_of_lt hxy with z hy,
  rw hy,
  apply concave_t h,
end

variable [decidable_rel (@has_lt.lt α _)]

def argmax' (h : concave f) : ∀ {x y}, increasing_at f x → decreasing_at f (x + y + 1) → ℕ
| x 0 _ _ := x + 1
| x (y + 1) hi hd :=
  if hd' : f (x + y + 2) < f (x + y + 1)
  then argmax' hi hd'
  else by {
    unfold decreasing_at at hd,
  }

def maximum (h : concave f) : ∀ {x y}, increasing_at f x → decreasing_at f y → ℕ
| x y := sorry

example : concave f → increasing_at x + 1 →

end

section

variables (f : ℕ → ℤ) (x y : ℕ)

lemma concave_upper_bound : concave f → f x + f (x + y + 2) + y < f (x + 1) + f (x + y + 1) :=
begin
  intro h,
  induction y,
  case nat.zero {
    simp,
    apply h,
  },
  case nat.succ : y ih {
    have,
    {
      calc  f x + f (x + y + 3) + y + 1 + f (x + y + 2) + f (x + y + 1)
          = f x + f (x + y + 2) + y + (f (x + y + 1) + f (x + y + 3) + 1) : by cc
      ... < f (x + 1) + f (x + y + 1) + (f (x + y + 2) + f (x + y + 2)) : add_lt_add_of_lt_of_le ih (h (x + y + 1))
      ... = f (x + 1) + f (x + y + 2) + f (x + y + 2) + f (x + y + 1) : by cc,
    },
    rw [int.coe_nat_succ, ← add_assoc],
    exact lt_of_add_lt_add_right (lt_of_add_lt_add_right this),
  },
end

def find_decreasing' : ℕ → ℕ → ℕ
| x 0 := x
| x (y + 1) :=
  if f (x + 1) < f x
  then x
  else find_decreasing' (x + 1) y

def find_decreasing : ℕ :=
if h : f 1 < f 0
then 0
else find_decreasing' f 1 (f 1 - f 0).to_nat

lemma find_decreasing'_bound : x ≤ find_decreasing' f x y ∧ find_decreasing' f x y ≤ x + y :=
begin
  induction y generalizing x,
  case nat.zero {
    split; refl,
  },
  case nat.succ : y ih {
    unfold find_decreasing',
    by_cases f (x + 1) < f x; simp [h],
    specialize ih (x + 1),
    rw [add_assoc, add_comm 1 y] at ih,
    split,
    transitivity,
    exact nat.le_succ _,
    exact ih.left,
    exact ih.right,
  },
end

lemma int.coe_to_nat {x : ℤ} : 0 ≤ x → ↑x.to_nat = x :=
by cases x; simp

example : concave f → decreasing_at f (find_decreasing f) :=
begin
  intro hf,
  unfold decreasing_at find_decreasing,
  by_cases f 1 < f 0; simp [h],
  have := λ z, concave_upper_bound f 0 z hf,
  simp at this,
  generalize hy : (f 1 - f 0).to_nat = y,
  have hf := int.coe_to_nat (sub_nonneg.mpr (not_lt.mp h)),
  have : f 1 = f 0 + y,
    rw ← hy,
    rw hf,
    simp,
  rw this at *,
  have hb := find_decreasing'_bound f 1 y,
  induction y,
  case nat.zero {
    unfold find_decreasing',
    simp at h hy,
    specialize hf 0,
    simp [le_antisymm h hy] at hf,
    assumption,
  },
  case nat.succ : y ih {
    
  },

  have : f 1 = (f 1 - f 0).to_nat + f 0,
    rw [hf, sub_add_cancel],
  rw this,
end

end
