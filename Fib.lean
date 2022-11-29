variable {α : Type u} (f : α → α) (x : α)

def iterate₁ : Nat → α
  | 0 => x
  | n + 1 => f (iterate₁ n)

theorem iterate₁_succ : ∀ n, iterate₁ f x (n + 1) = iterate₁ f (f x) n
  | 0 => rfl
  | n + 1 => congrArg f (iterate₁_succ n)

def iterate₂ (x : α) : Nat → α
  | 0 => x
  | n + 1 => iterate₂ (f x) n

theorem iterate₂_succ x : ∀ n, iterate₂ f x (n + 1) = f (iterate₂ f x n)
  | 0 => rfl
  | n + 1 => iterate₂_succ (f x) n

theorem iterate₁_eq_iterate₂ x : ∀ n, iterate₁ f x n = iterate₂ f x n
  | 0 => rfl
  | n + 1 => (iterate₁_succ f x n).trans (iterate₁_eq_iterate₂ (f x) n)

theorem iterate₂_eq_iterate₁ : ∀ n, iterate₂ f x n = iterate₁ f x n
  | 0 => rfl
  | n + 1 => (iterate₂_succ f x n).trans (congrArg f (iterate₂_eq_iterate₁ n))

def iterate (n : Nat) : α :=
  Std.Range.forIn (m := Id) [:n] x λ _ x => .yield (f x)

theorem iterate_eq_iterate₂ : iterate f x n = iterate₂ f x n := by
  show Std.Range.forIn.loop _ _ _ (n + 0) .. = _
  generalize 0 = i
  induction n generalizing x i with
  | zero => apply ite_self
  | succ fuel ih =>
    have : ¬i ≥ fuel.succ + i :=
      Nat.add_comm _ i ▸ (Nat.not_succ_le_self _ <| Nat.le_trans · <| Nat.le_add_right i _)
    simp! [this]
    rw [Nat.succ_add]
    apply ih

theorem forInRange {p : Nat → α → Prop} (px : p 0 x) (pf : ∀ n x, p n x → p (n + 1) (f x)) n : p n (iterate f x n) := by
  rw [iterate_eq_iterate₂, iterate₂_eq_iterate₁]
  induction n with
  | zero => exact px
  | succ n ih => exact pf n _ ih

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def fib' (n : Nat) : Nat :=
  (h n).fst
where h
  | 0 => (0, 1)
  | n + 1 => let (a, b) := h n; (b, b + a)

theorem fib'_eq_fib n : fib' n = fib n :=
  congrArg Prod.fst (h n)
where h : ∀ n, fib'.h n = (fib n, fib (n + 1))
  | 0 => rfl
  | n + 1 => by rw [fib'.h, h n]; rfl

def fib'' (n : Nat) : Nat :=
  h n (0, 1)
where h
  | 0, (a, _) => a
  | n + 1, (a, b) => h n (b, b + a)

theorem fib''_eq_fib n : fib'' n = fib n :=
  h 0 n |>.trans <| congrArg fib <| Nat.zero_add n
where h m : ∀ n, fib''.h n (fib m, fib (m + 1)) = fib (m + n)
  | 0 => rfl
  | n + 1 => Nat.add_right_comm m n 1 ▸ h (m + 1) n

def ifib (n : Nat) : Nat := Id.run do
  let mut (a, b) := (0, 1)
  for _ in [:n] do
    (a, b) := (b, b + a)
  return a

theorem ifib_eq_fib n : ifib n = fib n := by
  apply congrArg (a₂ := ⟨fib n, fib (n + 1)⟩) MProd.fst
  apply forInRange (p := λ n ab => ab = MProd.mk (fib n) (fib (n + 1)))
  . rfl
  . intro _ _ ih
    cases ih
    rfl

variable (f : Nat → α → α) (x : α)

def iterate₁' : Nat → α
  | 0 => x
  | n + 1 => f n (iterate₁' n)

def iterate₂' : Nat → α :=
  h x 0
where h x i
  | 0 => x
  | n + 1 => h (f i x) (i + 1) n

theorem iterate₂'_eq_iterate₁' : ∀ n, iterate₂' f x n = iterate₁' f x n
  | 0 => rfl
  | n + 1 => .trans (h x 0 n) (congrArg (f n) <| iterate₂'_eq_iterate₁' n)
where h x i : ∀ n, iterate₂'.h f x i (n + 1) = f (n + i) (iterate₂'.h f x i n)
  | 0 => i.zero_add.symm ▸ rfl
  | n + 1 => n.succ_add i ▸ h (f i x) (i + 1) n

def iterate' (n : Nat) : α :=
  Std.Range.forIn (m := Id) [:n] x λ i x => .yield (f i x)

theorem iterate'_eq_iterate₂' : iterate' f x n = iterate₂' f x n := by
  show Std.Range.forIn.loop _ _ _ (n + 0) .. = iterate₂'.h ..
  generalize 0 = i
  induction n generalizing x i with
  | zero => apply ite_self
  | succ fuel ih =>
    have : ¬i ≥ fuel.succ + i :=
      Nat.add_comm _ i ▸ (Nat.not_succ_le_self _ <| Nat.le_trans · <| Nat.le_add_right i _)
    simp! [this]
    rw [Nat.succ_add]
    apply ih

theorem forInRange' {p : Nat → α → Prop} (px : p 0 x) (pf : ∀ n x, p n x → p (n + 1) (f n x)) n : p n (iterate' f x n) := by
  rw [iterate'_eq_iterate₂', iterate₂'_eq_iterate₁']
  induction n with
  | zero => exact px
  | succ n ih => exact pf n _ ih

def fac : Nat → Nat
  | 0 => 1
  | n + 1 => fac n * (n + 1)

def fac' : Nat → Nat :=
  h 1
where h a
  | 0 => a
  | n + 1 => h (a * (n + 1)) n

theorem fac'_eq_fac n : fac' n = fac n :=
  Nat.mul_one (fac n) ▸ h 1 n
where h a : ∀ n, fac'.h a n = fac n * a
  | 0 => Nat.one_mul a |>.symm
  | n + 1 => h (a * (n + 1)) n |>.trans <| Nat.mul_assoc _ _ a ▸ Nat.mul_comm _ a ▸ rfl

def ifac (n : Nat) : Nat := Id.run do
  let mut a := 1
  for i in [:n] do
    a := a * (i + 1)
  return a

theorem ifac_eq_fac n : ifac n = fac n := by
  apply forInRange' (p := λ n a => a = fac n)
  . rfl
  . intro _ _ ih
    cases ih
    rfl

def fac'' : Nat → Nat :=
  h 1 1
where h a i
  | 0 => a
  | n + 1 => h (a * i) (i + 1) n

partial
def fac''' (n : Nat) : Nat :=
  h 1 1
where h a i :=
  if i < n
  then h (a * (i + 1)) (i + 1)
  else a
