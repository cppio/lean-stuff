inductive ℕ
  | z : ℕ
  | s (n : ℕ) : ℕ

def ℕ.add (a : ℕ) : ℕ → ℕ
  | z => a
  | s b => s (add a b)

instance : Add ℕ where
  add := ℕ.add

def ℕ.mul (a : ℕ) : ℕ → ℕ
  | z => z
  | s b => mul a b + a

instance : Mul ℕ where
  mul := ℕ.mul

theorem ℕ.add_z a : a + z = a := rfl
theorem ℕ.add_s a b : a + s b = s (a + b) := rfl

theorem ℕ.z_add : ∀ b, z + b = b
  | z => rfl
  | s b => congrArg s (z_add b)

theorem ℕ.s_add a : ∀ b, s a + b = s (a + b)
  | z => rfl
  | s b => congrArg s (s_add a b)

theorem ℕ.add_comm a : (b : ℕ) → a + b = b + a
  | z => (z_add a).symm
  | s b => (congrArg s (add_comm a b)).trans (s_add b a).symm

theorem ℕ.add_assoc a b : (c : ℕ) → a + b + c = a + (b + c)
  | z => rfl
  | s c => congrArg s (add_assoc a b c)

theorem ℕ.mul_z a : a * z = z := rfl
theorem ℕ.mul_s a b : a * s b = a * b + a := rfl

theorem ℕ.z_mul : ∀ b, z * b = z
  | z => rfl
  | s b => z_mul b

theorem ℕ.s_mul a : ∀ b, s a * b = a * b + b
  | z => rfl
  | s b => (congrArg (· + s a) (s_mul a b)).trans (congrArg s ((add_assoc (a * b) b a).trans ((congrArg (a * b + ·) (add_comm b a)).trans (add_assoc (a * b) a b).symm)))

theorem ℕ.mul_comm a : (b : ℕ) → a * b = b * a
  | z => (z_mul a).symm
  | s b => (congrArg (· + a) (mul_comm a b)).trans (s_mul b a).symm

theorem ℕ.add_mul a b : (c : ℕ) → (a + b) * c = a * c + b * c
  | z => rfl
  | s c => show (a + b) * c + (a + b) = a * c + a + (b * c + b) from sorry

theorem ℕ.mul_add a b : (c : ℕ) → a * (b + c) = a * b + a * c
  | z => rfl
  | s c => (congrArg (· + a) (mul_add a b c)).trans (add_assoc (a * b) (a * c) a)

theorem ℕ.mul_assoc a b : (c : ℕ) → a * b * c = a * (b * c)
  | z => rfl
  | s c => show a * b * c + a * b = a * (b * c + b) from sorry

def ℤ := @Quot (ℕ × ℕ) λ (a, b) (c, d) => a + d = b + c

def ℤ.add : ℤ → ℤ → ℤ :=
  Quot.lift (λ (a, b) => Quot.lift (λ (c, d) => Quot.mk _ (a + c, b + d)) λ (c, d) (c', d') h => Quot.sound <| by
    dsimp at h ⊢
    sorry
  ) λ (a, b) (a', b') h => by
    dsimp at h
    dsimp
    sorry

def ℤ.mul : ℤ → ℤ → ℤ :=
  Quot.lift (λ (a, b) => Quot.lift (λ (c, d) => Quot.mk _ (a * c + b * d, a * d + b * c)) sorry) sorry

def ℤ.neg : ℤ → ℤ :=
  .lift (λ (a, b) => .mk _ (b, a)) λ _ _ h => Quot.sound h.symm

def ℤ.sub : ℤ → ℤ → ℤ :=
  Quot.lift (λ (a, b) => Quot.lift (λ (c, d) => Quot.mk _ (a + d, b + c)) sorry) sorry
