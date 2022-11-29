private def Nat.rec' {motive : Nat → Sort u} (zero : motive zero) (succ : ∀ n, motive n → motive (succ n)) : ∀ n, motive n
  | .zero => zero
  | .succ n => succ n (rec' zero succ n)

@[csimp]
private theorem Nat.rec_eq_rec' : @rec = @rec' := by
  funext motive zero succ n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (succ n) ih

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by _ m n => (m, n)

def ack' : Nat → Nat → Nat :=
  Nat.rec
    (λ n => n + 1)
    λ _m ack_m => Nat.rec
      (ack_m 1)
      λ _n ack_m_1_n => ack_m ack_m_1_n

example : ack 0 n = n + 1 := rfl
example : ack (m + 1) 0 = ack m 1 := rfl
example : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := rfl

example : ack' 0 n = n + 1 := rfl
example : ack' (m + 1) 0 = ack' m 1 := rfl
example : ack' (m + 1) (n + 1) = ack' m (ack' (m + 1) n) := rfl
