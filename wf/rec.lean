set_option eqn_compiler.lemmas false

def ack : ℕ → ℕ → ℕ
| 0 n := n + 1
| (m + 1) 0 := ack m 1
| (m + 1) (n + 1) := ack m (ack (m + 1) n)

#print prefix ack.equations

#reduce   ack 0 0
def foo : ack 0 0     = 1 := by simp
def typeof {α} (_ : α) := α
set_option pp.implicit true
#print foo

def ack' : ℕ → ℕ → ℕ :=
@nat.rec (λ m, ℕ → ℕ) (λ n, n + 1) $ λ m ack_m,
  @nat.rec (λ n, ℕ) (ack_m 1) $ λ n ack_sm_n,
    ack_m ack_sm_n

example (n) : ack' 0 n = n + 1 := rfl
example (m) : ack' (m + 1) 0 = ack' m 1 := rfl
example (m n) : ack' (m + 1) (n + 1) = ack' m (ack' (m + 1) n) := rfl

mutual def ack'', ack'''
with ack'' : ℕ → ℕ → ℕ
| 0 := nat.succ
| (m + 1) := ack''' (ack'' m)
with ack''' : (ℕ → ℕ) → ℕ → ℕ
| ack_m 0 := ack_m 1
| ack_m (n + 1) := ack_m (ack''' ack_m n)
