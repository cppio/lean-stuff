inductive Nat' : Type
  | zero : Nat'
  | succ : Nat' → Nat'

theorem Nat'.succ_inj : succ n = succ m → n = m :=
  Eq.rec (motive := λ m _ => rec False (λ m _ => n = m) m) rfl

theorem Nat'.succ_ne_zero : succ n ≠ zero :=
  Eq.rec (motive := λ m _ => rec False (λ _ _ => True) m) trivial

private def Nat'.rec' {motive : Nat' → Sort u} (zero : motive zero) (succ : ∀ n, motive n → motive n.succ) : ∀ n, motive n
  | .zero => zero
  | .succ n => succ n (rec' zero succ n)

attribute [implementedBy Nat'.rec'] Nat'.rec

def a : Nat' → Nat'
  | .zero => .zero
  | .succ i => .succ i

def b : Nat' → Nat'
  | .zero => .zero
  | .succ i => i

def c : Nat' → Nat'
  | .zero => .zero
  | .succ i => c i

def d : Nat' → Nat'
  | .zero => .zero
  | .succ i => .succ (d i)

def a' : Nat' → Nat' :=
  @Nat'.rec _
    .zero
    λ i _ => .succ i

def b' : Nat' → Nat' :=
  @Nat'.rec _
    .zero
    λ i _ => i

def c' : Nat' → Nat' :=
  @Nat'.rec _
    .zero
    λ _ c_i => c_i

def d' : Nat' → Nat' :=
  @Nat'.rec _
    .zero
    λ _ => .succ
