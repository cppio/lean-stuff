def LoopT (m : Type u → Type v) (α : Type u) : Type (max (u + 1) v) :=
  (∀ {β}, (Unit → β → m (ForInStep β)) → β → m β) → m α

instance [Monad m] : Monad (LoopT m) where
  pure x _ := return x
  bind f g loop := do g (← f @loop) @loop

instance : ForIn (LoopT m) Lean.Loop Unit where
  forIn _ b f loop := loop (λ a b => f a b @loop) b

def LoopT.run [Monad m] (f : LoopT m α) : m α :=
  f Lean.Loop.forIn.loop

def isort [Monad m] (a : List Nat) : LoopT m (List Nat) := do
  let mut l := a
  let mut i := l.length - 1
  while 0 < i do
    let x := l[i - 1]!
    let mut j := i
    while j < a.length do
      if x ≤ l[j]! then break
      l := l.set (j - 1) l[j]!
      j := j + 1
    l := l.set (j - 1) x
    i := i - 1
  return l

def loopFuel : Nat → ∀ {β}, (Unit → β → Option (ForInStep β)) → β → Option β
  | 0, _, _, _ => none
  | n + 1, _, f, b => do
    match ← f () b with
    | .done b => b
    | .yield b => loopFuel n f b

#eval isort [5, 4, 3, 2, 1] |>.run |> Id.run
#eval isort [5, 4, 3, 2, 1] (loopFuel 5)

def Option.get : (o : Option α) → o ≠ none → α
  | some x, _ => x

theorem Option.get_some (h : o = some x) : Option.get o h' = x := by
  cases h
  rfl

theorem loopFuel_monotone : ∀ {n m}, n ≤ m → loopFuel n f b ≠ none → loopFuel m f b ≠ none
  | _, _, .refl, h => h
  | _ + 1, _ + 1, hnm, h => by
    dsimp [loopFuel, bind, Option.bind] at h ⊢
    split <;> rename_i h' <;> simp [h'] at h ⊢
    split <;> rename_i h' <;> simp [h'] at h ⊢
    apply loopFuel_monotone (Nat.pred_le_pred hnm) h

def ForInStep.ok (t : β → Nat) (up : Nat) : ForInStep β → Prop
  | .done _ => True
  | .yield b => 0 < t b ∧ t b < up

theorem termination (t : β → Nat) (f : Unit → β → Option (ForInStep β)) (b : β) (init : 0 < t b) (iter : ∀ b, (h : f () b ≠ none) ×' ((f () b).get h).ok t (t b)) : loopFuel (t b) f b ≠ none := by
  generalize htb : t b = n
  induction n using Nat.strongInductionOn generalizing b with
  | _ n ih =>
  cases htb
  cases htb : t b with
  | zero => cases htb ▸ init
  | succ n =>
    cases iter b with | _ iter₁ iter₂ =>
    dsimp [loopFuel, bind, Option.bind]
    split
    intro; apply iter₁; assumption
    dsimp
    split
    simp
    rename_i heq
    simp [Option.get_some heq, ForInStep.ok] at iter₂
    apply loopFuel_monotone
    exact Nat.pred_le_pred (htb ▸ iter₂.right)
    dsimp
    apply ih _ iter₂.right _ iter₂.left rfl

example l : ∃ n, isort l (@loopFuel n) ≠ none := by
  cases l with
  | nil => exists 1
  | cons x l =>
  exists l.length + 1
  simp only [isort, forIn, pure, bind, Option.bind]
  split <;> simp
  rename_i h; revert h
  show _ ≠ _
  apply termination (MProd.fst · + 1) _ ⟨_, _⟩ (Nat.zero_lt_succ _)
  intro b
  constructor
  case fst =>
    split <;> simp
    split <;> simp
    rename_i h; revert h
    show _ ≠ _
    cases b with | _ b₁ b₂ =>
    by_cases hb : b₁ < l.length + 1
    case inr => simp [loopFuel, bind, Option.bind, hb]
    apply loopFuel_monotone
    show List.length l + 2 - b₁ ≤ _
    apply Nat.sub_le_of_le_add
    rw [Nat.add_assoc, Nat.add_comm 1]
    apply Nat.add_le_add_left
    apply Nat.succ_le_succ
    assumption
    apply termination (l.length + 2 - MProd.fst ·) _ ⟨_, _⟩
    simp
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    apply Nat.le.step
    exact hb
    intro b
    constructor
    case fst =>
      split <;> simp
      split <;> simp
    case snd =>
      rename_i h
      simp [Option.get]
      dsimp
      split
      rename_i h₁ _
      split at h₁ <;> simp at h₁ <;> simp [← h₁, ForInStep.ok]
      split at h₁ <;> simp at h₁ <;> simp [← h₁, ForInStep.ok]
      constructor
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      apply Nat.succ_le_succ
      assumption
      rw [Nat.add_sub_add_right _ 1]
      apply Nat.le_sub_of_add_le
      rw [Nat.succ_add]
      apply Nat.succ_le_succ
      rw [Nat.sub_add_cancel]
      exact .refl
      apply Nat.le_of_lt
      assumption
  case snd =>
    split
    case inr => simp [Option.get, ForInStep.ok]
    rename_i h
    dsimp
    simp [Option.get]
    split
    rename_i h₁ _
    split at h₁ <;> simp at h₁
    simp [← h₁, ForInStep.ok]
    rw [Nat.sub_add_cancel h]
    constructor
    exact h
    exact .refl
