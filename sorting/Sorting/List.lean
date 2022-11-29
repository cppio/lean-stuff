namespace List

inductive Chain (r : α → α → Prop) : List α → Prop
  | nil : Chain r []
  | singleton a : Chain r [a]
  | cons : r a b → Chain r (b :: l) → Chain r (a :: b :: l)

namespace Chain

attribute [simp] nil singleton

@[simp]
theorem cons_iff : Chain r (a :: b :: l) ↔ r a b ∧ Chain r (b :: l) where
  mp | cons h c => ⟨h, c⟩
  mpr | ⟨h, c⟩ => cons h c

theorem fst : Chain r (a :: b :: l) → r a b
  | cons h _ => h

theorem snd : Chain r (a :: l) → Chain r l
  | singleton _ => nil
  | cons _ c => c

end Chain

inductive Perm : List α → List α → Prop
  | nil : Perm [] []
  | cons a : Perm l₁ l₂ → Perm (a :: l₁) (a :: l₂)
  | swap a b : Perm l₁ l₂ → Perm (b :: a :: l₁) (a :: b :: l₂)
  | trans : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

namespace Perm

@[simp]
theorem refl : (l : List α) → Perm l l
  | [] => nil
  | a :: l => cons a (refl l)

theorem symm (p : Perm l₂ l₁) : Perm l₁ l₂ := by
  induction p with
  | nil => exact nil
  | cons a _ p => exact cons a p
  | swap a b _ p => exact swap b a p
  | trans _ _ p₁ p₂ => exact trans p₂ p₁

theorem middle (a : α) : ∀ l r, Perm (l ++ a :: r) (a :: l ++ r)
  | [], _ => refl _
  | b :: l, r => trans (cons b (middle a l r)) (swap a b (refl _))

theorem inv_lemma : Perm (l ++ a :: r) L → ∃ l r, L = l ++ a :: r := by
  generalize h : l ++ a :: r = s
  intro h
  induction h generalizing l r with
  | nil => cases l <;> cases h
  | cons b _ ih =>
    cases l <;> cases h
    . exact ⟨[], _, rfl⟩
    . have ⟨l, r, ih⟩ := ih rfl
      exact ⟨b :: l, r, congrArg (b :: ·) ih⟩
  | swap b c _ ih =>
    (cases l; (case' cons l => cases l); rotate_right)
      <;> cases h
    . exact ⟨[b], _, rfl⟩
    . exact ⟨[], c :: _, rfl⟩
    . have ⟨l, r, ih⟩ := ih rfl
      exact ⟨b :: c :: l, r, congrArg (b :: c :: ·) ih⟩
  | trans _ _ ih₁ ih₂ =>
    cases h
    have ⟨_, _, ih₁⟩ := ih₁ rfl
    cases ih₁
    exact ih₂ rfl

theorem inv l₁ l₂ a : Perm (l₁ ++ a :: r₁) (l₂ ++ a :: r₂) → Perm (l₁ ++ r₁) (l₂ ++ r₂) := by
  generalize h₁ : l₁ ++ a :: r₁ = s₁
  generalize h₂ : l₂ ++ a :: r₂ = s₂
  intro h
  induction h generalizing l₁ r₁ l₂ r₂ with
  | nil => cases l₁ <;> cases h₁
  | cons _ p ih =>
    cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂
    . exact p
    . exact trans p (middle _ _ _)
    . exact trans (symm (middle _ _ _)) p
    . exact cons _ (ih _ _ rfl rfl)
  | swap _ _ p ih =>
    (cases l₁; (case' cons l₁ => cases l₁); rotate_right)
      <;> (cases l₂; (case' cons l₂ => cases l₂); rotate_right)
      <;> cases h₁ <;> cases h₂
    . exact cons _ p
    . exact cons _ p
    . exact cons _ (trans p (middle _ _ _))
    . exact cons _ p
    . exact cons _ p
    . exact trans (cons _ (trans p (middle _ _ _))) (swap _ _ (refl _))
    . exact cons _ (trans (symm (middle _ _ _)) p)
    . exact trans (swap _ _ (refl _)) (cons _ (trans (symm (middle _ _ _)) p))
    . exact swap _ _ (ih _ _ rfl rfl)
  | trans p₁ p₂ ih₁ ih₂ =>
    subst_vars
    have ⟨_, _, h⟩ := inv_lemma p₁
    subst_vars
    apply trans (ih₁ _ _ rfl rfl) (ih₂ _ _ rfl rfl)

@[simp]
theorem cons_iff : Perm (x :: l₁) (x :: l₂) ↔ Perm l₁ l₂ where
  mp := inv [] [] x
  mpr := cons x

@[simp]
theorem cons'_iff : Perm (y₁ :: x :: l₁) (y₂ :: x :: l₂) ↔ Perm (y₁ :: l₁) (y₂ :: l₂) where
  mp := inv [y₁] [y₂] x
  mpr p := trans (trans (swap x y₁ (refl l₁)) (cons x p)) (swap y₂ x (refl l₂))

@[simp]
theorem swap_iff₁ : Perm (x :: l₁) (y :: x :: l₂) ↔ Perm l₁ (y :: l₂) where
  mp := inv [] [y] x
  mpr p := trans (cons x p) (swap y x (refl l₂))

@[simp]
theorem swap_iff₂ : Perm (y :: x :: l₁) (x :: l₂) ↔ Perm (y :: l₁) l₂ where
  mp := inv [y] [] x
  mpr p := trans (swap x y (refl l₁)) (cons x p)

theorem length (p : Perm l₁ l₂) : length l₁ = length l₂ := by
  induction p <;> simp [*]

theorem mem (p : Perm l₁ l₂) {x} : Mem x l₁ → Mem x l₂ := by
  induction p generalizing x with
  | nil =>
    intro h
    exact h
  | cons _ _ ih =>
    intro h
    cases h
    case head => exact .head _
    case tail h => exact .tail _ (ih h)
  | swap _ _ _ ih =>
    intro h
    cases h
    case head => exact .tail _ (.head _)
    case tail h =>
      cases h
      case head => exact .head _
      case tail h => exact .tail _ (.tail _ (ih h))
  | trans _ _ ih₁ ih₂ => exact ih₂ ∘ ih₁

end Perm
