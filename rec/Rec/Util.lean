import Lean.Data.RBMap

namespace Lean.RBNode

variable {α : Type u} {β γ : α → Type v} (f : (a : α) → β a → γ a)

theorem map_balance1 l k v r : map f (balance1 l k v r) = balance1 (map f l) k (f k v) (map f r) := by
  cases l; case' node c l' _ _ r' =>
    cases c
    all_goals cases l'; case' node c _ _ _ _ => cases c
    all_goals cases r'; case' node c _ _ _ _ => cases c
  all_goals rfl

theorem map_balance2 l k v r : map f (balance2 l k v r) = balance2 (map f l) k (f k v) (map f r) := by
  cases r; case' node c l' _ _ r' =>
    cases c
    all_goals cases l'; case' node c _ _ _ _ => cases c
    all_goals cases r'; case' node c _ _ _ _ => cases c
  all_goals rfl

theorem map_ins cmp t k v : map f (ins cmp t k v) = ins cmp (map f t) k (f k v) := by
  induction t with
  | leaf => rfl
  | node c l key val r hl hr =>
    cases c <;> dsimp [ins] <;> split <;> dsimp [map] <;> congr
    . apply (map_balance1 ..).trans; congr
    . apply (map_balance2 ..).trans; congr

theorem map_setBlack t : map f (setBlack t) = setBlack (map f t) := by
  cases t <;> rfl

theorem map_insert cmp t k v : map f (insert cmp t k v) = insert cmp (map f t) k (f k v) := by
  match t with
  | leaf => rfl
  | node .red .. => apply (map_setBlack ..).trans; congr; apply map_ins
  | node .black .. => apply map_ins

theorem map_setRed t : map f (setRed t) = setRed (map f t) := by
  cases t <;> rfl

theorem map_balLeft l k v r : map f (balLeft l k v r) = balLeft (map f l) k (f k v) (map f r) := by
  cases r; case' node c l' _ _ _ =>
    cases c
    all_goals cases l'; case' node c _ _ _ _ => cases c
  all_goals cases l; case' node c _ _ _ _ => cases c
  all_goals simp [balLeft, map, map_balance2, map_setRed]

theorem map_balRight l k v r : map f (balRight l k v r) = balRight (map f l) k (f k v) (map f r) := by
  cases l; case' node c _ _ _ r' =>
    cases c
    all_goals cases r'; case' node c _ _ _ _ => cases c
  all_goals cases r; case' node c _ _ _ _ => cases c
  all_goals simp [balRight, map, map_balance1, map_setRed]

theorem map_appendTrees l r : map f (appendTrees l r) = appendTrees (map f l) (map f r) := by
  cases l; case' node c _ _ _ _ => cases c
  all_goals cases r; case' node c _ _ _ _ => cases c
  all_goals try rfl
  all_goals
    simp [appendTrees]
    simp [map]
    simp [appendTrees]
    rename_i l₁ k₁ v₁ r₁ l₂ k₂ v₂ r₂
  . have : size r₁ + size l₂ < size (node .red l₁ k₁ v₁ r₁) + size (node .red l₂ k₂ v₂ r₂) := by
      dsimp [size]
      rw [Nat.add_comm (size l₂), Nat.add_right_comm, Nat.add_assoc, Nat.add_assoc, ← Nat.add_assoc (size r₁), ← Nat.add_assoc (size r₁), Nat.add_left_comm (size r₁)]
      apply Nat.le_trans _ (Nat.le_add_left ..)
      apply Nat.le.step
      simp [Nat.add_assoc]
      apply Nat.le_trans _ (Nat.le_add_left ..)
      apply Nat.lt_succ_self
    rw [← map_appendTrees r₁ l₂]
    cases appendTrees r₁ l₂; case' node c _ _ _ _ => cases c
    all_goals simp [map]
  . have : size r₁ + size (node .black l₂ k₂ v₂ r₂) < size (node .red l₁ k₁ v₁ r₁) + size (node .black l₂ k₂ v₂ r₂) := by
      apply Nat.add_lt_add_right
      apply Nat.le_add_left
    apply map_appendTrees
  . have : size (node .black l₁ k₁ v₁ r₁) + size l₂ < size (node .black l₁ k₁ v₁ r₁) + size (node .red l₂ k₂ v₂ r₂) := by
      dsimp [size]
      apply Nat.add_lt_add_left
      rw [Nat.add_right_comm]
      apply Nat.le_add_right
    apply map_appendTrees
  . have : size r₁ + size l₂ < size (node .black l₁ k₁ v₁ r₁) + size (node .black l₂ k₂ v₂ r₂) := by
      dsimp [size]
      rw [Nat.add_comm (size l₂), Nat.add_right_comm, Nat.add_assoc, Nat.add_assoc, ← Nat.add_assoc (size r₁), ← Nat.add_assoc (size r₁), Nat.add_left_comm (size r₁)]
      apply Nat.le_trans _ (Nat.le_add_left ..)
      apply Nat.le.step
      simp [Nat.add_assoc]
      apply Nat.le_trans _ (Nat.le_add_left ..)
      apply Nat.lt_succ_self
    rw [← map_appendTrees r₁ l₂]
    cases appendTrees r₁ l₂; case' node c _ _ _ _ => cases c
    all_goals simp [map, map_balLeft]
termination_by _ l r => l.size + r.size

theorem map_del cmp x t : map f (del cmp x t) = del cmp x (map f t) := by
  induction t with
  | leaf => rfl
  | node _ l _ _ r =>
    unfold del
    dsimp [map]
    split
    . match l with
      | leaf => rfl
      | node .red .. => simp [isBlack, map]; assumption
      | node .black .. => simp [isBlack, map]; apply (map_balLeft ..).trans; congr
    . match r with
      | leaf => rfl
      | node .red .. => simp [isBlack, map]; assumption
      | node .black .. => simp [isBlack, map]; apply (map_balRight ..).trans; congr
    . apply map_appendTrees

theorem map_erase cmp x t : map f (erase cmp x t) = erase cmp x (map f t) := by
  apply (map_setBlack ..).trans; congr; apply map_del

theorem WellFormed.mapWff (w : WellFormed cmp n) : WellFormed cmp (map f n) := by
  induction w with
  | leafWff => exact leafWff
  | insertWff _ h ih => exact h ▸ insertWff ih (map_insert ..)
  | eraseWff _ h ih => exact h ▸ eraseWff ih (map_erase ..)

end Lean.RBNode

def Lean.RBMap.map (f : α → β → γ) : RBMap α β cmp → RBMap α γ cmp
  | ⟨t, w⟩ => ⟨.map f t, .mapWff f w⟩

def Lean.RBMap.mapM [Monad m] (f : α → β → m γ) : RBMap α β cmp → m (RBMap α γ cmp)
  | ⟨t, w⟩ => return ⟨← t.mapM f, sorry⟩
