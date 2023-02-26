class Preorder (α) extends LE α where
  trans {x y z : α} : x ≤ y → y ≤ z → x ≤ z
  refl (x : α) : x ≤ x

class TotalPreorder (α) extends Preorder α where
  total (x y : α) : x ≤ y ∨ y ≤ x
  refl x := (total x x).elim id id

theorem le_of_not_le [I : TotalPreorder α] {x y : α} (h : ¬x ≤ y) : y ≤ x :=
  (I.total x y).elim (False.elim ∘ h) id

instance : TotalPreorder Nat where
  trans := Nat.le_trans
  total := Nat.le_total

inductive List.Chain (R : α → α → Prop) : α → List α → Prop
  | nil : Chain R a []
  | cons : R a b → Chain R b l → Chain R a (b :: l)

def List.Chain' (R : α → α → Prop) : List α → Prop
  | [] => True
  | a :: l => Chain R a l

inductive List.Perm : List α → List α → Prop
  | nil : Perm [] []
  | cons (x) : Perm l₁ l₂ → Perm (x :: l₁) (x :: l₂)
  | swap (x y l) : Perm (y :: x :: l) (x :: y :: l)
  | trans : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

@[simp]
theorem List.Perm.refl : (l : List α) → Perm l l
  | [] => nil
  | x :: l => cons x (refl l)

theorem List.Perm.symm (h : Perm l₂ l₁) : Perm l₁ l₂ := by
  induction h with
  | nil => exact nil
  | cons x _ ih => exact cons x ih
  | swap x y l => exact swap y x l
  | trans _ _ ih₁ ih₂ => exact trans ih₂ ih₁

theorem List.Perm.swap' (y) (h : Perm l₁ (x :: l₂)) : Perm (y :: l₁) (x :: y :: l₂) :=
  trans (cons y h) (swap x y l₂)

theorem List.Perm.length_eq (h : Perm l₁ l₂) : length l₁ = length l₂ := by
  induction h <;> simp [*]

theorem List.Perm.middle (x : α) : ∀ l₁ l₂, Perm (l₁ ++ x :: l₂) (x :: l₁ ++ l₂)
  | [], _ => refl _
  | y :: l₁, l₂ => swap' y (middle x l₁ l₂)

theorem List.Perm.inv : Perm (l₁ ++ x :: r₁) (l₂ ++ x :: r₂) → Perm (l₁ ++ r₁) (l₂ ++ r₂) := by
  generalize h₁ : l₁ ++ x :: r₁ = s₁
  generalize h₂ : l₂ ++ x :: r₂ = s₂
  intro h
  induction h generalizing l₁ r₁ l₂ r₂ with
  | nil => sorry
  | cons y h ih =>
    cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂
    . exact h
    . exact trans h (middle _ _ _)
    . exact trans (symm (middle _ _ _)) h
    . exact cons y (ih rfl rfl)
  | swap _ _ _ => sorry
  | trans _ _ _ _ => sorry

@[simp]
theorem List.Perm.cons_iff : Perm (x :: l₁) (x :: l₂) ↔ Perm l₁ l₂ where
  mp h := inv (l₁ := []) (l₂ := []) h
  mpr := cons x

@[simp]
theorem List.Perm.cons_iff' : Perm (y₁ :: x :: l₁) (y₂ :: x :: l₂) ↔ Perm (y₁ :: l₁) (y₂ :: l₂) where
  mp h := inv (l₁ := [y₁]) (l₂ := [y₂]) h
  mpr h := trans (trans (swap x y₁ l₁) (cons x h)) (swap y₂ x l₂)

@[simp]
theorem List.Perm.swap_iff : Perm (y :: l₁) (x :: y :: l₂) ↔ Perm l₁ (x :: l₂) where
  mp h := inv (l₁ := []) (l₂ := [x]) h
  mpr := swap' y

@[simp]
theorem List.Perm.swap_iff' : Perm (y₁ :: x :: l₁) (x :: y₂ :: l₂) ↔ Perm (y₁ :: l₁) (y₂ :: l₂) where
  mp h := inv (l₁ := [y₁]) (l₂ := []) h
  mpr h := symm (swap' x (symm h))

class ComparisonSort (f : ∀ {α} [I : LE α] [DecidableRel I.le], List α → List α) where
  perm [I : LE α] [DecidableRel I.le] (l : List α) : (f l).Perm l
  sort [I : TotalPreorder α] [DecidableRel I.le] (l : List α) : (f l).Chain' I.le

section

variable [I : LE α] [DecidableRel I.le]

def insert (x : α) : List α → List α
  | [] => [x]
  | y :: l =>
    if x ≤ y
    then x :: y :: l
    else y :: insert x l

def insertionSort : List α → List α
  | [] => []
  | x :: l => insert x (insertionSort l)

theorem perm_insert (x : α) (l) : (insert x l).Perm (x :: l) := by
  induction l <;> simp [insert]; split <;> simp [*]

end

theorem sort_insert [I : TotalPreorder α] [DecidableRel I.le] (x) (h : l.Chain' I.le) : (insert x l).Chain' I.le := by
  induction l
  case nil => exact .nil
  case cons y l ih =>
    unfold insert
    split
    case _ h' => exact .cons h' h
    case _ h' =>
      have h' := le_of_not_le h'
      dsimp [List.Chain']
      cases h
      case nil => exact .cons h' .nil
      case cons z l h₁ h₂  =>
        specialize ih h₁
        unfold insert at ih ⊢
        split
        case _ h'' =>
          simp [h''] at ih
          exact .cons h' ih
        case _ h'' =>
          simp [h''] at ih
          exact .cons h₂ ih

instance : ComparisonSort @insertionSort where
  perm l := by
    induction l with
    | nil => exact .nil
    | cons x l ih => exact .trans (perm_insert x (insertionSort l)) (.cons x ih)
  sort l := by
    induction l with
    | nil => exact trivial
    | cons x l ih => exact sort_insert x ih

section

variable [I : LE α] [DecidableRel I.le]

def select (x : α) : List α → α × List α
  | [] => (x, [])
  | y :: l =>
    if x ≤ y
    then ((select x l).1, y :: (select x l).2)
    else ((select y l).1, x :: (select y l).2)

theorem perm_select (x : α) (l) : ((select x l).1 :: (select x l).2).Perm (x :: l) := by
  induction l generalizing x <;> simp [select]; split <;> simp [*]

def selectionSort : List α → List α
  | [] => []
  | x :: l =>
    have := Nat.le_of_eq (perm_select x l).length_eq
    (select x l).1 :: selectionSort (select x l).2
termination_by _ l => l.length

end

instance : ComparisonSort @selectionSort where
  perm l := by
    generalize hn : l.length = n
    induction n generalizing l with
    | zero =>
      cases l with
      | nil => exact .nil
      | cons => cases hn
    | succ _ ih =>
      cases l with
      | nil => cases hn
      | cons x l =>
        simp [selectionSort]
        exact .trans (.cons _ (ih _ (Nat.succ.inj ((perm_select x l).length_eq.trans hn)))) (perm_select x l)
  sort l := by
    sorry

-- todo: comparison in monad, time complexity

section

variable [Monad m] (le : α → α → m Bool)

def insertM (x : α) : List α → m (List α)
  | [] => return [x]
  | y :: l =>
    return if ← le x y
      then x :: y :: l
      else y :: (← insertM x l)

def insertM' (x : α) : List α → m (List α)
  | [] => return [x]
  | y :: l => do
    if ← le x y
    then return x :: y :: l
    else return y :: (← insertM' x l)

def myLe (x y : Nat) : IO Bool := do
  IO.println s!"{x} ≤ {y}"
  return x ≤ y

#print insertM
#print insertM'

def insertionSortM : List α → List α
  | [] => []
  | x :: l => insertM ifLE x (insertionSortM l)

end

variable [I : LE α] [DecidableRel I.le]

def isLE (x y : α) (t e : List α) : List α :=
  if x ≤ y then t else e

theorem insert_eq_insertM (x : α) (l) : insert x l = insertM isLE x l := by
  unfold isLE
  induction l <;> simp [insert, insertM]
  split <;> simp [*]

theorem insertionSort_eq_insertionSortM (l : List α) : insertionSort l = insertionSortM isLE l := by
  induction l <;> simp [insertionSort, insertionSortM, insert_eq_insertM, *]
