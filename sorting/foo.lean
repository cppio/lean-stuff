inductive list (α)
  | nil : list α
  | cons (x : α) (xs : list α) : list α

open list

def length : list α → Nat
  | nil => 0
  | cons _ xs => length xs + 1

def map (f : α → β) : list α → list β
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

theorem length_map (f : α → β) : ∀ l, length (map f l) = length l
  | nil => rfl
  | cons _ xs => congrArg (· + 1) (length_map f xs)

theorem length_map' : length (map f l) = length l := by
  induction l
  case nil =>
    rfl
  case cons x xs ih =>
    unfold map length
    simp
    assumption

structure array (α : Type) (n : Nat) :=
  l : list α
  h : length l = n

example (x y : Nat) : array Nat 2 := {
  l := cons x (cons y nil),
  h := rfl
}

def foo : IO Unit := do
  let l := [5, 6, 7, 8]
  for h : i in [:4] do
    IO.println (l[i]'h.2)


@[simp]
def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x ≤ y
    then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
termination_by _ l l' => (l, l')

@[simp] noncomputable
def merge' : List Nat → List Nat → List Nat :=
  List.rec
    (λ ys => ys)
    λ x xs merge_xs => List.rec
      (x :: xs)
      λ y ys merge_x_xs_ys =>
        if x ≤ y
        then x :: merge_xs (y :: ys)
        else y :: merge_x_xs_ys

example : merge [] ys = ys := rfl
example : merge (x :: xs) [] = x :: xs := rfl
example : merge (x :: xs) (y :: ys) = if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys := rfl

example : merge' [] ys = ys := rfl
example : merge' (x :: xs) [] = x :: xs := rfl
example : merge' (x :: xs) (y :: ys) = if x ≤ y then x :: merge' xs (y :: ys) else y :: merge' (x :: xs) ys := rfl

-- TODO allow example
def mergeeq : ∀ l l', merge l l' = merge' l l'
  | [], _ => by simp
  | _::_, [] => by simp
  | _::_, _::_ => by simp; split <;> exact congrArg _ (mergeeq _ _)
termination_by _ l l' => (l, l')

def partition : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x::xs =>
    let (l, r) := partition xs
    (x :: r, l)

theorem length_partition (x x' xs) :
  let l := x :: x' :: xs
  (partition l).1.length < l.length ∧ (partition l).2.length < l.length
:= by
  induction xs
  case nil => simp [partition]
  case cons _ _ ih =>
    cases ih
    constructor
    apply Nat.succ_lt_succ
    assumption
    apply Nat.lt.step
    assumption

@[simp]
def msort : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: x' :: xs =>
    let p := partition (x :: x' :: xs)
    have := (length_partition x x' xs).1
    have := (length_partition x x' xs).2
    merge (msort p.1) (msort p.2)
termination_by _ l => l.length

inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | singleton : Sorted [x]
  | cons : x ≤ x' → Sorted (x' :: xs) → Sorted (x :: x' :: xs)

theorem sorted_merge (hxs : Sorted xs) (hys : Sorted ys) : Sorted (merge xs ys) := by
  induction hxs
  case nil => simp; exact hys
  case singleton =>
    induction hys
    case nil => exact .singleton
    case singleton =>
      simp
      split
      case _ h => exact .cons h .singleton
      case _ h => exact .cons (Nat.ge_of_not_lt (h ∘ Nat.le_of_lt)) .singleton
    case cons hy hys ihy =>
      simp
      split
      case _ h => exact .cons h (.cons hy hys)
      case _ h =>
        split
        case _ h' => exact .cons (Nat.ge_of_not_lt (h ∘ Nat.le_of_lt)) (.cons h' hys)
        case _ h' => simp [h'] at ihy; exact .cons hy ihy
  case cons hx hxs ihx =>
    induction hys
    case nil => simp; exact Sorted.cons hx hxs
    case singleton =>
      simp
      split
      case _ h =>
        split
        case _ h' => simp [h'] at ihx; exact .cons hx ihx
        case _ h' => exact .cons h (.cons (Nat.ge_of_not_lt (h' ∘ Nat.le_of_lt)) hxs)
      case _ h => exact .cons (Nat.ge_of_not_lt (h ∘ Nat.le_of_lt)) (.cons hx hxs)
    case cons hy _ ihy =>
      simp
      split
      case _ h =>
        split
        case _ h' => simp [h'] at ihx; exact .cons hx ihx
        case _ h' => simp [h'] at ihx; exact .cons h ihx
      case _ h =>
        have : ¬_ := h ∘ Nat.le_trans hx
        simp [this] at ihx
        split
        case _ h' =>
          apply Sorted.cons (Nat.ge_of_not_lt (h ∘ Nat.le_of_lt))
          split
          case _ h'' =>
            simp [h''] at ihx
            cases ihx
            case cons ihx => exact .cons hx ihx
          case _ h'' =>
            simp [h''] at ihx
            cases ihx
            case cons ihx => exact .cons h' ihx
        case _ h' =>
          have : ¬_ := h' ∘ Nat.le_trans hx
          simp [h', this] at ihx ihy
          cases ihx
          case cons ihx => exact .cons hy (ihy ihx)

theorem sorted_msort : ∀ l, Sorted (msort l)
  | [] => .nil
  | [x] => .singleton
  | x :: x' :: xs =>
    have := (length_partition x x' xs).1
    have := (length_partition x x' xs).2
    by
      simp
      apply sorted_merge
      apply sorted_msort
      apply sorted_msort
termination_by _ l => l.length
