import Std.Data.List.Lemmas

namespace List

theorem Mem.of_mem_head : x ∈ head? l → x ∈ l := by
  intro; cases l <;> simp_all

theorem Mem.of_mem_last : x ∈ last' l → x ∈ l := by
  match l with
  | [] => simp
  | [_] => intro; simp_all
  | _ :: _ :: l => intro h; have := of_mem_last (l := _ :: l) h; simp_all

@[simp]
theorem last'_append_cons : (l ++ x :: r).last' = (x :: r).last' :=
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: l => last'_append_cons (l := _ :: l)

@[simp]
theorem head?_append_cons : (l ++ x :: r).head? = (l ++ [x]).head? := by
  cases l <;> rfl

variable {α : Type u} {R : α → α → Prop}

@[simp] theorem Chain_nil_def : Chain R a [] ↔ True := ⟨λ | .nil => ⟨⟩, λ | ⟨⟩ => .nil⟩
@[simp] theorem Chain_cons_def : Chain R a (b :: l) ↔ R a b ∧ Chain R b l := ⟨λ | .cons h h' => ⟨h, h'⟩, λ ⟨h, h'⟩ => .cons h h'⟩

attribute [local simp] Chain'

theorem Chain'_cons : Chain' R (x :: l) ↔ (∀ y ∈ l.head?, R x y) ∧ Chain' R l := by
  cases l <;> simp

theorem Chain'.cons (hx : ∀ y ∈ l.head?, R x y) (hl : Chain' R l) : Chain' R (x :: l) :=
  Chain'_cons.mpr ⟨hx, hl⟩

theorem Chain'_append : Chain' R (l ++ r) ↔ Chain' R l ∧ (∀ x ∈ l.last', ∀ y ∈ r.head?, R x y) ∧ Chain' R r := by
  match l with
  | [] => simp
  | [x] => simp; exact Chain'_cons
  | x :: y :: l => simp [and_assoc]; intro; exact Chain'_append (l := y :: l)

theorem Chain'.append (hl : Chain' R l) (hlr : ∀ x ∈ l.last', ∀ y ∈ r.head?, R x y) (hr : Chain' R r) : Chain' R (l ++ r) :=
  Chain'_append.mpr ⟨hl, hlr, hr⟩

end List

inductive BTree (α : Type u)
  | leaf
  | node (l : BTree α) (x : α) (r : BTree α)

namespace BTree

variable {α : Type u}

@[simp]
def toList : BTree α → List α
  | leaf       => []
  | node l x r => toList l ++ x :: toList r

@[simp]
def size : BTree α → Nat
  | leaf       => 0
  | node l _ r => size l + size r + 1

@[simp]
def height : BTree α → Nat
  | leaf       => 0
  | node l _ r => max (height l) (height r) + 1

private def toList.impl : BTree α → List α :=
  toList []
where
  toList a
  | leaf       => a
  | node l x r => toList (x :: toList a r) l

@[csimp]
private theorem toList.eq_impl : @toList = @impl := by
  funext α t
  suffices ∀ a t, toList t ++ a = impl.toList a t from
    (List.append_nil .. ▸ this [] t :)
  intro a t
  induction t generalizing a with
  | leaf => rfl
  | node _ _ _ ihl ihr =>
    dsimp [toList, impl.toList]
    rw [← ihr, ← ihl, List.append_assoc]
    rfl

@[simp]
def front? : BTree α → Option α
  | leaf          => none
  | node leaf x _ => some x
  | node l    _ _ => front? l

@[simp]
def back? : BTree α → Option α
  | leaf          => none
  | node _ x leaf => some x
  | node _ _ r    => back? r

theorem head?_toList : (t : BTree α) → t.toList.head? = t.front?
  | leaf               => rfl
  | node leaf      _ _ => rfl
  | node (node ..) _ _ => by simp; rw [← List.head?_append_cons]; exact head?_toList (node ..)

theorem last'_toList : (t : BTree α) → t.toList.last' = t.back?
  | leaf               => rfl
  | node _ _ leaf      => by simp
  | node _ _ (node ..) => by simp; rw [← List.last'_append_cons]; exact last'_toList (node ..)

variable [LT α]

theorem leaf_lt (x : α) : ∀ y ∈ leaf.back?, y < x := λ _ hy => nomatch hy
theorem leaf_gt (x : α) : ∀ y ∈ leaf.front?, x < y := λ _ hy => nomatch hy

inductive Bst : BTree α → Prop
  | leaf : Bst leaf
  | node {l x r} : (∀ y ∈ l.back?, y < x) → (∀ y ∈ r.front?, x < y) → Bst l → Bst r → Bst (node l x r)

theorem Bst_iff_Chain_toList {t : BTree α} : Bst t ↔ t.toList.Chain' LT.lt := by
  constructor
  . intro h
    induction h with
    | leaf => dsimp!
    | node hlx hrx _ _ ihl ihr =>
      dsimp
      refine .append ihl ?_ <| .cons (head?_toList _ ▸ hrx) ihr
      simp
      exact last'_toList _ ▸ hlx
  . intro h
    induction t with
    | leaf => constructor
    | node _ _ _ ihl ihr =>
      simp [List.Chain'_append, List.Chain'_cons] at h
      constructor
      . exact last'_toList _ ▸ h.2.1
      . exact head?_toList _ ▸ h.2.2.1
      . exact ihl h.1
      . exact ihr h.2.2.2

variable [@DecidableRel α LT.lt]

instance instDecidableBst : (t : BTree α) → Decidable (Bst t)
  | leaf => isTrue .leaf
  | node l _ r =>
    if hlx : _
    then
      if hrx : _
      then
        match instDecidableBst l with
        | isTrue hl =>
          match instDecidableBst r with
          | isTrue hr => isTrue <| .node hlx hrx hl hr
          | isFalse hr => isFalse λ | .node _ _ _ hr' => hr hr'
        | isFalse hl => isFalse λ | .node _ _ hl' _ => hl hl'
      else isFalse λ | .node _ hrx' _ _ => hrx hrx'
    else isFalse λ | .node hlx' _ _ _ => hlx hlx'

@[simp]
def find (y : α) : BTree α → Bool
  | leaf => false
  | node l x r => if y < x then find y l else if x < y then find y r else true

def insert (y : α) : BTree α → BTree α
  | leaf => node leaf y leaf
  | node l x r => if y < x then node (insert y l) x r else if x < y then node l x (insert y r) else node l x r

theorem insert_lt {t : BTree α} (hyz : y < z) (hlz : ∀ x ∈ t.back?, x < z) : ∀ x ∈ (t.insert y).back?, x < z := by
  induction t with
  | leaf => simp [hyz]
  | node _ _ r _ ihr =>
    unfold insert
    split
    . cases r <;> exact hlz
    . split
      . cases r with
        | leaf => simp [hyz]
        | node =>
          specialize ihr hlz
          unfold insert at ihr ⊢
          split
          next h => rw [if_pos h] at ihr; exact ihr
          next h =>
            rw [if_neg h] at ihr; split
            next h => rw [if_pos h] at ihr; exact ihr
            next h => rw [if_neg h] at ihr; exact ihr
      . exact hlz

theorem insert_gt {t : BTree α} (hyz : z < y) (hlz : ∀ x ∈ t.front?, z < x) : ∀ x ∈ (t.insert y).front?, z < x := by
  induction t with
  | leaf => simp [hyz]
  | node l _ _ ihl =>
    unfold insert
    split
    . cases l with
      | leaf => simp [hyz]
      | node =>
        specialize ihl hlz
        unfold insert at ihl ⊢
        split
        next h => rw [if_pos h] at ihl; exact ihl
        next h =>
          rw [if_neg h] at ihl; split
          next h => rw [if_pos h] at ihl; exact ihl
          next h => rw [if_neg h] at ihl; exact ihl
    . split
      . cases l <;> exact hlz
      . exact hlz

theorem insert_Bst {t : BTree α} (h : Bst t) : Bst (t.insert y) := by
  induction h with
  | leaf =>
    refine .node ?_ ?_ .leaf .leaf
    . simp
    . simp
  | node hlx hrx hl hr =>
    unfold insert
    split
    next h => exact .node (insert_lt h hlx) hrx (insert_Bst hl) hr
    next =>
      split
      next h => exact .node hlx (insert_gt h hrx) hl (insert_Bst hr)
      next => exact .node hlx hrx hl hr

theorem Bst.rotate_left {r : BTree α} : Bst (.node l x (.node c y r)) → Bst (.node (.node l x c) y r)
  | .node hlx hcyrx hl (.node _   hry     .leaf     hr) => .node (by simp [*]) hry (.node hlx (leaf_gt x) hl .leaf) hr
  | .node hlx hcyrx hl (.node hcy hry hc@(.node ..) hr) => .node  hcy          hry (.node hlx  hcyrx      hl  hc  ) hr

theorem Bst.rotate_right {r : BTree α} : Bst (.node (.node l x c) y r) → Bst (.node l x (.node c y r))
  | .node hlxcy hry (.node hlx _   hl     .leaf    ) hr => .node hlx (by simp [*]) hl (.node (leaf_lt y) hry .leaf hr)
  | .node hlxcy hry (.node hlx hcx hl hc@(.node ..)) hr => .node hlx  hcx          hl (.node  hlxcy      hry  hc   hr)

variable (l r : Nat) in
inductive Close : Prop
  | balanced : l = r → Close
  | left : l = r + 1 → Close
  | right : l + 1 = r → Close

inductive Avl : BTree α → Prop
  | leaf : Avl leaf
  | node : Close l.height r.height → Avl l → Avl r → Avl (node l x r)

def rebalance (l : BTree α) (x : α) (r : BTree α) : BTree α × α × BTree α :=
  if _ : r.height + 1 < l.height
  then
    match l with
    | node l₁ x₁ r₁ =>
      if _ : l₁.height < r₁.height
      then
        match r₁ with
        | node l₂ x₂ r₂ => (node l₁ x₁ l₂, x₂, node r₂ x r)
      else (l₁, x₁, node r₁ x r)
  else
    if _ : l.height + 1 < r.height
    then
      match r with
      | node l₁ x₁ r₁ =>
        if _ : r₁.height < l₁.height
        then
          match l₁ with
          | node l₂ x₂ r₂ => (node l x l₂, x₂, node r₂ x₁ r₁)
        else (node l x l₁, x₁, r₁)
    else (l, x, r)

#check Nat.sub_le_sub_left

theorem Close_rebalance {l} {x : α} {r} : let (l', _, r') := rebalance l x r; Close l'.height r'.height := by
  dsimp
  unfold rebalance
  split
  case' inr =>
    split
    case inr h₁ h₂ =>
      dsimp
      generalize height l = l at h₁ h₂
      generalize height r = r at h₁ h₂
      cases Nat.le_of_not_lt h₁ with
      | refl => exact .left rfl
      | step h₁ =>
      cases Nat.le_of_not_lt h₂ with
      | refl => exact .right rfl
      | step h₂ => exact .balanced (Nat.le_antisymm h₁ h₂)
  . split
    next l₁ x₁ r₁ _ _ =>
    split
    . sorry
    . dsimp
      sorry
  . sorry

variable (y : α) in
def insertAvl' : BTree α → BTree α × α × BTree α
  | leaf => (leaf, y, leaf)
  | node l x r =>
    if y < x
    then
      let (l', x', r') := insertAvl' l
      rebalance (node l' x' r') x r
    else
      if x < y
      then
        let (l', x', r') := insertAvl' r
        rebalance l x (node l' x' r')
      else (l, x, r)

def insertAvl (y : α) (t : BTree α) : BTree α :=
  let (l, x, r) := insertAvl' y t
  node l x r

end BTree

variable (α : Type u) [LT α] in
def Bst := { t : BTree α // t.Bst }

namespace Bst

variable {α : Type u} [LT α]

def empty : Bst α := ⟨.leaf, .leaf⟩

def singleton (x : α) : Bst α := ⟨.node .leaf x .leaf, .node (BTree.leaf_lt x) (BTree.leaf_gt x) .leaf .leaf⟩

def size (t : Bst α) : Nat := t.val.size

variable [@DecidableRel α LT.lt]

def find (x : α) (t : Bst α) : Bool := t.val.find x

def insert (x : α) (t : Bst α) : Bst α := ⟨t.val.insert x, BTree.insert_Bst t.property⟩

end Bst

def foo : Bst Nat := ⟨.node (.node (.node .leaf 0 .leaf) 2 (.node .leaf 3 .leaf)) 4 (.node (.node .leaf 5 .leaf) 6 (.node .leaf 7 .leaf)), by decide⟩
#eval foo.1.toList

#eval foo.insert 1 |>.1.toList

#reduce BTree.leaf |>.insertAvl 0 |>.insertAvl 1 |>.insertAvl 2 |>.insertAvl 3 |>.insertAvl 4 |>.insertAvl 5 |>.insertAvl 6 |>.insertAvl 7

/-
@[simp]
def Bst' : BTree α → Prop
  | leaf => True
  | node l x r => l.lt x ∧ r.gt x ∧ Bst l ∧ Bst r

@[simp]
example : (t : BTree α) → Bst t ↔ Bst' t
  | leaf => ⟨λ | .leaf => .intro, λ | .intro => .leaf⟩
  | node .. => ⟨λ | .node hxl hxr hl hr => ⟨hxl, hxr, hl, hr⟩, λ | ⟨hxl, hxr, hl, hr⟩ => .node hxl hxr hl hr⟩
-/
