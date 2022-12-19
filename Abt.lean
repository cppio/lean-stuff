import Rec
import Std.Data.List.Lemmas

private def True.casesOn' {motive : True → Sort u} t (intro : motive intro) : motive t := intro
@[csimp] theorem True.casesOn_eq' : @True.casesOn = @True.casesOn' := by
  funext motive t intro
  rfl

def String.joinSep l sep := join (List.intersperse sep l)

theorem Nat.le_trans_lt {n m k : Nat} (h₁ : n ≤ m) (h₂ : m < k) : n < k :=
  Nat.le_trans (succ_le_succ h₁) h₂

theorem Nat.le_of_le_add_right {n m k : Nat} (h : n + k ≤ m) : n ≤ m := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (Nat.le_of_succ_le_succ h.step)

theorem Nat.le_of_le_add_left {n m k : Nat} (h : k + n ≤ m) : n ≤ m := by
  rw [Nat.add_comm] at h
  exact Nat.le_of_le_add_right h

theorem Nat.lt_of_lt_add_left {n m k : Nat} (h : k + n ≤ m) : n ≤ m := Nat.le_of_le_add_left h

theorem Nat.lt_of_lt_add_right {n m k : Nat} (h : n + k < m) : n < m := by
  rw [Nat.add_comm] at h
  exact Nat.lt_of_lt_add_left h

theorem lt_of_compare_lt {x y : α} [LT α] [Decidable (x < y)] [DecidableEq α] (h : compareOfLessAndEq x y = .lt) : x < y := by
  unfold compareOfLessAndEq at h
  split at h
  . assumption
  . split at h
    . contradiction
    . contradiction

theorem eq_of_compare_eq {x y : α} [LT α] [Decidable (x < y)] [DecidableEq α] (h : compareOfLessAndEq x y = .eq) : x = y := by
  unfold compareOfLessAndEq at h
  split at h
  . contradiction
  . split at h
    . assumption
    . contradiction

theorem gt_of_compare_gt {x y : Nat} (h : compare x y = .gt) : x > y := by
  dsimp [compare, compareOfLessAndEq] at h
  split at h
  . contradiction
  . split at h
    . contradiction
    . apply Nat.gt_of_not_le
      intro h
      cases Nat.eq_or_lt_of_le h
      . contradiction
      . contradiction

theorem Nat.le_max₁ (x y : Nat) : x ≤ max x y := by
  rw [Nat.max_def]
  split
  . assumption
  . exact .refl

theorem Nat.le_max₂ (x y : Nat) : y ≤ max x y := by
  rw [Nat.max_def]
  split
  . exact .refl
  . rename_i h
    exact Nat.ge_of_not_lt (h ∘ Nat.le_of_lt)

inductive List.Suffix {α : Type u} : List α → List α → Prop
  | refl : Suffix l l
  | cons x : Suffix l₁ l₂ → Suffix l₁ (x :: l₂)

theorem List.Suffix.nil : {l : List α} → Suffix [] l
  | [] => .refl
  | x :: _ => .cons x nil

theorem List.Suffix.tail : Suffix (x :: l₁) l₂ → Suffix l₁ l₂
  | refl => cons x refl
  | cons y s => cons y <| tail s

theorem List.mem_of_mem_suffix (m : x ∈ l₁) : Suffix l₁ l₂ → x ∈ l₂
  | .refl => m
  | .cons y s => .tail y <| mem_of_mem_suffix m s

def List.recSuffix (l : List α) {motive : ∀ l', l'.Suffix l → Sort _}
  (nil : motive [] .nil)
  (cons : ∀ x xs h, motive xs h.tail → motive (x :: xs) h)
: motive l .refl :=
  match l with
  | [] => nil
  | x :: xs => cons x xs .refl (@recSuffix α xs (motive · <| .cons _ ·) nil (cons · · <| .cons _ ·))

variable {τ : Type u} (α : τ → Sort v) in
inductive DList : List τ → Sort _
  | nil : DList []
  | cons : α t → DList ts → DList (t :: ts)

#compile List
#compile DList

namespace DList

scoped syntax "⟦" term,* "⟧" : term

macro_rules
  | `(⟦⟧)          => ``(nil)
  | `(⟦$x⟧)        => ``(cons $x ⟦⟧)
  | `(⟦$x, $xs,*⟧) => ``(cons $x ⟦$xs,*⟧)

@[app_unexpander nil]
protected def nilUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_) => ``(⟦⟧)

@[app_unexpander cons]
protected def consUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $x ⟦⟧)      => ``(⟦$x⟧)
  | `($_ $x ⟦$xs,*⟧) => ``(⟦$x, $xs,*⟧)
  | _                => throw ()

variable {τ : Type u} {α : τ → Sort v} {β : Sort w}

def recSuffix
  {ts : List τ} {motive : ∀ ts', ts'.Suffix ts → DList α ts' → Sort w}
  (nil : motive [] .nil nil)
  (cons : ∀ {t ts'} x xs h, motive ts' h.tail xs → motive (t :: ts') h (cons x xs))
  (xs : DList α ts)
: motive ts .refl xs :=
  match ts, xs with
  | _, .nil => nil
  | _, .cons x xs => cons x xs .refl (@recSuffix _ (motive · <| .cons _ ·) nil (cons · · <| .cons _ ·) xs)

/-
variable
  {motive : ∀ ts, DList α ts → Sort w}
  (nil : motive [] nil) in
@[simp]
def recMem {ts : List τ} (cons : ∀ {t ts'} x xs, t ∈ ts → motive ts' xs → motive (t :: ts') (cons x xs)) : ∀ xs, motive ts xs
  | .nil => nil
  | .cons x xs => cons x xs (.head _) (recMem (cons · · <| .tail _ ·) xs)
-/

variable (f : ∀ t, α t) in
@[simp]
def mk : ∀ ts, DList α ts
  | [] => nil
  | t :: ts => cons (f t) (mk ts)

@[simp]
def mkMem : ∀ ts, (∀ {t}, t ∈ ts → α t) → DList α ts
  | [], _ => nil
  | t :: ts, f => cons (f (.head ts)) (mkMem ts λ h => f (.tail t h))

variable {α' : τ → Sort v'} (f : ∀ {t}, α t → α' t) in
@[simp]
def map : DList α ts → DList α' ts
  | nil => nil
  | cons x xs => cons (f x) (map xs)

variable {α' : τ → Sort v'} in
@[simp]
def mapMem (f : ∀ {t}, t ∈ ts → α t → α' t) : DList α ts → DList α' ts
  | nil => nil
  | cons x xs => cons (f (.head _) x) (mapMem (λ h => f (.tail _ h)) xs)

/-
variable {α₁ : τ → Sort v₁} {α₂ : τ → Sort v₂} in
@[simp]
theorem map_map (f : ∀ {t}, α₁ t → α₂ t) (g : ∀ {t}, α t → α₁ t) {ts} : ∀ xs, @map τ α₁ α₂ @f ts (@map τ α α₁ @g ts xs) = @map τ α α₂ (f <| g ·) ts xs
  | nil => rfl
  | cons .. => congrArg _ (map_map ..)
-/

/-
variable {α₁ : τ → Sort v₁} {α₂ : τ → Sort v₂} in
@[simp]
theorem map_mapMem (f : ∀ {t}, α₁ t → α₂ t) {ts} (g : ∀ {t}, t ∈ ts → α t → α₁ t) (xs : DList α ts) : @map τ α₁ α₂ @f ts (@mapMem τ α α₁ ts @g xs) = @mapMem τ α α₂ ts (f <| g · ·) xs :=
  match ts, xs with
  | _, nil => rfl
  | _, cons .. => congrArg _ (map_mapMem ..)
-/

variable (f : ∀ {t}, α t → β → β) (y : β) in
@[simp]
def foldr : DList α ts → β
  | nil => y
  | cons x xs => f x (foldr xs)

variable (f : ∀ {t}, β → α t → β) in
@[simp]
def foldl (y : β) {ts} : DList α ts → β
  | nil => y
  | cons x xs => foldl (f y x) xs

variable {α : Type v} in
@[simp]
def toList {ts : List τ} : DList (λ _ => α) ts → List α
  | nil => []
  | cons x xs => x :: toList xs

instance instToString {α : τ → Type v} [∀ t, ToString (α t)] {ts} : ToString (DList α ts) where
  toString xs := xs.map toString |>.toList.toString

instance instInhabited [∀ t, Inhabited (α t)] : Inhabited (DList α ts) where
  default := default' ts
where
  default'
    | [] => .nil
    | _ :: ts => .cons default (default' ts)

end DList

structure Var {S : Sort u} (s : S) where
  x : Nat
  deriving Inhabited

namespace Var

variable {S : Sort u} {s : S}

instance instDecidableEq : DecidableEq (Var s)
  | ⟨x⟩, ⟨y⟩ =>
    if h : x = y
    then isTrue (congrArg Var.mk h)
    else isFalse (h ∘ congrArg Var.x)

instance instOfNat : OfNat (Var s) n := ⟨⟨n⟩⟩

protected def toString : Var s → String
  | ⟨x⟩ => ⟨toString x []⟩
where
  toString x l :=
    let l := Char.ofNat ('a'.toNat + x % 26) :: l
    match h : x / 26 with
    | 0 => l
    | q + 1 =>
      have := h ▸ Nat.div_le_self ..
      toString q l

instance instToString : ToString (Var s) := ⟨Var.toString⟩

def ofString : String → Var s
  | ⟨l⟩ =>
    ⟨l.foldl (λ x c => (x + 1) * 26 + (c.toNat - 'a'.toNat).min 25) 0 - 26 ^ l.length⟩

instance instCoeString : Coe String (Var s) := ⟨ofString⟩

end Var
abbrev isBound (O : List (List S × S) → S → Type) s :=
  ∃ (si t : _) (_ : O si t) (b : _), b ∈ si.map Prod.fst ∧ s ∈ b

variable {S : Type} (O : List (List S × S) → S → Type) in
inductive Abt : S → Type
  | bvar s (n : Nat) : Abt s
  | var (v : isBound O s) (x : Var s) : Abt s
  | op (o : O si s) (ai : DList (Abt ·.2) si) : Abt s

#compile mutual Abt

namespace Abt

variable {S : Type} {O : List (List S × S) → S → Type}

instance instInhabited : Inhabited (Abt O s) := ⟨.bvar s 0⟩

def subst [DecidableEq S] {s} (a : Abt O s) (x : Var s) : ∀ {t}, Abt O t → Abt O t := @rec S O (λ s _ => Abt O s) (λ si _ => DList (Abt O ·.2) si)
  bvar
  (λ {t} v y => if h : t = s then if h ▸ y = x then h ▸ a else var v y else var v y)
  (λ o _ => op o)
  DList.nil
  (λ _ _ => DList.cons (τ := _ × S) (α := (Abt O ·.2)))

variable [DecidableEq S]

variable (s : S) in
protected def bindCount : List S → Nat
  | [] => 0
  | t :: ts => Abt.bindCount ts + if s = t then 1 else 0

def bind {s : S} (x : Var s) : ∀ {t}, Abt O t → Nat → Abt O t := @rec S O (λ s _ => Nat → Abt O s) (λ si _ => Nat → DList (Abt O ·.2) si)
  (λ t m _ => bvar t m)
  (λ {t} v y n => if h : t = s then if h ▸ y = x then bvar t n else var v y else var v y)
  (λ o _ ai' n => op o (ai' n))
  (λ _ => .nil)
  (λ {b _} _ _ f fi n => .cons (f (n + Abt.bindCount s b.1)) (fi n))

def unbind (a : Abt O s) : ∀ {t}, Abt O t → Nat → Abt O t := @rec S O (λ s _ => Nat → Abt O s) (λ si _ => Nat → DList (Abt O ·.2) si)
  (λ t m n => if h : t = s then match compare m n with | .lt => bvar t m | .eq => h ▸ a | .gt => bvar t (m - 1) else bvar t m)
  (λ v x _ => var v x)
  (λ o _ ai' n => op o (ai' n))
  (λ _ => .nil)
  (λ {b _} _ _ f fi n => .cons (f (n + Abt.bindCount s b.1)) (fi n))

def unbind' (a : Abt O s) : ∀ {si : List (List S × S)}, DList (Abt O ·.2) si → Nat → DList (Abt O ·.2) si := @rec_1 S O (λ s _ => Nat → Abt O s) (λ si _ => Nat → DList (Abt O ·.2) si)
  (λ t m n => if h : t = s then match compare m n with | .lt => bvar t m | .eq => h ▸ a | .gt => bvar t (m - 1) else bvar t m)
  (λ v x _ => var v x)
  (λ o _ ai' n => op o (ai' n))
  (λ _ => .nil)
  (λ {b _} _ _ f fi n => .cons (f (n + Abt.bindCount s b.1)) (fi n))

def wellFormed : ∀ {s}, Abt O s → (_ : S → Nat := λ _ => 0) → Prop := @rec S O _ (λ _ _ => _ → _)
  (λ s n N => n < N s)
  (λ _ _ _ => True)
  (λ _ _ hai N => hai N)
  (λ _ => True)
  (λ {b _} _ _ ha hai N => ha (λ s => N s + Abt.bindCount s b.1) ∧ hai N)

def wellFormed' : {si : List (List S × S)} → DList (Abt O ·.2) si → (_ : S → Nat := λ _ => 0) → Prop := @rec_1 S O (λ _ _ => _ → _) _
  (λ s n N => n < N s)
  (λ _ _ _ => True)
  (λ _ _ (hai : _ → _) N => hai N)
  (λ _ => True)
  (λ {b _} _ _ ha hai N => ha (λ s => N s + Abt.bindCount s b.1) ∧ hai N)

@[simp]
theorem wellFormed_op {o : O si s} : wellFormed (.op o ai) N = wellFormed' ai N := rfl

@[simp]
theorem wellFormed'_cons {b : _ × _} {a : Abt O b.2} : wellFormed' (.cons a ai) N = (wellFormed a (λ s => N s + Abt.bindCount s b.1) ∧ wellFormed' ai N) := rfl

def wellFormed_zip {si : List (List S × S)} : (ai : DList (Abt O ·.2) si) → wellFormed' ai N → DList (λ b => { x : Abt O b.2 // x.wellFormed λ s => N s + Abt.bindCount s b.1 }) si
  | .nil, _ => .nil
  | .cons a ai, wf => .cons ⟨a, wf.1⟩ (wellFormed_zip ai wf.2)

theorem wellFormed_weaken (h : ∀ s, N s ≤ N' s) {s} : {a : Abt O s} → wellFormed a N → wellFormed a N'
  | bvar s _, wf => Nat.le_trans wf (h s)
  | var .., wf => wf
  | op _ ai, wf => weaken ai wf
where
  weaken {_}
  | .nil, wf => wf
  | .cons _ ai, wf => ⟨wellFormed_weaken (λ s => Nat.add_le_add_right (h s) _) wf.1, weaken ai wf.2⟩

theorem wellFormed_bind (x : Var s) {n} (h : n < N s) {t} : {a : Abt O t} → wellFormed a N → wellFormed (bind x a n) N
  | bvar .., wf => wf
  | var .., wf => by
    dsimp [bind]
    split
    . rename_i h'
      split
      . exact h' ▸ h
      . exact wf
    . exact wf
  | op _ ai, wf => bind' ai wf
where
  bind' {_}
  | .nil, wf => wf
  | .cons _ ai, wf => ⟨wellFormed_bind x (Nat.add_lt_add_right h _) wf.1, bind' ai wf.2⟩

theorem wellFormed_unbind {a : Abt O s} (h : wellFormed a N) {n} (h' : n ≤ N s) : {a' : Abt O t} → wellFormed a' (λ u => if u = s then N u + 1 else N u) → wellFormed (unbind a a' n) N
  | bvar _ m, wf => by
    dsimp [unbind]
    split <;> rename_i h
    . cases h
      split
      . rename_i h''
        exact Nat.le_trans (lt_of_compare_lt h'' :) h'
      . exact h
      . cases m with
        | zero =>
          rename_i h
          dsimp [compare, compareOfLessAndEq] at h
          split at h
          . cases h
          . split at h
            . cases h
            . cases Nat.eq_or_lt_of_le (Nat.zero_le n)
              . contradiction
              . contradiction
        | succ m =>
          simp [wellFormed] at wf
          exact Nat.lt_of_succ_lt_succ wf
    . simp [wellFormed, h] at wf
      exact wf
  | var .., wf => wf
  | op _ ai, wf => unbind' ai wf
where
  unbind' {_}
  | .nil, wf => wf
  | .cons _ ai, wf => ⟨by
    apply wellFormed_unbind _ (Nat.add_le_add_right h' _)
    . have : wellFormed _ _ := wf.1
      dsimp at this
      suffices _ = _ by
        apply (congrArg _ this).mp
        assumption
      funext u
      split
      . apply Nat.add_right_comm
      . rfl
    . exact wellFormed_weaken (λ _ => Nat.le_add_right ..) h,
  unbind' ai wf.2⟩

theorem wellFormed_subst {a : Abt O s} (wfa : wellFormed a) (x : Var s) : {b : Abt O t} → wellFormed b N → wellFormed (subst a x b) N
  | bvar .., wfb => wfb
  | var .., wfb => by
    dsimp [subst]
    split
    next h =>
      cases h
      dsimp
      split
      . exact wellFormed_weaken (λ _ => Nat.zero_le _) wfa
      . exact wfb
    . exact wfb
  | op _ ai, wfb => subst' ai wfb
where
  subst' {_}
  | .nil, wfb => wfb
  | .cons b ai, wfb => ⟨wellFormed_subst wfa x wfb.1, subst' ai wfb.2⟩

def freeIn {s : S} (x : Var s) : ∀ {t}, Abt O t → Prop := @rec S O _ _
  (λ _ _ => True)
  (λ {t} _ y => (h : t = s) → h ▸ y ≠ x)
  (λ _ _ hai => hai)
  True
  (λ _ _ ha hai => ha ∧ hai)

def freeIn' {s : S} (x : Var s) : {si : List (List S × S)} → DList (Abt O ·.2) si → Prop := @rec_1 S O (λ _ _ => _) _
  (λ _ _ => True)
  (λ {t} _ y => (h : t = s) → h ▸ y ≠ x)
  (λ _ _ hai => hai)
  True
  (λ _ _ ha hai => ha ∧ hai)

@[simp]
theorem freeIn_op {s : S} : freeIn x (.op o ai) = freeIn' x ai := rfl

theorem bind_unbind (v : isBound O s) (x : Var s) n (h : n + 1 = N s) : (a : Abt O t) → wellFormed a N → freeIn x a → bind x (unbind (var v x) a n) n = a
  | bvar t m, wf, _ => by
    dsimp [wellFormed] at wf
    dsimp [unbind]
    split
    . rename_i h
      cases h
      split
      . rfl
      . rename_i h
        have := eq_of_compare_eq h
        simp [bind, this]
      . rw [← h] at wf
        rename_i h
        cases Nat.not_succ_le_self _ (Nat.le_trans wf (gt_of_compare_gt h))
    . rfl
  | var _ y, _, hx => by
    dsimp [unbind, bind]
    split
    . rename_i h
      cases h
      split
      . rename_i h
        cases hx rfl h
      . rfl
    . rfl
  | op o ai, wf, hx => congrArg (op o) <| thm' ai wf hx
where
  thm' {_}
  | .nil, _, _ => rfl
  | .cons a ai, wf, hx => by
    apply congr (congrArg _ _) (thm' ai wf.2 hx.2)
    apply bind_unbind v x (n + Abt.bindCount s _) _ a wf.1 hx.1
    rw [Nat.add_right_comm]
    exact congrArg (· + _) h

def op' (o : O si s) (ai : DList (λ b => DList Var b.1 × Abt O b.2) si) : Abt O s :=
  .op o <| ai.map λ a => a.1.foldr (β := _ × _) (λ {t} x (a, n) => (bind x a (n t), λ u => if u = t then n u + 1 else n u)) (a.2, λ _ : S => 0) |>.1

def free (s : S) : ∀ {t}, Abt O t → Var s := @rec S O _ _
  (λ _ _ => ⟨0⟩)
  (λ {t} _ x => if t = s then ⟨x.1 + 1⟩ else ⟨0⟩)
  (λ _ _ hai => hai)
  ⟨0⟩
  (λ _ _ x y => ⟨max x.1 y.1⟩)

def free' (s : S) : {si : List (List S × S)} → DList (Abt O ·.2) si → Var s := @rec_1 S O (λ _ _ => _) _
  (λ _ _ => ⟨0⟩)
  (λ {t} _ x => if t = s then ⟨x.1 + 1⟩ else ⟨0⟩)
  (λ _ _ hai => hai)
  ⟨0⟩
  (λ _ _ x y => ⟨max x.1 y.1⟩)

@[simp]
theorem free_op {s : S} : free s (.op o ai) = free' s ai := rfl

theorem freeIn_free' (s : S) (x : Var s) : (a : Abt O t) → (free s a).1 ≤ x.1 → freeIn x a
  | bvar .., _ => trivial
  | var .., hx => by
    intro h
    cases h
    dsimp [free] at hx
    rw [if_pos rfl] at hx
    intro h
    cases h
    apply Nat.not_succ_le_self
    exact hx
  | op _ ai, hx => h ai hx
where
  h {si : List (List S × S)} : (ai : DList (Abt O <| Prod.snd ·) si) → (free' s ai).1 ≤ x.1 → freeIn' x ai
  | .nil, _ => trivial
  | .cons a ai, hx => ⟨freeIn_free' s x a <| Nat.le_trans (Nat.le_max₁ ..) hx, h ai <| Nat.le_trans (Nat.le_max₂ ..) hx⟩

theorem freeIn_free (s : S) (a : Abt O t) : freeIn (free s a) a := freeIn_free' s _ a .refl

def unop' : ∀ {si : List S}, DList (isBound O) si → Abt O s → DList Var si × Abt O s
  | [], _ => (.nil, ·)
  | s' :: si, .cons v vs => λ a =>
    let x := a.free s'
    let (xs, a) := unop' vs (unbind (var v x) a (Abt.bindCount s' si))
    (.cons x xs, a)

def unop (o : O si s) : DList (Abt O ·.2) si → DList (λ b => DList Var b.1 × Abt O b.2) si :=
  .mapMem (unop' <| .mkMem _ λ h => ⟨si, s, o, _, List.mem_map_of_mem Prod.fst ·, h⟩)

protected partial def toString [∀ si s, ToString (O si s)] {s} : Abt O s → String
  | .bvar _ x => "#" ++ toString x
  | .var _ x => x.toString
  | .op o .nil => toString o
  | .op o ai =>
    toString o ++ "(" ++ .joinSep (unop o ai |>.map @λ
      | (_, _), (.nil, a) => a.toString
      | (_, _), (xi, a) => .joinSep (xi.map Var.toString).toList ", " ++ ". " ++ a.toString
    ).toList "; " ++ ")"

instance instToString [∀ si s, ToString (O si s)] {s} : ToString (Abt O s) := ⟨Abt.toString⟩

instance instDecidableEq [∀ si s, DecidableEq (O si s)] : DecidableEq (Abt O s)
  | .bvar _ n, .bvar _ m => if h : n = m then h ▸ isTrue rfl else isFalse (h ∘ bvar.inj)
  | .var _ x, .var _ y => if h : x = y then h ▸ isTrue rfl else isFalse (h ∘ var.inj)
  | .op (si := si) o ai, .op (si := si') o' ai' =>
    if h : si = si'
    then by cases h; exact
      if h : o = o'
      then h ▸
        match op ai ai' with
        | isTrue h => h ▸ isTrue rfl
        | isFalse h => isFalse (h ∘ eq_of_heq ∘ And.right ∘ And.right ∘ op.inj)
      else isFalse (h ∘ eq_of_heq ∘ And.left ∘ And.right ∘ op.inj)
    else isFalse (h ∘ And.left ∘ op.inj)
  | .bvar .., .var .. => isFalse (nomatch ·)
  | .bvar .., .op .. => isFalse (nomatch ·)
  | .var .., .bvar .. => isFalse (nomatch ·)
  | .var .., .op .. => isFalse (nomatch ·)
  | .op .., .bvar .. => isFalse (nomatch ·)
  | .op .., .var .. => isFalse (nomatch ·)
where
  op {si : List (List S × S)} : DecidableEq (DList (Abt O ·.2) si)
    | .nil, .nil => isTrue rfl
    | .cons a ai, .cons a' ai' =>
      match instDecidableEq a a' with
      | isTrue h => h ▸
        match op ai ai' with
        | isTrue h => h ▸ isTrue rfl
        | isFalse h => isFalse (h ∘ And.right ∘ DList.cons.inj)
      | isFalse h => isFalse (h ∘ And.left ∘ DList.cons.inj)

variable (Γ : ∀ {s : S}, Var s → Prop)

def closed : ∀ {s}, Abt O s → Prop := @rec S O _ _
  (λ _ _ => True)
  (λ _ => Γ)
  (λ _ _ hai => hai)
  True
  (λ _ _ => And)

def closed' : ∀ {si : List (List S × S)}, DList (Abt O ·.2) si → Prop := @rec_1 S O (λ _ _ => _) _
  (λ _ _ => True)
  (λ _ => Γ)
  (λ _ _ hai => hai)
  True
  (λ _ _ ha hai => ha ∧ hai)

instance [∀ {s} (x : Var s), Decidable (Γ x)] : ∀ {s}, (a : Abt O s) → Decidable (closed Γ a) := @rec S O _ (λ _ ai => Decidable (closed' Γ ai))
  (λ _ _ => isTrue trivial)
  (λ _ _ => inferInstanceAs <| Decidable (Γ _))
  (λ _ _ hai => hai)
  (isTrue trivial)
  (λ _ _ ha hai => match ha with | isFalse ha => isFalse (λ ⟨ha', _⟩ => ha ha') | isTrue ha => match hai with | isFalse hai => isFalse (λ ⟨_, hai'⟩ => hai hai') | isTrue hai => isTrue ⟨ha, hai⟩)

theorem closed_unbind {a : Abt O s} (h : closed Γ a) : {a' : Abt O t} → closed Γ a' → closed Γ (unbind a a' n)
  | bvar _ m, c => by
    dsimp [unbind]
    split <;> rename_i h
    . cases h
      split
      . exact c
      . exact h
      . cases m with
        | zero =>
          rename_i h
          dsimp [compare, compareOfLessAndEq] at h
          split at h
          . cases h
          . split at h
            . cases h
            . cases Nat.eq_or_lt_of_le (Nat.zero_le n)
              . contradiction
              . contradiction
        | succ m => exact c
    . exact c
  | var .., c => c
  | op _ ai, c => unbind' ai c
where
  unbind' {_}
  | .nil, c => c
  | .cons _ ai, c => ⟨closed_unbind h c.1, unbind' ai c.2⟩

theorem closed_subst {a : Abt O s} (ca : closed Γ a) (x : Var s) : {b : Abt O t} → closed Γ b → closed Γ (subst a x b)
  | bvar .., cb => cb
  | var .., cb => by
    dsimp [subst]
    split
    next h =>
      cases h
      dsimp
      split
      . exact ca
      . exact cb
    . exact cb
  | op _ ai, cb => subst' ai cb
where
  subst' {_}
  | .nil, cb => cb
  | .cons b ai, cb => ⟨closed_subst ca x cb.1, subst' ai cb.2⟩

def sizeOf : ∀ {s}, Abt O s → Nat := @rec S O _ _
  (λ _ _ => 1)
  (λ _ _ => 1)
  (λ _ _ hai => hai + 1)
  0
  (λ _ _ ha hai => ha + hai)

def sizeOf' : ∀ {si : List (List S × S)}, DList (Abt O ·.2) si → Nat := @rec_1 S O (λ _ _ => _) _
  (λ _ _ => 1)
  (λ _ _ => 1)
  (λ _ _ hai => hai + 1)
  0
  (λ _ _ ha hai => ha + hai)

theorem sizeOf_unbind {a : Abt O s} (h : sizeOf a = 1) : (a' : Abt O t) → sizeOf (unbind a a' n) = sizeOf a'
  | bvar .. => by
    dsimp [unbind]
    split
    . split
      . rfl
      . rename_i h _ _
        cases h
        exact h
      . rfl
    . rfl
  | var .. => rfl
  | op _ ai => congrArg Nat.succ (f ai)
where
  f {si} : (ai : DList _ si) → _
    | .nil => rfl
    | .cons a' ai => by apply congr (congrArg Nat.add (sizeOf_unbind h a')) (f ai)

end Abt

def WfAbt (O : _ → S → _) [DecidableEq S] s := { a : Abt O s // a.wellFormed }

namespace WfAbt

variable {S : Type} {O : List (List S × S) → S → Type} [DecidableEq S]

instance instToString [ToString (Abt O s)] : ToString (WfAbt O s) where
  toString a := toString a.1

instance instDecidableEq [∀ si s, DecidableEq (O si s)] : DecidableEq (WfAbt O s)
  | ⟨x, _⟩, ⟨y, _⟩ => if h : x = y then isTrue (Subtype.eq h) else isFalse (h ∘ Subtype.mk.inj)

def var (v : isBound O s) (x : Var s) : WfAbt O s := ⟨.var v x, trivial⟩

def op (o : O si s) (ai : DList (WfAbt O ·.2) si) : WfAbt O s := ⟨.op o <| ai.map Subtype.val, by
  dsimp [Abt.wellFormed]
  clear o
  induction ai with
  | nil => trivial
  | cons a ai hai => exact ⟨Abt.wellFormed_weaken (λ _ => Nat.zero_le _) a.2, hai⟩
⟩

def op' (o : O si s) (ai : DList (λ b => DList Var b.1 × WfAbt O b.2) si) : WfAbt O s := ⟨.op' o <| ai.map λ a => (a.1, a.2.1), by
  dsimp [Abt.wellFormed, Abt.op']
  clear o
  induction ai with
  | nil => trivial
  | @cons b si a ai hai =>
    apply And.intro _ hai
    cases b with | _ si t =>
    cases a with | _ xs a =>
    dsimp at xs a ⊢
    suffices let x : _ × (S → _) := DList.foldr ..; Abt.wellFormed x.1 _ ∧ (∀ s, x.2 s ≤ Abt.bindCount s si) by
      exact this.1
    induction xs with
    | nil => exact ⟨Abt.wellFormed_weaken (λ _ => Nat.zero_le _) a.2, λ _ => .refl⟩
    | @cons s si x xs hxs =>
      dsimp [DList.foldr]
      constructor
      . apply Abt.wellFormed_bind
        . apply Nat.le_trans_lt (hxs.2 s)
          simp [Abt.bindCount]
        . exact Abt.wellFormed_weaken (λ _ => Nat.add_le_add_left (Nat.le_add_right ..) 0) hxs.1
      . intro t
        split
        . rename_i h
          cases h
          apply Nat.le_trans_lt (hxs.2 s)
          simp [Abt.bindCount]
        . apply Nat.le_trans (hxs.2 t) (Nat.le_add_right ..)
⟩

def unop' : ∀ {si}, DList (isBound O) si → (a : Abt O s) → a.wellFormed (Abt.bindCount · si) → DList Var si × WfAbt O s
  | [], _ => (.nil, ⟨·, ·⟩)
  | s' :: si, .cons v vs => λ a wf =>
    let x := a.free s'
    let (xs, a) := unop' vs (Abt.unbind (.var v x) a (Abt.bindCount s' si)) <| Abt.wellFormed_unbind (by exact trivial) (by exact .refl) (by apply Eq.mp (congrArg _ _) wf; funext u; dsimp [Abt.bindCount]; split <;> rename_i h; simp [h]; simp [Ne.symm h])
    (.cons x xs, a)

def unop (o : O si₁ s) {si : List (List S × S)} (hsi : si.Suffix si₁) : (ai : DList (Abt O ·.2) si) → Abt.wellFormed' ai → DList (λ b => DList Var b.1 × WfAbt O b.2) si
  | .nil, _ => .nil
  | .cons a ai, wf => .cons (unop' (.mkMem _ (⟨si₁, s, o, _, List.mem_map_of_mem _ (List.mem_of_mem_suffix (.head _) hsi), ·⟩)) a (by simp at wf; exact wf.1)) (unop o hsi.tail ai wf.2)

variable (O) in
inductive View : S → Type
  | var (v : isBound O s) (x : Var s) : View s
  | op (o : O si s) (ai : DList (λ b => DList Var b.1 × WfAbt O b.2) si) : View s

#compile WfAbt.View

def out : WfAbt O s → View O s
  | ⟨.var v x, _⟩ => .var v x
  | ⟨.op o ai, h⟩ => .op o (unop o .refl ai h)

def View.in : View O s → WfAbt O s
  | var v x => .var v x
  | op o ai => .op' o ai

theorem in_out : (a : WfAbt O s) → View.in (out a) = a := by
  intro ⟨a, wf⟩
  cases a with
  | bvar => cases wf
  | var => rfl
  | @op si _ o ai =>
    dsimp at wf
    apply Subtype.eq _
    apply congrArg (Abt.op o)
    dsimp [unop]
    have := @DList.recSuffix (List S × S) (Abt O ·.2) si (λ si' hs ai => (wf : _) → (
      DList.map (λ a => a.1.foldr (β := _ × _) (λ {t} x (a, n) => (Abt.bind x a (n t), λ u => if u = t then n u + 1 else n u)) (a.2, λ _ : S => 0) |>.1) <|
        DList.map (λ a => (a.1, a.2.1)) <|
          unop o hs ai wf
    ) = ai) ?nil ?cons ai wf
    exact this
    case nil => intro; rfl
    case cons =>
      clear wf ai
      intro si si' a ai' hs hai wf
      apply congr (congrArg _ _) (hai wf.2)
      have : Abt.wellFormed _ _ := wf.1
      simp at this
      show (DList.foldr _ ((unop' _ a this).2.1, _) (unop' _ a this).1).1 = a
      clear hai wf ai'
      rename _ => wf
      cases si with | _ si s =>
      dsimp at a wf ⊢
      suffices DList.foldr .. = (a, (Abt.bindCount · si)) from congrArg Prod.fst this
      have := @List.recSuffix _ si (λ si₁ hs' => ∀ a (wf : _), DList.foldr
        (λ {t} x (a, n) => (Abt.bind x a (n t), λ u => if u = t then n u + 1 else n u))
        (unop' (.mkMem si₁ λ h' => ⟨_, _, o, _, List.mem_map_of_mem Prod.fst (List.mem_of_mem_suffix (.head _) hs), List.mem_of_mem_suffix h' hs'⟩) a wf |>.2.1, λ _ : S => 0)
        (unop' (.mkMem si₁ λ h' => ⟨_, _, o, _, List.mem_map_of_mem Prod.fst (List.mem_of_mem_suffix (.head _) hs), List.mem_of_mem_suffix h' hs'⟩) a wf).1
      = (a, (Abt.bindCount · si₁))) ?nil ?cons a wf
      exact this
      case nil => intro _ _; rfl
      case cons =>
        intro s' si hs' hsi a wf
        dsimp [unop']
        specialize hsi (Abt.unbind (.var ⟨_, _, o, _, List.mem_map_of_mem Prod.fst (List.mem_of_mem_suffix (.head _) hs), List.mem_of_mem_suffix (.head _) hs'⟩ (a.free s')) a (Abt.bindCount s' si)) _
        . apply Abt.wellFormed_unbind
          . trivial
          . simp
          . apply Eq.mp (congrArg _ _) wf
            funext u
            split <;> rename_i h <;> simp [Abt.bindCount, h]
        generalize hB : DList.foldr .. = B
        have := hB.symm.trans hsi
        clear hB hsi
        clear hsi
        cases this
        congr
        . apply Abt.bind_unbind _ _ _ _ a wf (Abt.freeIn_free _ _)
          simp [Abt.bindCount]
        . funext u
          split <;> rename_i h <;> simp [Abt.bindCount, h]

def subst (a : WfAbt O s) (x : Var s) (b : WfAbt O t) : WfAbt O t := ⟨.subst a.1 x b.1, Abt.wellFormed_subst a.2 x b.2⟩

def View.sizeOf : View O s → Nat
  | .var .. => 1
  | .op _ ai => Abt.sizeOf' (ai.map (·.2.1)) + 1

@[simp]
theorem sizeOf_out : (a : WfAbt O s) → (out a).sizeOf = a.1.sizeOf
  | ⟨.var .., _⟩ => rfl
  | ⟨.op o ai, wf⟩ => by
    apply congrArg Nat.succ
    revert ai
    apply DList.recSuffix (motive := λ si hsi ai => (wf : _) → Abt.sizeOf' ((unop o hsi ai wf).map (·.2.1)) = Abt.sizeOf' ai)
    case nil => intro; rfl
    case cons =>
      intro si si' a ai hsi ih wf
      apply congr (congrArg Nat.add _) (ih wf.2)
      clear ih
      have : Abt.wellFormed _ _ := wf.1
      simp at this
      show Abt.sizeOf (unop' _ a this).2.1 = Abt.sizeOf a
      clear wf
      rename _ => wf
      cases si with | _ si s' =>
      dsimp at wf ⊢
      apply @List.rec _ (λ si => (vs : _) → (a : _ ) → (wf : Abt.wellFormed a (Abt.bindCount · si)) → Abt.sizeOf (unop' vs a wf).2.1 = Abt.sizeOf a) ?nil ?cons si (.mkMem _ (⟨_, s, o, _, List.mem_map_of_mem Prod.fst (List.mem_of_mem_suffix (.head si') hsi), ·⟩)) a wf
      case nil => intro .nil _ _; rfl
      case cons =>
        intro s si ih (.cons v vs) a wf
        dsimp [unop']
        apply ih vs (Abt.unbind (.var v (a.free s)) a (Abt.bindCount s si)) _ |>.trans
        apply Abt.sizeOf_unbind
        rfl

end WfAbt

/-
abt ExampleAbt
  Exp
  | num "[" Nat "]"
  | plus "(" Exp "; " Exp ")"
  | times "(" Exp "; " Exp ")"
  | let "(" Exp "; " Var Exp ". " Exp ")"
-/

namespace ExampleAbt

inductive S
  | Exp
deriving DecidableEq

inductive O : List (List S × S) → S → Type
  | num : Nat → O [] .Exp
  | plus : O [([], .Exp), ([], .Exp)] .Exp
  | times : O [([], .Exp), ([], .Exp)] .Exp
  | let : O [([], .Exp), ([.Exp], .Exp)] .Exp

instance : ToString (O si s) where
  toString
  | .num n => s!"num[{n}]"
  | .plus => "plus"
  | .times => "times"
  | .let => "let"

def Abt := WfAbt O

def Exp := Abt .Exp

inductive Exp.View
  | var : Var S.Exp → View
  | num : Nat → View
  | plus : Exp → Exp → View
  | times : Exp → Exp → View
  | let : Exp → Var S.Exp → Exp → View

open DList

def Exp.in : View → Exp
  | .var x => .var ⟨_, _, .let, [.Exp], by simp⟩ x
  | .num n => .op (.num n) ⟦⟧ 
  | .plus a b => .op .plus ⟦a, b⟧
  | .times a b => .op .times ⟦a, b⟧
  | .let a x b => .op' .let ⟦(⟦⟧, a), (⟦x⟧, b)⟧

def Exp.out (e : Exp) : View :=
  match WfAbt.out e with
  | .var _ x => .var x
  | .op (.num n) ⟦⟧ => .num n 
  | .op .plus ⟦(⟦⟧, a), (⟦⟧, b)⟧ => .plus a b
  | .op .times ⟦(⟦⟧, a), (⟦⟧, b)⟧ => .times a b
  | .op .let ⟦(⟦⟧, a), (⟦x⟧, b)⟧ => .let a x b

def Exp.var := («in» <| .var ·)
def Exp.num := («in» <| .num ·)
def Exp.plus := («in» <| .plus · ·)
def Exp.times := («in» <| .times · ·)
def Exp.let := («in» <| .let · · ·)

theorem Exp.in_out : ∀ e, «in» (out e) = e
  | ⟨.var .., _⟩ => rfl
  | ⟨.op (.num _) ⟦⟧, _⟩ => rfl
  | ⟨.op .plus ⟦_, _⟧, _⟩ => rfl
  | ⟨.op .times ⟦_, _⟧, _⟩ => rfl
  | ⟨.op .let ⟦_, _⟧, wf⟩ => (WfAbt.in_out ⟨.op .let ⟦_, _⟧, wf⟩ :)

variable {α} (num : Nat → α) (plus : α → α → α) (times : α → α → α) («let» : α → ((x : Exp) → x.1.closed (λ _ => False) → α) → α) in
partial def Exp.evalClosed [Nonempty α] : (e : Exp) → e.1.closed (λ _ => False) → α
  | ⟨.var .., _⟩ => False.elim
  | ⟨.op (.num n) ⟦⟧, _⟩ => λ _ => num n
  | ⟨.op .plus ⟦a, b⟧, wfa, wfb, _⟩ => λ ⟨ca, cb, _⟩ => plus (evalClosed ⟨a, wfa⟩ ca) (evalClosed ⟨b, wfb⟩ cb)
  | ⟨.op .times ⟦a, b⟧, wfa, wfb, _⟩ => λ ⟨ca, cb, _⟩ => times (evalClosed ⟨a, wfa⟩ ca) (evalClosed ⟨b, wfb⟩ cb)
  | ⟨.op .let ⟦a, b⟧, wfa, (wfb : Abt.wellFormed _ _), _⟩ => λ ⟨ca, cb, _⟩ => «let» (evalClosed ⟨a, wfa⟩ ca) λ x cx => evalClosed ⟨Abt.unbind x.1 b 0, Abt.wellFormed_unbind x.2 .refl <| by simp [Abt.bindCount] at wfb ⊢; exact wfb⟩ (Abt.closed_unbind (λ _ => False) cx cb)

def Exp.eval : (e : Exp) → (_ : e.1.closed (λ _ => False) := by decide) → Nat :=
  evalClosed
    (λ n => n)
    (λ a b => a + b)
    (λ a b => a * b)
    (λ a b => b (num a) ⟨⟩)

open Exp in
#eval «let» (plus (num 2) (num 3)) "z" (times (var "z") (num 8))
open Exp in
#eval eval (.let (plus (num 2) (num 3)) "z" (times (var "z") (num 8)))

end ExampleAbt

namespace ULC

inductive S
  | Exp
deriving DecidableEq

inductive O : List (List S × S) → S → Type
  | abs : O [([.Exp], .Exp)] .Exp
  | app : O [([], .Exp), ([], .Exp)] .Exp

instance : ToString (O si s) where
  toString
    | .abs => "abs"
    | .app => "app"

abbrev Abt := WfAbt O

abbrev Exp := Abt .Exp

inductive Exp.View
  | var : Var S.Exp → View
  | abs : Var S.Exp → Exp → View
  | app : Exp → Exp → View

open DList

def Exp.in : View → Exp
  | .var x => .var ⟨_, _, .abs, [.Exp], by simp⟩ x
  | .abs x e => .op' .abs ⟦(⟦x⟧, e)⟧
  | .app e₁ e₂ => .op .app ⟦e₁, e₂⟧

def Exp.var := (Exp.in <| .var ·)
def Exp.abs := (Exp.in <| .abs · ·)
def Exp.app := (Exp.in <| .app · ·)

def Exp.out (e : Exp) : View :=
  match WfAbt.out e with
  | .var _ x => .var x
  | .op .abs ⟦(⟦x⟧, e)⟧ => .abs x e
  | .op .app ⟦(⟦⟧, e₁), (⟦⟧, e₂)⟧ => .app e₁ e₂

end ULC

open ULC in
#eval Exp.app (.abs "x" <| .var "x") (.abs "x" <| .var "x")

namespace E

inductive S
  | Typ
  | Exp
deriving DecidableEq

inductive O : List (List S × S) → S → Type
  | arr : O [([], .Typ), ([], .Typ)] .Typ
  | void : O [] .Typ
  | lam : O [([], .Typ), ([.Exp], .Exp)] .Exp
  | ap : O [([], .Exp), ([], .Exp)] .Exp
deriving DecidableEq

instance : ToString (O si s) where
  toString
    | .arr => "arr"
    | .void => "void"
    | .lam => "lam"
    | .ap => "ap"

abbrev Abt := WfAbt O

abbrev Typ := Abt .Typ
abbrev Exp := Abt .Exp

inductive Typ.View
  | arr : Typ → Typ → View
  | void : View

inductive Exp.View
  | var : Var S.Exp → View
  | lam : Var S.Exp → Typ → Exp → View
  | ap : Exp → Exp → View

open DList

def Typ.in : View → Typ
  | .arr τ₁ τ₂ => .op .arr ⟦τ₁, τ₂⟧
  | .void => .op .void ⟦⟧

def Typ.arr := (Typ.in <| .arr · ·)
def Typ.void := (Typ.in <| .void)

theorem Typ.notBound : ¬isBound O S.Typ := by
    intro h
    match h with
    | ⟨_, _, .arr, b, .tail _ <| .tail _ h, _⟩ => cases h
    | ⟨_, _, .lam, b, .tail _ <| .tail _ h, _⟩ => cases h
    | ⟨_, _, .ap, b, .tail _ <| .tail _ h, _⟩ => cases h

def Typ.out (τ : Typ) : View :=
  match WfAbt.out τ with
  | .var h _ => notBound h |>.elim
  | .op .arr ⟦(⟦⟧, τ₁), (⟦⟧, τ₂)⟧ => .arr τ₁ τ₂
  | .op .void ⟦⟧ => .void

theorem Typ.in_out : ∀ τ, «in» (out τ) = τ
  | ⟨.var h _, _⟩ => notBound h |>.elim
  | ⟨.op .arr ⟦_, _⟧, _⟩ => rfl
  | ⟨.op .void ⟦⟧, _⟩ => rfl

theorem Typ.out_in : ∀ τ, out («in» τ) = τ
  | .arr .. => rfl
  | .void => rfl

def Exp.in : View → Exp
  | .var x => .var ⟨_, _, .lam, [.Exp], by simp⟩ x
  | .lam x τ e => .op' .lam ⟦(⟦⟧, τ), (⟦x⟧, e)⟧
  | .ap e₁ e₂ => .op .ap ⟦e₁, e₂⟧

def Exp.var := (Exp.in <| .var ·)
def Exp.lam := (Exp.in <| .lam · · ·)
def Exp.ap := (Exp.in <| .ap · ·)

def Exp.out (e : Exp) : View :=
  match WfAbt.out e with
  | .var _ x => .var x
  | .op .lam ⟦(⟦⟧, τ), (⟦x⟧, e)⟧ => .lam x τ e
  | .op .ap ⟦(⟦⟧, e₁), (⟦⟧, e₂)⟧ => .ap e₁ e₂

theorem Exp.in_out : ∀ e, «in» (out e) = e
  | ⟨.var .., _⟩ => rfl
  | ⟨.op .lam ⟦_, _⟧, wf⟩ => (WfAbt.in_out ⟨.op .lam ⟦_, _⟧, wf⟩ :)
  | ⟨.op .ap ⟦_, _⟧, _⟩ => rfl

protected partial def Typ.toString (τ : Typ) : String :=
  match Typ.out τ with
  | .arr τ₁ τ₂ => s!"({τ₁.toString} → {τ₂.toString})"
  | .void => "void"

protected partial def Exp.toString (e : Exp) : String :=
  match Exp.out e with
  | .var x => toString x
  | .lam x τ e => s!"(λ {x} : {τ.toString}. {e.toString})"
  | .ap e₁ e₂ => s!"({e₁.toString} {e₂.toString})"

instance : ToString Typ := ⟨Typ.toString⟩

instance : ToString Exp := ⟨Exp.toString⟩

variable {motive : Exp → Sort u} (var : ∀ x, motive (var x)) (lam : ∀ x τ e, motive e → motive (lam x τ e)) (ap : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (ap e₁ e₂)) in
@[eliminator, elab_as_elim]
def Exp.rec (e : Exp) : motive e :=
  match h : WfAbt.out e with
  | .var v x => by apply Eq.mp _ <| var x; show motive (WfAbt.View.in (.var v x)) = motive e; rw [← h, WfAbt.in_out]
  | .op .lam ⟦(⟦⟧, τ), (⟦x⟧, e')⟧ =>
    have h' : τ.1.sizeOf + e'.1.sizeOf + 1 = e.1.sizeOf := (h ▸ WfAbt.sizeOf_out _ :)
    have : e'.1.sizeOf < e.1.sizeOf := Nat.lt_of_lt_add_left <| Nat.le_of_eq h'
    by apply Eq.mp _ <| lam x τ e' (rec e'); show motive (WfAbt.View.in (.op .lam ⟦(⟦⟧, τ), (⟦x⟧, e')⟧)) = motive e; rw [← h, WfAbt.in_out]
  | .op .ap ⟦(⟦⟧, e₁), (⟦⟧, e₂)⟧ =>
    have h' : e₁.1.sizeOf + e₂.1.sizeOf + 1 = _ := h ▸ WfAbt.sizeOf_out _
    have : e₁.1.sizeOf < e.1.sizeOf := Nat.lt_of_lt_add_right (by exact Nat.le_of_eq h')
    have : e₂.1.sizeOf < e.1.sizeOf := Nat.lt_of_lt_add_left (by exact Nat.le_of_eq h')
    by apply Eq.mp _ <| ap e₁ e₂ (rec e₁) (rec e₂); show motive (WfAbt.View.in (.op .ap ⟦(⟦⟧, e₁), (⟦⟧, e₂)⟧)) = motive e; rw [← h, WfAbt.in_out]
termination_by _ e => e.1.sizeOf

variable {motive : Exp.View → Sort u} (var : ∀ x, motive (.var x)) (lam : ∀ x τ e, motive e.out → motive (.lam x τ e)) (ap : ∀ e₁ e₂, motive e₁.out → motive e₂.out → motive (.ap e₁ e₂)) in
def Exp.rec' (e : Exp) : motive e.out :=
  match h : e.out with
  | .var x => var x
  | .lam x τ e' =>
    have h' : τ.1.sizeOf + e'.1.sizeOf + 1 = e.1.sizeOf := have h : WfAbt.out e = .op .lam ⟦(⟦⟧, τ), (⟦x⟧, e')⟧ := by { unfold out at h; split at h <;> cases h; assumption }; (h ▸ WfAbt.sizeOf_out _ :)
    have : e'.1.sizeOf < e.1.sizeOf := Nat.lt_of_lt_add_left <| Nat.le_of_eq h'
    lam x τ e' (rec' e')
  | .ap e₁ e₂ =>
    have h' : e₁.1.sizeOf + e₂.1.sizeOf + 1 = _ := have h : WfAbt.out e = .op .ap ⟦(⟦⟧, e₁), (⟦⟧, e₂)⟧ := by { unfold out at h; split at h <;> cases h; assumption }; h ▸ WfAbt.sizeOf_out _
    have : e₁.1.sizeOf < e.1.sizeOf := Nat.lt_of_lt_add_right (by exact Nat.le_of_eq h')
    have : e₂.1.sizeOf < e.1.sizeOf := Nat.lt_of_lt_add_left (by exact Nat.le_of_eq h')
    ap e₁ e₂ (rec' e₁) (rec' e₂)
termination_by _ e => e.1.sizeOf

inductive Typing : List (Var S.Exp × Typ) → Exp.View → Typ → Prop
  | var : Γ.lookup x = some τ → Typing Γ (.var x) τ
  | lam : Typing ((x, τ) :: Γ) e.out τ' → Typing Γ (.lam x τ e) (.arr τ τ')
  | ap : Typing Γ e₁.out (.arr τ₁ τ₂) → Typing Γ e₂.out τ₁ → Typing Γ (.ap e₁ e₂) τ₂

theorem Typing.uniqueness : ∀ {τ}, Typing Γ e τ → ∀ {τ'}, Typing Γ e τ' → τ = τ' := Typing.rec (motive := λ Γ e τ _ => ∀ τ', Typing Γ e τ' → τ = τ')
  (λ h _ (.var h') => Option.some.inj <| h.symm.trans h')
  (λ _ ih _ (.lam h') => ih _ h' ▸ rfl)
  (λ _ _ ih₁ _ _ (.ap h₁' _) => And.right <| Typ.View.arr.inj <| congrArg Typ.out (ih₁ _ h₁'))

def inferType : ∀ (e : Exp) Γ, Option { τ // Typing Γ e.out τ } := Exp.rec
  (λ x Γ =>
    match h : Γ.lookup x with
    | some τ => some ⟨τ, .var h⟩
    | none => none
  )
  (λ x τ _ inferType_e Γ =>
    match inferType_e ((x, τ) :: Γ) with
    | some ⟨τ', h⟩ => some ⟨.arr τ τ', .lam h⟩
    | none => none
  )
  (λ _ _ inferType_e₁ inferType_e₂ Γ =>
    match inferType_e₁ Γ, inferType_e₂ Γ with
    | some ⟨τ₁, h₁⟩, some ⟨τ₂, h₂⟩ =>
      match h₁' : τ₁.out with
      | .arr τ τ' =>
        if h : τ = τ₂
        then some ⟨τ', .ap ((congrArg _ (h ▸ Typ.in_out _ ▸ congrArg Typ.in h₁' :)).mp h₁) h₂⟩
        else none
      | _ => none
    | _, _ => none
  )

inductive InferTypeResult₁ Γ e
  | success τ (h : Typing₁ Γ e τ)
  | failure (h : ∀ τ, ¬Typing₁ Γ e τ)

inductive InferTypeResult₂ Γ e
  | success τ (h : Typing₂ Γ e τ)
  | failure (h : ∀ τ, ¬Typing₂ Γ e τ)

def inferType₁ : ∀ e Γ, InferTypeResult₁ Γ (Exp.out e) := @Exp.rec' (λ e => ∀ Γ, InferTypeResult₁ Γ e)
  (λ x Γ =>
    match h : Γ.lookup x with
    | some τ => .success τ (.var h)
    | none => .failure λ _ (.var h') => nomatch (h.symm.trans h')
  )
  (λ x τ e inferType_e Γ =>
    match inferType_e ((x, τ) :: Γ) with
    | .success τ' h => .success (.arr τ τ') (.lam h)
    | .failure h => .failure λ _ (.lam h') => h _ h'
  )
  (λ e₁ e₂ inferType_e₁ inferType_e₂ Γ =>
    match inferType_e₁ Γ, inferType_e₂ Γ with
    | .success τ₁ h₁, .success τ₂ h₂ =>
      match h₁' : τ₁.out with
      | .arr τ τ' => sorry
      | _ => .failure λ _ (.ap h₁' _) => sorry
    | .failure h₁, _ => .failure λ _ (.ap h₁' _) => h₁ _ h₁'
    | _, .failure h₂ => .failure λ _ (.ap _ h₂') => h₂ _ h₂'
  )

end E

open E in
#eval Exp.ap (.lam "f" (.arr .void .void) <| .lam "x" .void <| .ap (.var "f") <| .ap (.var "f") <| .var "x") (.lam "x" .void <| .var "x")

open E in
#eval Exp.ap (.lam "f" .void <| .ap (.var "f") (.var "f")) (.lam "x" .void <| .var "x")

open E in
#eval inferType (.lam "x" .void <| .ap (.var "f") (.var "x")) [("f", .arr .void .void)]

open E in
#eval Typ.arr (.arr .void .void) (.arr .void .void)

namespace Ast

scoped syntax "ast " ident manyIndent(ident manyIndent("| " ident (colGt ident <|> str <|> Lean.Parser.Term.paren)*)) : command

macro_rules
  | `(ast $name $[$sort $[| $ctor $args*]*]*) => do
    let args : Array (Array (Array (Lean.TSyntax `term × _))) ← args.mapM <| Array.mapM <| Array.mapM λ arg =>
      match arg.raw with
      | `($arg:str) => return (arg, none)
      | `($arg) => return (arg, some <| ← Lean.withFreshMacroScope `(x))
    let argTypes := args.map <| Array.map <| Array.filterMap λ (t, x?) => x?.map λ _ => t
    let ctorType ← (sort.zip argTypes).mapM λ (s, a) => a.mapM <| Array.foldrM (`($(·) → $(·))) (s : Lean.Ident)
    let toString := sort.map (Lean.mkIdent <| ·.getId.str "toString")
    let argVars := args.map <| Array.map <| Array.filterMap (·.2)
    let fullCtor := (sort.zip ctor).map λ (s, c) => c.map (Lean.mkIdent <| s.getId ++ Lean.TSyntax.getId ·)
    let ctorToString ← (ctor.zip args).mapM λ (c, a) => (c.zip a).mapM λ (c, a) =>
      a.foldlM (λ s (t, x?) =>
        match x? with
        | some x =>
          if sort.contains ⟨t.raw⟩
          then `($s ++ $(x).toString)
          else `($s ++ toString $x)
        | none => `($s ++ $t)
      ) (Lean.Syntax.mkStrLit c.getId.toString)
    `(namespace $name
      mutual
      $[inductive $sort
          $[| $ctor:ident : $ctorType]*]*
      end
      mutual
      $[protected def $toString : $sort → String
          $[| $fullCtor:ident $argVars* => $ctorToString]*]*
      end
      mutual
      $[instance : ToString $sort := ⟨$toString⟩]*
      end
      end $name)

end Ast

open Ast in
ast Example
  Num
  | num "[" Nat "]"
  | plus "(" Num "; " Num ")"
  | times "(" Num "; " Num ")"
  | parse "(" Str ")"
  Str
  | str "[" String "]"
  | concat "(" Str "; " Str ")"
  | «repeat» "(" Str "; " Num ")"
  | toStr "(" Num ")"

def String.repeat : Nat → String → String
  | 0, _ => ""
  | 1, s => s
  | n + 1, s => String.repeat n s ++ s

namespace Example

mutual

def evalNum : Num → Nat
  | .num n => n
  | .plus n m => evalNum n + evalNum m
  | .times n m => evalNum n * evalNum m
  | .parse s => String.toNat! (evalStr s)

def evalStr : Str → String
  | .str s => s
  | .concat s t => evalStr s ++ evalStr t
  | .repeat s n => .repeat (evalNum n) (evalStr s)
  | .toStr n => toString (evalNum n)

end

open Num Str

#eval parse («repeat» (concat (str "1") (toStr (times (num 2) (num 3)))) (plus (num 2) (num 3)))
#eval evalNum <| parse («repeat» (concat (str "1") (toStr (times (num 2) (num 3)))) (plus (num 2) (num 3)))

end Example
