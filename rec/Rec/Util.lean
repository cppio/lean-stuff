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
  | insertWff _ h ih => cases h; exact insertWff ih (map_insert ..)
  | eraseWff _ h ih => cases h; exact eraseWff ih (map_erase ..)

/-
@[simp]
theorem ofMap_leaf : map f t = leaf ↔ t = leaf := by
  cases t <;> simp [map]

@[simp]
theorem ofMap_node  : map f t = node c l k v r ↔ ∃ l' v' r', t = node c l' k v' r' ∧ map f l' = l ∧ f k v' = v ∧ map f r' = r := by
  constructor
  . intro h
    cases t <;> cases h
    exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩
  . intro ⟨_, _, _, _⟩
    simp [map, *]

macro "destruct" : tactic =>
  `(tactic| ((repeat first | cases ‹Exists ..› | cases ‹And ..›); subst_vars))

section

local syntax "by_match " term " with" ("| " term)* : term
macro_rules
  | `(by_match $t with $[| $p]*) =>
    let q := p
    `(by match $t:term with $[| $p => intro h; simp [balance1] at h; destruct; exact ⟨$q, _, _, rfl, rfl, rfl, rfl⟩]*)

theorem ofMap_balance1 : map f t = balance1 l k v r → ∃ l' v' r', t = balance1 l' k v' r' ∧ map f l' = l ∧ f k v' = v ∧ map f r' = r :=
  by_match l with
  | leaf
  | node .red leaf _ _ leaf
  | node .red leaf _ _ (node .red ..)
  | node .red leaf _ _ (node .black ..)
  | node .red (node .red ..) _ _ leaf
  | node .red (node .red ..) _ _ (node .red ..)
  | node .red (node .red ..) _ _ (node .black ..)
  | node .red (node .black ..) _ _ leaf
  | node .red (node .black ..) _ _ (node .red ..)
  | node .red (node .black ..) _ _ (node .black ..)
  | node .black ..

end

section

local syntax "by_match " term " with" ("| " term)* : term
macro_rules
  | `(by_match $t with $[| $p]*) =>
    let q := p
    `(by match $t:term with $[| $p => intro h; simp [balance2] at h; destruct; exact ⟨_, _, $q, rfl, rfl, rfl, rfl⟩]*)

theorem ofMap_balance2 : map f t = balance2 l k v r → ∃ l' v' r', t = balance2 l' k v' r' ∧ map f l' = l ∧ f k v' = v ∧ map f r' = r :=
  by_match r with
  | leaf
  | node .red leaf _ _ leaf
  | node .red leaf _ _ (node .red ..)
  | node .red leaf _ _ (node .black ..)
  | node .red (node .red ..) _ _ leaf
  | node .red (node .red ..) _ _ (node .red ..)
  | node .red (node .red ..) _ _ (node .black ..)
  | node .red (node .black ..) _ _ leaf
  | node .red (node .black ..) _ _ (node .red ..)
  | node .red (node .black ..) _ _ (node .black ..)
  | node .black ..

end

theorem ofMap_ins (heq : ∀ {x y}, cmp x y = .eq → x = y) : map f t = ins cmp t' k v → ∃ t'' v', t = ins cmp t'' k v' := by
  unfold ins
  split
  . simp; intro; destruct; exact ⟨leaf, _, rfl⟩
  . split
    . simp; intro; destruct; have := ofMap_ins heq ‹_›; destruct; exact ⟨node .red .., _, by dsimp; rw [‹cmp .. = _›]⟩
    . simp; intro; destruct; have := ofMap_ins heq ‹_›; destruct; exact ⟨node .red .., _, by dsimp; rw [‹cmp .. = _›]⟩
    . simp; intro; destruct; exact ⟨node .red .., _, by dsimp; rw [‹cmp .. = _›]; exact heq ‹cmp .. = _› ▸ ‹_›⟩
  . split
    . intro h; have := ofMap_balance1 f h; clear h; destruct; have := ofMap_ins heq ‹_›; destruct; exact ⟨node .black .., _, by dsimp; rw [‹cmp .. = _›]⟩
    . intro h; have := ofMap_balance2 f h; clear h; destruct; have := ofMap_ins heq ‹_›; destruct; exact ⟨node .black .., _, by dsimp; rw [‹cmp .. = _›]⟩
    . simp; intro; destruct; exact ⟨node .black .., _, by dsimp; rw [‹cmp .. = _›]; exact heq ‹cmp .. = _› ▸ ‹_›⟩

theorem ofMap_setBlack : map f t = setBlack t' → ∃ t'', t = setBlack t'' := by
  cases t'
  . simp [setBlack]; intro; destruct; exact ⟨leaf, rfl⟩
  . simp [setBlack]; intro; destruct; exact ⟨node ‹_› .., rfl⟩

theorem ofMap_insert (heq : ∀ {x y}, cmp x y = .eq → x = y) (h : map f t = insert cmp t' k v) : ∃ t'' v', t = insert cmp t'' k v' := by
  unfold insert at h ⊢
  split at h
  . have := ofMap_setBlack f h; destruct; rw [map_setBlack] at h; sorry
  . have := ofMap_ins f heq h; destruct; exact ⟨‹_›, _, by dsimp; sorry⟩

theorem ins_ne_leaf : ins cmp t k v ≠ leaf := by
  unfold ins
  split
  . simp
  . split <;> simp
  . split
    . unfold balance1
      split <;> simp
    . unfold balance2
      split <;> simp
    . simp

theorem insert_ne_leaf : insert cmp t k v ≠ leaf := by
  unfold insert
  split
  . unfold setBlack
    split
    . simp
    . exact ins_ne_leaf
  . exact ins_ne_leaf

theorem ofMap_insert (h : map f t = insert cmp t' k v) : ∃ t'' v', t = insert cmp t'' k v' := by
  cases t <;> cases t' <;> dsimp [map, insert, isRed] at h ⊢
  . simp at h; cases ins_ne_leaf h.symm
  . sorry
  . sorry
  . sorry

theorem WellFormed.ofMapWff (w : WellFormed cmp (map f n)) : WellFormed cmp n := by
  generalize hn' : map f n = n' at w
  induction w generalizing n with
  | leafWff => cases n; exact leafWff; cases hn'
  | insertWff _ h ih => cases h; cases n; dsimp [map] at hn'; cases insert_ne_leaf hn'.symm; have := ofMap_insert f sorry hn'; destruct; rename_i h; rw [h, map_insert] at hn'; exact insertWff (ih sorry) ‹_›
  | eraseWff _ h ih => cases h; sorry -- exact h ▸ eraseWff ih (map_erase ..)

variable {α : Type u} {β γ : α → Type u} {m : Type u → Type v} [Applicative m] (f : (a : α) → β a → m (γ a)) in
def mapM' : (t : RBNode α β) → m { t' : RBNode α γ // t.map (λ _ _ => PUnit.unit) = t'.map (λ _ _ => PUnit.unit) }
  | leaf => pure ⟨leaf, rfl⟩
  | node color lchild key val rchild =>
    (λ ⟨lchild', _⟩ val' ⟨rchild', _⟩ => ⟨node color lchild' key val' rchild', by unfold map; congr⟩) <$> mapM' lchild <*> f key val <*> mapM' rchild
  -/

end Lean.RBNode

def Lean.RBMap.map (f : α → β → γ) : RBMap α β cmp → RBMap α γ cmp
  | ⟨t, w⟩ => ⟨.map f t, .mapWff f w⟩

def Lean.RBMap.mapM [Applicative m]  (f : α → β → m γ) : RBMap α β cmp → m (RBMap α γ cmp)
  | ⟨t, w⟩ =>
    --(λ ⟨t', h⟩ => ⟨t', .ofMapWff (λ _ _ => PUnit.unit) <| h ▸ .mapWff _ w⟩) <$> t.mapM' f
    (⟨·, sorry⟩) <$> t.mapM f

/-
attribute [local simp]
  Functor.map SeqLeft.seqLeft SeqRight.seqRight Seq.seq bind
  EStateM.map EStateM.seqRight EStateM.bind

instance : LawfulMonad (EStateM ε σ) where
  map_const := rfl
  id_map _ := by funext _; simp; split <;> simp [*]
  seqLeft_eq _ _ := by funext _; simp; split <;> rfl
  seqRight_eq _ _ := by funext _; simp; split; split <;> assumption; rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := by
    funext _; simp; split
    . split at *; simp [*]; contradiction
    . split at *; simp [*]; injections; simp [*]

instance : LawfulMonad (EIO ε) := instLawfulMonadEStateMInstMonadEStateM
-/
