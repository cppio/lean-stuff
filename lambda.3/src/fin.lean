import data.fin.tuple
import data.list.basic

/-
-- TODO
import algebra.big_operators
open_locale big_operators
-/

section fin

variables {n : ℕ}

def fin.succ' : fin n → fin n.succ :=
λ i, ⟨i.val.succ, nat.succ_lt_succ i.property⟩

instance : has_coe (fin n) (fin n.succ) := ⟨fin.cast_succ⟩

variables {α : fin n.succ → Sort*}

def fin.tail' : (∀ i, α i) → ∀ i, α (fin.succ' i) :=
λ t i, t i.succ'

variables (x : α 0) (t : ∀ i, α (fin.succ' i))

def fin.cons' : ∀ i, α i :=
subtype.rec $ @nat.rec (λ i, ∀ hi, α ⟨i, hi⟩)
  (λ hi, x)
  (λ i _ hi, t ⟨i, nat.lt_of_succ_lt_succ hi⟩)

theorem fin.tail_cons' : fin.tail' (fin.cons' x t) = t :=
funext $ λ ⟨i, hi⟩, rfl

end fin

section list

variables {α : Type*}

def fin.to_list : ∀ {n}, (fin n → α) → list α
| 0 t := []
| (n + 1) t := t 0 :: fin.to_list (fin.tail' t)

theorem fin.length_to_list : ∀ {n} (t : fin n → α), (fin.to_list t).length = n
| 0 t := rfl
| (n + 1) t := congr_arg (+ 1) $ fin.length_to_list (fin.tail' t)

variables (x : α) (l : list α) {n : ℕ}

def fin.of_list' : n = l.length → fin n → α :=
λ h i, l.nth_le i (h ▸ i.property)

def fin.of_list : fin l.length → α :=
fin.of_list' l rfl

lemma fin.of_list_to_list' : ∀ {n} (t : fin n → α) i,
  fin.of_list' (fin.to_list t) (fin.length_to_list t).symm i = t i
| (n + 1) t ⟨0, hi⟩ := rfl
| (n + 1) t ⟨i + 1, hi⟩ :=
  fin.of_list_to_list' (fin.tail' t) ⟨i, nat.le_of_succ_le_succ hi⟩

variables (t : fin n → α)

theorem fin.of_list_to_list :
  fin.of_list' (fin.to_list t) (fin.length_to_list t).symm = t :=
funext $ fin.of_list_to_list' t

theorem fin.to_list_of_list' : ∀ (l : list α) {n} (h : n = l.length),
  fin.to_list (fin.of_list' l h) = l
| [] 0 h := rfl
| (x :: l) (n + 1) h :=
  congr_arg ((::) x) $ fin.to_list_of_list' l $ nat.succ.inj h

theorem fin.to_list_of_list : fin.to_list (fin.of_list l) = l :=
fin.to_list_of_list' l rfl

end list

section map

variables {α β : Type*} (f : α → β)

theorem fin.map_to_list : ∀ {n} (t : fin n → α),
  list.map f (fin.to_list t) = fin.to_list (f ∘ t)
| 0 t := rfl
| (n + 1) t := congr_arg ((::) $ f (t 0)) $ fin.map_to_list (fin.tail' t)

variables (l : list α) {n : ℕ} (h : n = (list.map f l).length)

theorem fin.of_list'_map : fin.of_list' (list.map f l) h =
  f ∘ fin.of_list' l (h.trans $ list.length_map f l) :=
funext (λ i, list.nth_le_map' f (h ▸ i.property))

theorem fin.of_list_map :
  fin.of_list (list.map f l) = f ∘ fin.of_list' l (list.length_map f l) :=
fin.of_list'_map f l rfl

end map

def fin.dfoldl : ∀ {n} {α : fin n → Sort*} {β : fin n.succ → Sort*},
  (∀ i : fin n, β i → α i → β i.succ') → β 0 → (∀ i, α i) → β (fin.last n)
| 0 α β f y t := y
| (n + 1) α β f y t :=
  @fin.dfoldl n (α ∘ fin.succ') (β ∘ fin.succ')
  (λ i, f i.succ') (f 0 y $ t 0) (fin.tail' t)

def fin.dfoldr : ∀ {n} {α : fin n → Sort*} {β : fin n.succ → Sort*},
  (∀ i, α i → β i.succ' → β i) → β (fin.last n) → (∀ i, α i) → β 0
| 0 α β f y t := y
| (n + 1) α β f y t := f 0 (t 0) $
  @fin.dfoldr n (α ∘ fin.succ') (β ∘ fin.succ') (λ i, f i.succ') y (fin.tail' t)

theorem fin.dfoldl_map : ∀ {n} {α : fin n → Sort*} {β : fin n.succ → Sort*}
  (f) (y : β 0) {φ : fin n → Sort*} (t : ∀ i, φ i) (g : ∀ i, φ i → α i),
  fin.dfoldl f y (λ i, g i $ t i) = fin.dfoldl (λ i, (∘ g i) ∘ f i) y t
| 0 α β f y φ t g := rfl
| (n + 1) α β f y φ t g :=
  @fin.dfoldl_map n (α ∘ fin.succ') (β ∘ fin.succ')
  (λ i, f i.succ') (f 0 y $ g 0 $ t 0)
  (φ ∘ fin.succ') (fin.tail' t) (λ i, g i.succ')

theorem fin.dfoldr_map : ∀ {n} {α : fin n → Sort*} {β : fin n.succ → Sort*}
  (f) (y : β (fin.last n)) {φ : fin n → Sort*} (t : ∀ i, φ i) (g : ∀ i, φ i → α i),
  fin.dfoldr f y (λ i, g i $ t i) = fin.dfoldr (λ i, f i ∘ g i) y t
| 0 α β f y φ t g := rfl
| (n + 1) α β f y φ t g :=
  congr_arg (f 0 $ g 0 $ t 0) $
  @fin.dfoldr_map n (α ∘ fin.succ') (β ∘ fin.succ')
  (λ i, f i.succ') y (φ ∘ fin.succ') (fin.tail' t) (λ i, g i.succ')

section foldl

variables {α β : Sort*} (f : β → α → β) (y : β)
variables {φ : Sort*} {n : ℕ} (t : fin n → φ) (g : φ → α)

def fin.foldl : (fin n → α) → β :=
@fin.dfoldl n (λ i, α) (λ i, β) (λ i, f) y

theorem fin.foldl_map : fin.foldl f y (g ∘ t) = fin.foldl ((∘ g) ∘ f) y t :=
@fin.dfoldl_map n (λ i, α) (λ i, β) (λ i, f) y (λ i, φ) t (λ i, g)

end foldl

section foldr

variables {α β : Sort*} (f : α → β → β) (y : β)
variables {φ : Sort*} {n : ℕ} (t : fin n → φ) (g : φ → α)

def fin.foldr : (fin n → α) → β :=
@fin.dfoldr n (λ i, α) (λ i, β) (λ i, f) y

theorem fin.foldr_map : fin.foldr f y (g ∘ t) = fin.foldr (f ∘ g) y t :=
@fin.dfoldr_map n (λ i, α) (λ i, β) (λ i, f) y (λ i, φ) t (λ i, g)

end foldr

section foldl_list

variables {α β : Type*} (f : β → α → β) (y : β) (l : list α)

theorem fin.foldl_to_list : ∀ (y) {n} (t : fin n → α),
  list.foldl f y (fin.to_list t) = fin.foldl f y t
| y 0 t := rfl
| y (n + 1) t := fin.foldl_to_list (f y (t 0)) (fin.tail' t)

theorem fin.foldl_of_list' : ∀ (y) (l : list α) {n} (h : n = l.length),
  fin.foldl f y (fin.of_list' l h) = list.foldl f y l
| y [] 0 h := rfl
| y (x :: l) (n + 1) h := fin.foldl_of_list' (f y x) l $ nat.succ.inj h

theorem fin.foldl_of_list : fin.foldl f y (fin.of_list l) = list.foldl f y l :=
fin.foldl_of_list' f y l rfl

end foldl_list

section foldr_list

variables {α β : Type*} (f : α → β → β) (y : β) (l : list α)

theorem fin.foldr_to_list : ∀ {n} (t : fin n → α),
  list.foldr f y (fin.to_list t) = fin.foldr f y t
| 0 t := rfl
| (n + 1) t := congr_arg (f (t 0)) $ fin.foldr_to_list (fin.tail' t)

theorem fin.foldr_of_list' : ∀ (l : list α) {n} (h : n = l.length),
  fin.foldr f y (fin.of_list' l h) = list.foldr f y l
| [] 0 h := rfl
| (x :: l) (n + 1) h := congr_arg (f x) $ fin.foldr_of_list' l $ nat.succ.inj h

theorem fin.foldr_of_list : fin.foldr f y (fin.of_list l) = list.foldr f y l :=
fin.foldr_of_list' f y l rfl

end foldr_list

section finset

parameter (α : Type*)

structure finset' := (card : ℕ) (elems : fin card → α)

parameter {α}

instance : has_emptyc finset' := ⟨{card := 0, elems := fin.elim0}⟩
instance : has_singleton α finset' := ⟨λ x, {card := 1, elems := λ _, x}⟩
instance : has_union finset' :=
⟨λ s t, {card := s.card + t.card, elems := fin.append rfl s.elems t.elems}⟩
instance : has_mem α finset' := ⟨λ x s, ∃ i, s.elems i = x⟩
instance : has_subset finset' := ⟨λ s t, ∀ x, x ∈ s → x ∈ t⟩
instance : has_coe_to_sort finset' _ := ⟨λ s, {x // x ∈ s}⟩

theorem finset'.mem_singleton (x y) : x ∈ ({y} : finset') ↔ x = y :=
⟨λ ⟨i, h⟩, h.symm, λ h, ⟨0, h.symm⟩⟩

theorem finset'.mem_singleton_self {x} : x ∈ ({x} : finset') :=
⟨0, rfl⟩

instance : is_trans finset' has_subset.subset :=
⟨λ s t u hst htu x, htu x ∘ hst x⟩

theorem finset'.mem_union (x) (s t : finset') : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t :=
begin
  split,
  {
    intro h,
    cases h with i h,
    cases i with i hi,
    by_cases hs : i < s.card,
    {
      left,
      use i,
      exact hs,
      dsimp [has_union.union, fin.append] at h,
      simp [hs] at h,
      exact h,
    },
    {
      right,
      dsimp [has_union.union] at hi h,
      use i - s.card,
        simp at hs,
        suffices : i - s.card + s.card < t.card + s.card,
          simp at this,
          assumption,
        rw nat.sub_add_cancel,
        rw add_comm,
        assumption,
        assumption,
      simp [fin.append, hs] at h,
      assumption,
    },
  },
  {
    intro h,
    cases h,
    case inl {
      cases h with i h,
      use i,
        dsimp [has_union.union],
        apply nat.lt_of_succ_le,
        transitivity,
        exact i.property,
        apply le_self_add,
      dsimp [has_union.union, fin.append],
      cases i with i hi,
      simp [hi, h],
    },
    case inr {
      cases h with i h,
      use s.card + i,
        dsimp [has_union.union],
        apply nat.add_lt_add_left,
        exact i.property,
      dsimp [has_union.union, fin.append],
      simp [h],
    },
  },
end

def finset'.to_list (s : finset') : list α := fin.to_list s.elems

theorem finset'.mem_to_list (x) (s : finset') : x ∈ s.to_list ↔ x ∈ s :=
begin
  cases s with card elems,
  split,
  {
    intro h,
    induction card,
    case zero {
      cases h,
    },
    case succ : card ih {
      cases h,
      case inl {
        exact ⟨0, h.symm⟩,
      },
      case inr {
        cases ih (fin.tail' elems) h with i hi,
        exact ⟨i.succ', hi⟩,
      },
    },
  },
  {
    intro h,
    cases h with i h,
    cases card,
    case zero {
      exact i.elim0,
    },
    case succ {
      cases i with i hi,
      induction i generalizing card,
      case zero {
        exact or.inl h.symm,
      },
      case succ : i ih {
        cases card,
        case zero {
          simp at hi,
          contradiction,
        },
        case succ {
          exact or.inr (ih card (fin.tail' elems) (nat.lt_of_succ_lt_succ hi) h),
        },
      },
    },
  },
end

end finset

theorem fin.foldl_lift {α β} (f : β → α → β) :
  ∀ (y) {n} (t : fin n → α) {φ} (g : β → φ) (f' : φ → α → φ),
  (∀ y x, g (f y x) = f' (g y) x) → g (fin.foldl f y t) = fin.foldl f' (g y) t
| y 0 t φ g f' hf := rfl
| y (n + 1) t φ g f' hf :=
  by { unfold fin.foldl fin.dfoldl,
       rw ← hf,
       exact fin.foldl_lift _ (fin.tail' t) g f' hf, }

theorem fin.foldr_lift {α β} (f : α → β → β) (y) :
  ∀ {n} (t : fin n → α) {φ} (g : β → φ) (f' : α → φ → φ),
  (∀ x y, g (f x y) = f' x (g y)) → g (fin.foldr f y t) = fin.foldr f' (g y) t
| 0 t φ g f' hf := rfl
| (n + 1) t φ g f' hf :=
  by { unfold fin.foldr fin.dfoldr,
       rw hf,
       congr,
       exact fin.foldr_lift (fin.tail' t) g f' hf, }

def option.lift₂ {α β γ} (f : α → β → γ) : option α → option β → option γ
| (some x) (some y) := some (f x y)
| _ _ := none

def fin.lift_option {n α} : (fin n → option α) → option (fin n → α) :=
@fin.dfoldl n (λ i, option α) (λ i, option (fin i → α))
  (λ i, option.lift₂ $ flip $ @fin.last_cases i (λ i', α)) (some fin.elim0)

-- TODO

section sum

lemma fin.foldl_assoc {α} (f) [is_associative α f] (x₁) : ∀ (x₂) {n} (t : fin n → α), fin.foldl f (f x₁ x₂) t = f x₁ (fin.foldl f x₂ t)
| x₂ 0 t := rfl
| x₂ (n + 1) t :=
  ((is_associative.assoc x₁ x₂ (t 0) : f (f x₁ x₂) (t 0) = f x₁ (f x₂ (t 0))).symm ▸ fin.foldl_assoc (f x₂ (t 0)) (fin.tail' t) :
  fin.foldl f (f (f x₁ x₂) (t 0)) (fin.tail' t) = f x₁ (fin.foldl f (f x₂ (t 0)) (fin.tail' t)))

theorem fin.foldl_eq_foldr_assoc {α} (f) [is_associative α f] : ∀ (x₁ x₂) {n} (t : fin n → α), f (fin.foldl f x₁ t) x₂ = f x₁ (fin.foldr f x₂ t)
| x₁ x₂ 0 t := rfl
| x₁ x₂ (n + 1) t := by {
  show f (fin.foldl f (f x₁ (t 0)) (fin.tail' t)) x₂ = f x₁ (f (t 0) (fin.foldr f x₂ (fin.tail' t))),
  rw fin.foldl_assoc,
  rw @is_associative.assoc α f _,
  exact congr_arg (f x₁) (fin.foldl_eq_foldr_assoc (t 0) x₂ (fin.tail' t)),
}

variables {α : Type*} [has_zero α] [has_add α]

/-
def fin.sumr : ∀ {n}, (fin n → α) → α :=
@nat.rec (λ n, (fin n → α) → α) (λ t, 0) (λ n s t, t 0 + s (fin.tail' t))

def fin.suml : ∀ {n}, (fin n → α) → α :=
@nat.rec (λ n, (fin n → α) → α) (λ t, 0) (λ n s t, s (fin.init t) + t (fin.last n))

lemma fin.sumr_eq_foldr : ∀ {n} (t : fin n → α), fin.sumr t = fin.foldr (+) 0 t
| 0 t := rfl
| (n + 1) t := congr_arg ((+) (t 0)) $ fin.sumr_eq_foldr (fin.tail' t)

lemma fin.suml_eq_foldl : ∀ {n} (t : fin n → α), fin.suml t = fin.foldl (+) 0 t
| 0 t := rfl
| 1 t := rfl
| (n + 2) t := by {
  show fin.suml (fin.init t) + t (fin.last (n + 1)) = fin.foldl has_add.add (0 + t 0) (fin.tail' t),
  rw fin.suml_eq_foldl (fin.init t),
  show fin.foldl has_add.add (0 + t 0) (fin.tail' (fin.init t)) + t (fin.last (n + 1)) = fin.foldl has_add.add (0 + t 0) (fin.tail' t),
}

theorem fin.suml_eq_sumr [is_associative α (+)] : ∀ {n} (t : fin n → α), 0 + fin.suml t = fin.sumr t + 0
| 0 t := rfl
| (n + 1) t := by { dsimp [fin.suml, fin.sumr], show 0 + (t 0 + fin.suml (fin.tail' t)) = fin.sumr (fin.init t) + t (fin.last n) + 0, }

variables x₁ x₂ x₃ x₄ : α
#reduce fin.sumr $ fin.of_list [x₁, x₂, x₃, x₄]
#reduce fin.foldr (+) 0 $ fin.of_list [x₁, x₂, x₃, x₄]
#reduce fin.foldl (+) 0 $ fin.of_list [x₁, x₂, x₃, x₄]
#reduce fin.suml $ fin.of_list [x₁, x₂, x₃, x₄]
-/

end sum
