namespace hidden

def list' (α β : Type*) := Π γ : Type*, γ → (α → β → γ) → γ

def list'.nil {α β} : list' α β := λ _ x _, x
def list'.cons {α β} : α → β → list' α β := λ x y _ _ f, f x y

def list'.map {α β γ} : (β → γ) → list' α β → list' α γ := λ f l, l _ list'.nil (λ x y, list'.cons x (f y))

-- def list'.rec {α β γ} : γ → (α → β → γ) → list' α β → γ := λ x f l, l _ x f

/-
def list' (α β) := unit ⊕ (α × β)

def list'.nil {α β} : list' α β := sum.inl ()
def list'.cons {α β} : α → β → list' α β := λ x y, sum.inr (x, y)

def list'.map {α β γ} : (β → γ) → list' α β → list' α γ := λ f l, match l with sum.inl () := list'.nil | sum.inr (x, y) := list'.cons x (f y) end

def list'.rec {α β γ} : γ → (α → β → γ) → list' α β → γ := λ x f l, match l with sum.inl () := x | sum.inr (x, y) := f x y end
--/

def list (α) := Π β, (list' α β → β) → β

def list.fold {α} : list' α (list α) → list α := λ l _ f, f (l.map (λ l, l _ f))
def list.rec {α β} : (list' α β → β) → list α → β := λ f l, l _ f

def list.unfold {α} : list α → list' α (list α) := list.rec (list'.map list.fold)

def list.nil {α} : list α := list.fold list'.nil
def list.cons {α} : α → list α → list α := λ x l, list.fold (list'.cons x l)

def list.length {α} : list α → ℕ := list.rec (λ l, l _ 0 (λ _ x, x + 1))
-- def list.length {α} : list α → ℕ := list.rec (list'.rec 0 (λ _ x, x + 1))

#reduce list.nil.length
#reduce (list.cons 2 list.nil).length
#reduce (list.cons 3 (list.cons 2 list.nil)).length

def list.head {α} : list α → option α := list.rec (λ l, l _ none (λ x _, some x))
-- def list.head {α} : list α → option α := list.rec (list'.rec none (λ x _, some x))
-- def list.head {α} : list α → option α := λ l, l.unfold (option α) none (λ x _, some x)

#reduce list.nil.head
#reduce (list.cons 2 list.nil).head
#reduce (list.cons 3 (list.cons 2 list.nil)).head

def list.tail {α} : list α → list α := λ l, l.unfold _ list.nil (λ _ _, list.nil)
-- def list.tail {α} : list α → list α := λ l, list'.rec list.nil (λ _ _, list.nil) l.unfold

#reduce list.nil.tail.length
#reduce (list.cons 2 list.nil).tail.length
#reduce (list.cons 3 (list.cons 2 list.nil)).tail.length

#reduce list.nil.tail.head
#reduce (list.cons 2 list.nil).tail.head
#reduce (list.cons 3 (list.cons 2 list.nil)).tail.head

end hidden
