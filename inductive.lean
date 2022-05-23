namespace hidden

universes u₁ u₂ u₃

def list' (α : Type u₁) (β : Type u₂) : Type (max u₁ u₂ (u₃+1)) := Π (γ : Type u₃), γ → (α → β → γ) → γ

def list'.nil {α β} : list' α β := λ _ x _, x
def list'.cons {α β} : α → β → list' α β := λ x y _ _ f, f x y

def list'.map {α β γ} : (β → γ) → list' α β → list' α γ := λ f l _ x g, l _ x (λ y z, g y (f z))

def list (α) : Type (max u₁ (u₂+1) (u₃+1)) := Π β, (list'.{u₁ u₂ u₃} α β → β) → β

def list.fold {α} : list' α (list α) → list α := λ l _ f, f (l.map (λ l, l _ f))
def list.rec {α β} : (list' α β → β) → list α → β := λ f l, l _ f

def list.unfold {α} : list α → list' α (list α) := list.rec (list'.map list.fold)
--def list.unfold' {α} : list α → list' α (list α) := λ (l : list α), l (list' α (list α)) (λ (l : list' α (list' α (list α))) (_x) (x : _x) (g : α → list α → _x), l _x x (λ (y : α) (z : list' α (list α)), g y (λ (_x) (f : list' α _x → _x), f (λ (_y) (x : _y) (g : α → _x → _y), z _y x (λ (y : α) (z : list α), g y (z _x f))))))
def list.unfold' {α : Type u₁} : list.{u₁ u₂ u₃} α → list'.{u₁ (max u₁ (u₂+1) (u₃+1)) u₃} α (list.{u₁ u₂ u₃} α) := λ (l : list.{u₁ u₂ u₃} α), l (list'.{u₁ (max u₁ (u₂+1) (u₃+1)) u₃} α (list.{u₁ u₂ u₃} α)) (λ l _ x f, l _ x (λ x l, f x (λ _ f, f (λ _ x g, l _ x (λ x l, g x (l _ f))))))

set_option pp.all true
set_option pp.full_names false
#check @list.fold      
#check @list.unfold  
#check @list.unfold'
#print list.unfold

def list.nil {α} : list α := list.fold list'.nil
def list.cons {α} : α → list α → list α := λ x l, list.fold (list'.cons x l)

def list.length {α} : list α → ℕ := list.rec (λ l, l _ 0 (λ _ x, x + 1))

#reduce list.nil.length
#reduce (list.cons 2 list.nil).length
#reduce (list.cons 3 (list.cons 2 list.nil)).length

def list.head {α} : list α → option α := λ l, l.unfold _ none (λ x _, some x)

#reduce list.nil.head
#reduce (list.cons 2 list.nil).head
#reduce (list.cons 3 (list.cons 2 list.nil)).head

def list.tail {α} : list α → list α := λ l, l.unfold _ list.nil (λ _ l, l)

#reduce list.nil.tail.length
#reduce (list.cons 2 list.nil).tail.length
#reduce (list.cons 3 (list.cons 2 list.nil)).tail.length

#reduce list.nil.tail.head
#reduce (list.cons 2 list.nil).tail.head
#reduce (list.cons 3 (list.cons 2 list.nil)).tail.head

end hidden

namespace hidden₂

universes u₁ u₂ u₃
variables {α : Type u₁} {β : Type u₂} {γ : Type u₃}

def prod (α : Type u₁) (β : Type u₂) : Type (max u₁ u₂ (u₃+1)) := Π (γ : Type u₃), (α → β → γ) → γ
def prod.mk (x : α) (y : β) : prod α β := λ γ f, f x y
def prod.fst (z : prod α β) : α := z α (λ x y, x)
def prod.snd (z : prod α β) : β := z β (λ x y, y)

def sum (α : Type u₁) (β : Type u₂) : Type (max u₁ u₂ (u₃+1)) := Π (γ : Type u₃), (α → γ) → (β → γ) → γ
def sum.inl (x : α) : sum α β := λ γ f g, f x
def sum.inr (y : β) : sum α β := λ γ f g, g y
def sum.cases_on (z : sum α β) (f : α → γ) (g : β → γ) : γ := z γ f g

def empty := Π (α : Type*), α
def unit := Π (α : Type*), α → α

end hidden₂
