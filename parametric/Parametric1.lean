import Parametric

class ParaF (ϕ : (Fin2 n → Type u) → Type u) :=
  prop : ∀ α β, (∀ i, α i → β i → Prop) → ϕ α → ϕ β → Prop

attribute [simp] ParaF.prop

instance : ParaF λ α => α i where
  prop _ _ r := r i

instance : @ParaF n λ _ => α where
  prop _ _ _ := Eq

instance [ParaF ϕ] [ParaF φ] : ParaF λ α => ϕ α → φ α where
  prop α β r f g := ∀ x y, ParaF.prop α β r x y → ParaF.prop α β r (f x) (g y)

class ParaT (α : Type u) :=
  prop : α → Prop

attribute [simp] ParaT.prop

instance (ϕ : Type u → Type u) [I : @ParaF 1 λ α => ϕ (α .zero)] : ParaT (∀ α, ϕ α) where
  prop f := ∀ {α β} (r : α → β → Prop), I.prop (λ _ => α) (λ _ => β) (λ _ => r) (f α) (f β)

instance (ϕ : Type u → Type u → Type u) [I : @ParaF 2 λ α => ϕ (α .zero) (α (.succ .zero))] : ParaT (∀ α β, ϕ α β) where
  prop f := ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop), I.prop (Fin2.cases₂' α β) (Fin2.cases₂' α' β') (Fin2.cases₂ r s) (f α β) (f α' β')

def Para (α) [I : ParaT α] := Subtype I.prop

instance [ParaT α] : CoeFun (Para α) λ _ => α where
  coe := Subtype.val

def Para.mk [ParaT α] (x : α) (h : ParaT.prop x := by parametric) : Para α := ⟨x, h⟩

section K

example : ParaT.prop (@f : ∀ {α β}, α → β → α) =
  ∀ {α α'} (r : α → α' → Prop),
    ∀ {β β'} (s : β → β' → Prop),
      ∀ x x', r x x' →
        ∀ y y', s y y' →
          r (f x y) (f x' y')
:= rfl

example : Para (∀ {α β}, α → β → α) := .mk λ x _ => x

example (f : Para (∀ {α β}, α → β → α)) : f x y = x :=
  f.2 (λ _ x' => x' = x) (λ _ y' => y' = y) () x rfl () y rfl

end K

section List

def lift (r : α → β → Prop) : List α → List β → Prop
  | [],    []    => True
  | x::xs, y::ys => r x y ∧ lift r xs ys
  | _,     _     => False

theorem lift_map (g : α → β) : ∀ l, lift (λ x y => g x = y) l (l.map g)
  | [] => trivial
  | _::l => ⟨rfl, lift_map g l⟩

instance [ParaF ϕ] : ParaF λ α => List (ϕ α) where
  prop α β r := lift (ParaF.prop α β r)

example : ParaT.prop (@f : ∀ {α β}, (α → β → β) → β → List α → β) =
  ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop),
    ∀ c c', (∀ x x', r x x' → ∀ y y', s y y' → s (c x y) (c' x' y')) →
      ∀ x x', s x x' →
        ∀ l l', lift r l l' →
          s (f c x l) (f c' x' l')
:= rfl

example : ParaT.prop (@List.foldr) := by
  intro _ _ r _ _ s c c' _ x x' _
  let rec h : ∀ l l', lift r l l' → s (l.foldr c x) (l'.foldr c' x')
  | [], [], _ => by parametric
  | _::_, _::_, ⟨_, _⟩ => by parametric h
  exact h

example (f : Para (∀ {α β}, (α → β → β) → β → List α → β)) (g : α → α') (h : β → β') (c c') (hc : ∀ x y, h (c x y) = c' (g x) (h y)) (x l) : h (f c x l) = f c' (h x) (l.map g) :=
  f.2 (λ x y => g x = y) (λ x y => h x = y) c _ (λ x _ hx y _ hy => hx ▸ hy ▸ hc x y) x _ rfl l _ (lift_map g l)

example : ParaT.prop λ {α β : Type _} x => List.map (λ f : α → β => f x) := by
  dsimp
  intro α α' r β β' s x x' hx
  let rec h : ∀ l l', lift (λ (f : α → β) (g : α' → β') => ∀ x y, r x y → s (f x) (g y)) l l' → lift s (l.map λ f => f x) (l'.map λ g => g x')
  | [], [], _ => by parametric
  | _::_, _::_, ⟨_, _⟩ => by parametric h
  exact h

end List
