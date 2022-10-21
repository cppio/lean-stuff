import Parametric

class ParaF (ϕ : (Fin2 n → Type u) → Type u) :=
  prop : ∀ α β, (∀ i, α i → β i → Prop) → ϕ α → ϕ β → Prop

instance : ParaF λ α => α i where
  prop _ _ r := r i

instance : @ParaF n λ _ => α where
  prop _ _ _ := Eq

instance [ParaF ϕ] [ParaF φ] : ParaF λ α => ϕ α → φ α where
  prop α β r f g := ∀ x y, ParaF.prop α β r x y → ParaF.prop α β r (f x) (g y)

class ParaT (α : Type u) :=
  prop : α → Prop

instance (ϕ : Type u → Type u) [I : @ParaF 1 λ α => ϕ (α 0)] : ParaT (∀ α, ϕ α) where
  prop f := ∀ {α β} (r : α → β → Prop), I.prop (λ _ => α) (λ _ => β) (λ _ => r) (f α) (f β)

instance (ϕ : Type u → Type u → Type u) [I : @ParaF 2 λ α => ϕ (α 0) (α 1)] : ParaT (∀ α β, ϕ α β) where
  prop f := ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop), I.prop (Fin2.cases₂' α β) (Fin2.cases₂' α' β') (Fin2.cases₂ r s) (f α β) (f α' β')

example : ParaT.prop (@f : ∀ {α β}, α → β → α) =
  ∀ {α α'} (r : α → α' → Prop),
    ∀ {β β'} (s : β → β' → Prop),
      ∀ x x', r x x' →
        ∀ y y', s y y' →
          r (f x y) (f x' y')
:= rfl
