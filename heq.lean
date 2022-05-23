lemma prod_inj {α₁ β₁ α₂ β₂} :
  (α₁ × β₁) = (α₂ × β₂) → α₁ = α₂ ∧ β₁ = β₂ :=
begin
  by_cases ∃ (x : α₁), true,
end

lemma heq_to_eq {α β} {motive : Π {α}, α → Sort*} {x : α} {y : β} :
  x == y → (Π {x : β}, x = y → motive x) → motive x :=
λ h f, let ht := type_eq_of_heq h, hx := cast_heq ht x in
  cast (by { congr, exact ht.symm, exact hx }) (f (eq_of_heq (hx.trans h)))

/-
    ((@eq.rec _ _
        (λ (α), ∀ (x' : α), (cast ht x) == x' → motive (cast ht x) = motive x')
        (λ (_ : β) hx', eq_of_heq hx' ▸ rfl) _ ht.symm)
     x hx)
     -/

lemma heq_to_eq' {α₁ α₂ β₁ β₂} {motive : Π {α₁ α₂}, α₁ × α₂ → Sort*} {x : α₁ × α₂} {y : β₁ × β₂} :
  x == y → (Π {x : β₁ × β₂}, x = y → motive x) → motive x :=
λ h f, let ht := type_eq_of_heq h, hx := cast_heq ht x in
  cast (by { have := prod_inj ht.symm, congr, exact this.left, exact this.right, exact hx }) (f (eq_of_heq (hx.trans h)))

theorem prod.mk.inj' {α₁ β₁ α₂ β₂} {x₁ : α₁} {y₁ : β₁} {x₂ : α₂} {y₂ : β₂} :
  (x₁, y₁) == (x₂, y₂) → x₁ == x₂ ∧ y₁ == y₂ :=
begin
  intro h,
  exact @heq_to_eq' _ _ _ _ (λ α₁ α₂ ⟨x₁, y₁⟩, x₁ == x₂ ∧ y₁ == y₂) _ _ h (λ ⟨_, _⟩, and.imp heq_of_eq heq_of_eq ∘ prod.mk.inj),
end

theorem prod.mk.inj_iff' {α₁ α₂ β₁ β₂} {a₁ : α₁} {a₂ : α₂} {b₁ : β₁} {b₂ : β₂} :
  (a₁, b₁) == (a₂, b₂) ↔ a₁ == a₂ ∧ b₁ == b₂ :=
begin
  split,
    exact prod.mk.inj',
  intro h,
  cases h with ha hb,
  apply ha.rec_on,
  apply hb.rec_on,
  refl,
end
