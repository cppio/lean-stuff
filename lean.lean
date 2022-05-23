section

variables {p q : Prop}

theorem not_not : p → ¬¬p
  := λ hp hnp, hnp hp

theorem not.not : ¬¬¬p → ¬p
  := λ hp, hp ∘ not_not

theorem not.imp : ¬¬p → (p → q) → ¬¬q
  := λ hp hpq hnq, hp (hnq ∘ hpq)

theorem not.not_not_and_not_not : ¬¬(¬¬p ∧ ¬¬q) → (¬¬p ∧ ¬¬q)
  := λ hpq, ⟨λ hnp, hpq (λ ⟨hp, _⟩, hp hnp), λ hnq, hpq (λ ⟨_, hq⟩, hq hnq)⟩

theorem not.not_not_and : ¬¬(¬¬p ∧ ¬¬q) → ¬¬(p ∧ q)
  := λ hpq hnpq, hpq (λ ⟨hp', hq'⟩, hp' (λ hp, hq' (λ hq, hnpq ⟨hp, hq⟩)))

theorem not.not_not_or : ¬¬(¬¬p ∨ ¬¬q) → ¬¬(p ∨ q)
  := λ hpq' hnpq, hpq' (λ hpq, hpq.elim (λ hp, hp (hnpq ∘ or.inl)) (λ hq, hq (hnpq ∘ or.inr)))

end

/-
example : p ∧ q → ¬(¬p ∨ ¬q) := λ ⟨h₁, h₂⟩ h, h.elim (not_not h₁) (not_not h₂)
example : ¬p ∨ ¬q → ¬(p ∧ q) := λ h ⟨h₁, h₂⟩, h.elim (not_not h₁) (not_not h₂)

example : ¬p ∧ ¬q → ¬(p ∨ q) := λ ⟨h₁, h₂⟩ h, h.elim h₁ h₂
example : p ∨ q → ¬(¬p ∧ ¬q) := λ h ⟨h₁, h₂⟩, h.elim h₁ h₂

example : ¬(p ∨ q) → ¬p ∧ ¬q := λ h, ⟨h ∘ or.inl, h ∘ or.inr⟩
example : ¬(¬p ∧ ¬q) → ¬¬(p ∨ q) := λ h h', h ⟨h' ∘ or.inl, h' ∘ or.inr⟩

lemma push : ¬¬p ∧ ¬¬q → ¬¬(p ∧ q) := λ ⟨h₁, h₂⟩ h, h₁ (λ hp, h₂ (λ hq, h ⟨hp, hq⟩))

example : ¬(¬p ∨ ¬q) → ¬¬(p ∧ q) := λ h h', push ⟨h ∘ or.inl, h ∘ or.inr⟩ h'
example : ¬(p ∧ q) → ¬¬(¬p ∨ ¬q) := λ h h', push ⟨h' ∘ or.inl, h' ∘ or.inr⟩ h
-/

/-
variables {α : Sort*} {p : α → Prop}

theorem forall_not_not : ¬¬(∀ x, ¬¬p x) → (∀ x, ¬¬p x)
  := λ hnnf x hn, hnnf (λ hf, hf x hn)

theorem not_not_exists : ¬¬(∃ x, ¬¬p x) → ¬¬(∃ x, p x)
  := λ he hne, he (λ ⟨x, hnn⟩, hnn (λ h, hne ⟨x, h⟩))

theorem forall'    : (∀ x,  p x) → ¬(∃ x, ¬p x) := λ  h ⟨x, h'⟩, h' (h  x)
theorem forall_not : (∀ x, ¬p x) → ¬(∃ x,  p x) := λ  h ⟨x, h'⟩, h   x  h'

theorem exists'    : (∃ x,  p x) → ¬(∀ x, ¬p x) := λ ⟨x, h⟩ h' , h'  x  h
theorem exists_not : (∃ x, ¬p x) → ¬(∀ x,  p x) := λ ⟨x, h⟩ h' , h  (h' x)


theorem not_exists : ¬(∃ x, p x) → (∀ x, ¬p x) := λ h x h', h ⟨x, h'⟩

theorem not_forall_not : ¬(∀ x, ¬p x) → ¬¬(∃ x, p x) := (∘ not_exists)


theorem not_exists_iff_forall_not : ¬(∃ x, p x) ↔ (∀ x, ¬p x) := ⟨not_exists, forall_not⟩
theorem not_forall_not_iff_exists : ¬(∀ x, ¬p x) ↔ ¬¬(∃ x, p x) := ⟨not_forall_not, λ h h', h (λ ⟨x, h''⟩, h' x h'')⟩




theorem not_exists_not : ¬(∃ x, ¬p x) → ¬¬(∀ x, p x) := λ h h', h _

theorem not_forall : ¬(∀ x, p x) → ¬¬(∃ x, ¬p x) := sorry

example : (∀ x, ¬p x) ↔ ¬(∃ x, p x) := ⟨forall_not, not_exists⟩


theorem not_forall : ¬(∀ x, p x) → ¬¬(∃ x, ¬p x) := λ h h', h (λ x, _)


example : (∀ x, ¬¬p x) → ¬¬(∀ x, p x) := λ h h', h' (λ x, let y := h x in _)
-/
