def or_to_psum' {α β} (h : α ∨ β) : ∃ h' : psum α β, @or.rec α β (Prop) (λ x, h' = psum.inl x) (λ y, h' = psum.inr y) h :=
sorry
#check @or.rec

def or_to_psum' {α β} (h : α ∨ β) : ∃ h' : psum α β, @psum.rec α β (λ h', Prop) (λ x, h = or.inl x) (λ y, h = or.inr y) h' :=
classical.choice $ h.elim (λ x, ⟨⟨psum.inl x, rfl⟩⟩) (λ y, ⟨⟨psum.inr y, rfl⟩⟩)

noncomputable def or_to_psum {α β} (h : α ∨ β) : psum α β :=
classical.some $ or_to_psum' h

/-
noncomputable def or_to_psum {α β} : α ∨ β → psum α β :=
classical.choice ∘ or.rec (nonempty.intro ∘ psum.inl) (nonempty.intro ∘ psum.inr)
-/

set_option pp.proofs true
lemma or_to_psum_inl {α β} (x : α) : or_to_psum (or.inl x) = @psum.inl α β x :=
begin
  change classical.some (or_to_psum' (or.inl x)) = _,
  generalize h' : classical.some (or_to_psum' (or.inl x)) = h,
  have := classical.some_spec (or_to_psum' (or.inl x)),
  rw h' at this,
  cases h,
    refl,
    dsimp at this,
    simp at this,
end
