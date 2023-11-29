variable {P : Nat → Prop} [I : DecidablePred P]

theorem wellFoundedPrinciple (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬P m := by
  cases h with | intro n h =>
  have : ∀ m, m ≤ n → (∃ n, P n ∧ ∀ m, m < n → ¬P m) ∨ (∀ k, k < m → ¬P k) := by
    intro m hm
    induction m with
    | zero => exact .inr λ _ hk => nomatch hk
    | succ m ih =>
      specialize ih <| Nat.le_of_succ_le hm
      cases ih with
      | inl ih => exact .inl ih
      | inr ih =>
        cases I m with
        | isFalse h' =>
          refine .inr ?_
          intro k hk
          cases hk with
          | refl => exact h'
          | step hk => exact ih k hk
        | isTrue h' => exact .inl ⟨m, h', ih⟩
  cases this n .refl with
  | inl h' => exact h'
  | inr h' => exact ⟨n, h, h'⟩

def foo {P : Nat → Prop} [I : DecidablePred P] (h : ∃ n, P n ∧ ∀ k, k < n → ¬P k) : Σ' n, P n :=
  match I .zero with
  | .isTrue h => ⟨.zero, h⟩
  | .isFalse hn =>
    let ⟨n, hn⟩ := @foo (P ·.succ) _ (match h with | ⟨.zero, hn', _⟩ => hn hn' |>.elim | ⟨.succ n, hn, hn'⟩ => ⟨n, hn, λ k hk => hn' k.succ (Nat.succ_lt_succ hk)⟩)
    ⟨n.succ, hn⟩
termination_by _ => Classical.choose h
decreasing_by {
  simp_wf
  match h with
  | ⟨.zero, hn', _⟩ => cases hn hn'
  | ⟨.succ n, hn', hn''⟩ =>
  have h' : ∃ n, P n.succ ∧ ∀ k, k < n → ¬ P k.succ := ⟨n, hn', λ k hk => hn'' k.succ (Nat.succ_lt_succ hk)⟩
  generalize hx : Classical.choose h = x
  generalize hy : Classical.choose h' = y
  apply Nat.gt_of_not_le
  intro hxy
  have := hx ▸ Classical.choose_spec h
  cases x with
  | zero => cases hn this.1
  | succ x => cases hy ▸ Classical.choose_spec h' |>.2 x hxy this.1
}

def bar : (∃ n, P n) → Σ' n, P n := foo ∘ wellFoundedPrinciple

#print axioms bar

#check bar
