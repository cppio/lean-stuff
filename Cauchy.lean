import Mathlib

set_option autoImplicit false

variable {α : Type*} [MetricSpace α]

def HasLimit (f : ℕ → α) (x : α) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (f n) x < ε

theorem HasLimit.const (x : α) : HasLimit (fun _ => x) x :=
  by simp +contextual [HasLimit]

theorem HasLimit.unique {f} {x y : α} : HasLimit f x → HasLimit f y → x = y := by
  intro hx hy
  apply MetricSpace.eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  rewrite [← forall_lt_iff_le']
  intro ε hε
  let ⟨N₁, h₁⟩ := hx (ε / 2) (by simp [hε])
  let ⟨N₂, h₂⟩ := hy (ε / 2) (by simp [hε])
  apply lt_of_le_of_lt
  . apply dist_triangle
    exact f (N₁ ⊔ N₂)
  apply lt_of_lt_of_eq
  . apply add_lt_add
    . rewrite [dist_comm]
      apply h₁
      simp
    . apply h₂
      simp
  simp

theorem HasLimit.sum {f₁ f₂} {x₁ x₂ : ℝ} : HasLimit f₁ x₁ → HasLimit f₂ x₂ → HasLimit (f₁ + f₂) (x₁ + x₂) := by
  intro h₁ h₂ ε hε
  replace ⟨N₁, h₁⟩ := h₁ (ε / 2) (by simp [hε])
  replace ⟨N₂, h₂⟩ := h₂ (ε / 2) (by simp [hε])
  exists N₁ ⊔ N₂
  intro n hn
  simp at hn
  simp [dist]
  rewrite [add_sub_add_comm]
  apply lt_of_le_of_lt
  . apply abs_add_le
  apply lt_of_lt_of_eq (add_lt_add (h₁ n hn.left) (h₂ n hn.right))
  simp

theorem HasLimit.mono {f₁ f₂} {x₁ x₂ : ℝ} : (∀ n, f₁ n ≤ f₂ n) → HasLimit f₁ x₁ → HasLimit f₂ x₂ → x₁ ≤ x₂ := by
  intro h h₁ h₂
  replace h₁ : ∀ ε > 0, ∃ N, ∀ n ≥ N, x₁ - ε < f₁ n := by
    intro ε hε
    let ⟨N, h⟩ := h₁ ε hε
    exists N
    intro n hn
    specialize h n hn
    simp [dist, abs_lt] at h
    exact sub_left_lt_of_lt_add h.left
  replace h₂ : ∀ ε > 0, ∃ N, ∀ n ≥ N, f₂ n < x₂ + ε := by
    intro ε hε
    let ⟨N, h⟩ := h₂ ε hε
    exists N
    intro n hn
    specialize h n hn
    simp [dist, abs_lt] at h
    exact lt_add_of_tsub_lt_left h.right
  have : ∀ ε > 0, x₁ - ε < x₂ + ε := by
    intro ε hε
    let ⟨N₁, h₁⟩ := h₁ ε hε
    let ⟨N₂, h₂⟩ := h₂ ε hε
    exact lt_trans (lt_of_lt_of_le (h₁ (N₁ ⊔ N₂) (by simp)) (h (N₁ ⊔ N₂))) (h₂ (N₁ ⊔ N₂) (by simp))
  apply le_of_forall_lt
  intro x hx
  specialize this ((x₁ - x) / 2)
  simp [hx, ← sub_lt_iff_lt_add, sub_sub] at this
  exact this

def IsCauchy (f : ℕ → α) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (f n) (f N) < ε

def IsCauchy.isCauchy' {f : ℕ → α} (hf : IsCauchy f) : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, dist (f n) (f m) < ε :=
  fun ε hε =>
    let ⟨N, h⟩ := hf (ε / 2) (div_pos hε two_pos)
    ⟨N, fun n hn m hm => lt_of_le_of_lt (dist_triangle _ (f N) _) (lt_of_lt_of_eq (add_lt_add (h n hn) (@dist_comm α .. ▸ h m hm)) (add_halves ε))⟩

class Complete (α) [MetricSpace α] where
  complete {f : ℕ → α} : IsCauchy f → ∃ x, HasLimit f x

instance : Complete ℝ where
  complete hf :=
    let ⟨x, hx⟩ := CompleteSpace.complete (Metric.cauchySeq_iff'.mpr hf)
    ⟨x, Metric.tendsto_atTop.mp hx⟩

def Completion α [MetricSpace α] :=
  @Quot { f : ℕ → α // IsCauchy f } fun f₁ f₂ => HasLimit (fun n => dist (f₁.val n) (f₂.val n)) 0

def IsCauchy.dist {f₁ f₂ : ℕ → α} (hf₁ : IsCauchy f₁) (hf₂ : IsCauchy f₂) : IsCauchy (fun n => dist (f₁ n) (f₂ n)) := by
  intro ε hε
  let ⟨N₁, h₁⟩ := hf₁.isCauchy' (ε / 2) (div_pos hε two_pos)
  let ⟨N₂, h₂⟩ := hf₂.isCauchy' (ε / 2) (div_pos hε two_pos)
  exists N₁ ⊔ N₂
  intro n hn
  simp at hn
  simp [Dist.dist, abs_lt]
  constructor
  . apply lt_of_le_of_lt
    . apply dist_triangle
      exact f₁ n
    apply lt_of_le_of_lt
    . apply add_le_add_left
      apply dist_triangle
      exact f₂ n
    apply lt_trans
    . apply add_lt_add_right
      . apply h₁
        . simp
        . exact hn.left
    apply lt_of_lt_of_eq
    . apply add_lt_add_left
      apply add_lt_add_left
      . rewrite [dist_comm]
        apply h₂
        . simp
        . exact hn.right
    simp [add_comm _ (ε / 2), ← add_assoc]
  . rewrite [sub_lt_iff_lt_add] 
    apply lt_of_le_of_lt
    . apply dist_triangle
      exact f₁ (N₁ ⊔ N₂)
    apply lt_of_le_of_lt
    . apply add_le_add_left
      apply dist_triangle
      exact f₂ (N₁ ⊔ N₂)
    apply lt_trans
    . apply add_lt_add_right
      . apply h₁ n hn.left
        simp
    apply lt_of_lt_of_eq
    . apply add_lt_add_left
      apply add_lt_add_left
      . rewrite [dist_comm]
        apply h₂ n hn.right
        simp
    simp [add_comm _ (ε / 2), ← add_assoc]

noncomputable instance : Dist (Completion α) where
  dist := by
    refine Quot.lift (fun f₁ => Quot.lift (fun f₂ => Classical.choose <| Complete.complete <| f₁.property.dist f₂.property) ?_) ?_
    . intro f₂ f₂' h
      dsimp
      generalize hx : Classical.choose _ = x
      replace hx := hx ▸ Classical.choose_spec _
      generalize hx' : Classical.choose _ = x'
      replace hx' := hx' ▸ Classical.choose_spec _
      symm
      apply hx'.unique
      intro ε hε
      let ⟨N₁, h₁⟩ := h (ε / 2) (by simp [hε])
      let ⟨N₂, h₂⟩ := hx (ε / 2) (by simp [hε])
      exists N₁ ⊔ N₂
      intro n hn
      simp at hn
      apply lt_of_le_of_lt
      . apply dist_triangle
        exact dist (f₁.val n) (f₂.val n)
      apply lt_of_lt_of_eq _ (add_halves ε)
      apply add_lt_add _ (h₂ n hn.right)
      simp [dist, abs_lt]
      specialize h₁ n hn.left
      simp [dist] at h₁
      constructor
      . apply lt_of_le_of_lt
        . apply dist_triangle
          exact f₂'.val n
        rewrite [add_comm]
        apply add_lt_add_right
        rewrite [dist_comm]
        exact h₁
      . rewrite [sub_lt_iff_lt_add']
        apply lt_of_le_of_lt
        . apply dist_triangle
          exact f₂.val n
        apply add_lt_add_left
        exact h₁
    . intro f₁ f₁' h
      apply funext
      apply Quot.ind
      intro f₂
      dsimp
      generalize hx : Classical.choose _ = x
      replace hx := hx ▸ Classical.choose_spec _
      generalize hx' : Classical.choose _ = x'
      replace hx' := hx' ▸ Classical.choose_spec _
      symm
      apply hx'.unique
      intro ε hε
      let ⟨N₁, h₁⟩ := h (ε / 2) (by simp [hε])
      let ⟨N₂, h₂⟩ := hx (ε / 2) (by simp [hε])
      exists N₁ ⊔ N₂
      intro n hn
      simp at hn
      apply lt_of_le_of_lt
      . apply dist_triangle
        exact dist (f₁.val n) (f₂.val n)
      apply lt_of_lt_of_eq _ (add_halves ε)
      apply add_lt_add _ (h₂ n hn.right)
      simp [dist, abs_lt]
      specialize h₁ n hn.left
      simp [dist] at h₁
      constructor
      . apply lt_of_le_of_lt
        . apply dist_triangle
          exact f₁'.val n
        apply add_lt_add_right
        exact h₁
      . rewrite [sub_lt_iff_lt_add']
        apply lt_of_le_of_lt
        . apply dist_triangle
          exact f₁.val n
        rewrite [add_comm]
        apply add_lt_add_left
        rewrite [dist_comm]
        exact h₁

noncomputable instance : MetricSpace (Completion α) where
  dist_self := by
    apply Quot.ind
    intro f
    dsimp [dist]
    generalize hx : Classical.choose _ = x
    replace hx := hx ▸ Classical.choose_spec _
    simp at hx
    exact hx.unique (.const 0)
  dist_comm := by
    apply Quot.ind
    intro f₁
    apply Quot.ind
    intro f₂
    simp [dist, dist_comm]
  dist_triangle := by
    apply Quot.ind
    intro f₁
    apply Quot.ind
    intro f₂
    apply Quot.ind
    intro f₃
    dsimp [dist]
    generalize hx₁ : Classical.choose _ = x₁
    replace hx₁ := hx₁ ▸ Classical.choose_spec _
    generalize hx₂ : Classical.choose _ = x₂
    replace hx₂ := hx₂ ▸ Classical.choose_spec _
    generalize hx₃ : Classical.choose _ = x₃
    replace hx₃ := hx₃ ▸ Classical.choose_spec _
    apply hx₁.mono _ (hx₂.sum hx₃)
    intro n
    apply dist_triangle
  eq_of_dist_eq_zero := by
    apply Quot.ind
    intro f₁
    apply Quot.ind
    intro f₂
    dsimp [dist]
    generalize hx : Classical.choose _ = x
    replace hx := hx ▸ Classical.choose_spec _
    intro h
    cases h
    exact Quot.sound hx

set_option maxHeartbeats 300000 in
instance : Complete (Completion α) where
  complete {f} hf := by
    generalize h : (fun n => (f n).out) = f'
    replace h : f = fun n => .mk _ (f' n) := by simp [← h]
    cases h
    have := fun n => Classical.indefiniteDescription _ ((f' n).property (1 / (n + 1)) (by simp; exact n.cast_add_one_pos))
    refine ⟨.mk _ ⟨fun n => (f' n).val (this n).val, ?_⟩, ?_⟩
    . intro ε hε
      let ⟨N₁, h₁⟩ := hf.isCauchy' (ε / 4) (by simp [hε])
      let N := N₁ ⊔ ⌈4 / ε⌉₊
      exists N
      intro n hn
      specialize h₁ n (le_trans (by simp [N]) hn) N (by simp [N])
      dsimp [dist] at h₁
      generalize hx : Classical.choose _ = x at h₁
      replace hx := hx ▸ Classical.choose_spec _
      let ⟨N₂, h₂⟩ := hx (ε / 4) (by simp [hε])
      let N' := N₂ ⊔ (this n).val ⊔ (this N).val
      apply lt_of_le_of_lt
      . apply dist_triangle
        exact (f' N).val N'
      apply lt_trans (add_lt_add_left ((this N).property N' (by simp [N'])) _)
      apply lt_of_le_of_lt
      . apply add_le_add_right
        apply dist_triangle
        exact (f' n).val N'
      apply lt_trans
      . apply add_lt_add_right
        apply add_lt_add
        . rewrite [dist_comm]
          exact (this n).property N' (by simp [N'])
        . specialize h₂ N' (by simp [N'])
          simp [dist, abs_lt, sub_lt_iff_lt_add] at h₂ 
          exact h₂.right
      have : ⌈4 / ε⌉₊ ≤ N := by simp [N]
      simp at this
      replace := one_div_lt_one_div_of_lt (by simp [hε]) (lt_of_le_of_lt (c := (N + 1 : ℝ)) this (by simp))
      rewrite [← div_mul, mul_comm, mul_one_div] at this
      apply lt_of_lt_of_eq
      . apply add_lt_add _ this
        swap
        apply add_lt_add _ (add_lt_add_left h₁ _)
        swap
        apply lt_of_le_of_lt _ this
        apply one_div_le_one_div_of_le N.cast_add_one_pos
        . simp
          exact hn
      ring
    . intro ε hε
      let ⟨N, h⟩ := hf.isCauchy' (ε / 5) (by simp [hε])
      exists N
      intro n hn
      dsimp [dist]
      generalize hx : Classical.choose _ = x
      replace hx := hx ▸ Classical.choose_spec _
      let ⟨N₁, h₁⟩ := hx (ε / 5) (by simp [hε])
      let ⟨N₂, h₂⟩ := (f' n).property.isCauchy' (ε / 5) (by simp [hε])
      let N' := N ⊔ N₁ ⊔ N₂ ⊔ ⌈5 / ε⌉₊
      specialize h n hn N' (by simp [N'])
      dsimp [dist] at h
      generalize hx' : Classical.choose _ = x' at h
      replace hx' := hx' ▸ Classical.choose_spec _
      let ⟨N₃, h₃⟩ := hx' (ε / 5) (by simp [hε])
      let N'' := N₂ ⊔ N₃ ⊔ this N'
      specialize h₁ N' (by simp [N'])
      specialize h₂ N' (by simp [N']) N'' (by simp [N''])
      specialize h₃ N'' (by simp [N''])

      apply lt_trans
      . simp [dist, abs_lt] at h₁
        exact h₁.left
      apply lt_of_lt_of_eq
      . apply add_lt_add_left
        apply lt_of_le_of_lt
        . apply dist_triangle
          exact (f' n).val N''
        apply add_lt_add h₂
        apply lt_of_le_of_lt
        . apply dist_triangle
          exact (f' N').val N''
        apply add_lt_add
        . simp [dist, abs_lt, sub_lt_iff_lt_add] at h₃
          exact lt_trans h₃.right (add_lt_add_left h _)
        apply lt_trans ((this N').property N'' (by simp [N'']))
        change _ < ε / 5
        have : ⌈5 / ε⌉₊ ≤ N' := by simp [N']
        simp at this
        rewrite [one_div_lt]
        . apply lt_of_le_of_lt
          . simp
            exact this
          . simp
        . exact N'.cast_add_one_pos
        . simp [hε]
      ring
