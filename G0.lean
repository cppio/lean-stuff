import Mathlib

theorem Nat.log2_add_one_le_self {n} : log2 (n + 1) ≤ n :=
  by simp [Nat.le_iff_lt_add_one, Nat.log2_lt, Nat.lt_two_pow_self]

theorem string_eq_iff {s t : Σ n, Fin n → Bool} : s = t ↔ ∃ h, ∀ i, s.snd i = t.snd (i.cast h) := by
  constructor
  . intro (.refl _)
    simp
  . intro h
    ext
    exact h.fst
    apply heq_of_eq_cast (h.fst ▸ rfl)
    funext i
    rewrite [h.snd]
    cases s
    cases h.fst
    simp

instance : Denumerable (Σ n, Fin n → Bool) where
  encode | ⟨n, s⟩ => 2 ^ n - 1 + .ofBits s
  decode m := let n := (m + 1).log2; some ⟨n, fun i => (m - (2 ^ n - 1)).testBit i⟩
  encodek := by
    intro ⟨n, s⟩
    simp only [Option.some.injEq, string_eq_iff]
    suffices _ by
      use this
      intro ⟨i, h⟩
      simp [this] at h
      simp [this, Nat.testBit_ofBits, h]
    simp [Nat.log2_eq_log_two, Nat.log_eq_iff]
    constructor
    . omega
    apply Nat.lt_of_le_of_lt
    . apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      apply Nat.le_pred_of_lt
      apply Nat.ofBits_lt_two_pow
    simp [Nat.pow_succ']
    rewrite [Nat.add_assoc, Nat.sub_add_cancel Nat.one_le_two_pow, ← Nat.sub_add_comm Nat.one_le_two_pow]
    simp +arith
  decode_inv m := by
    simp
    symm
    rewrite [← Nat.sub_eq_iff_eq_add']
    . apply Nat.eq_of_testBit_eq
      intro i
      simp [Nat.testBit_ofBits]
      intro h
      apply Nat.lt_of_succ_le
      simp [Nat.le_log2, Nat.pow_succ']
      apply Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.ge_two_pow_of_testBit h))
      clear i h
      simp [Nat.mul_sub]
      simp [← Nat.pow_succ']
      trans
      swap
      . apply Nat.add_le_add_left
        apply Nat.sub_le_sub_right
        exact Nat.le_of_lt Nat.lt_log2_self
      . omega
    . simp [Nat.log2_self_le]

def s n : Fin n → Bool :=
  let ⟨m, x⟩ := Denumerable.ofNat (Σ n, Fin n → Bool) n
  fun i => if h : i < m then x ⟨i, h⟩ else false

theorem s_dense {m} (t : Fin m → Bool) : ∃ n, ∃ (h : m ≤ n), ∀ i : Fin m, t i = s n (i.castLE h) := by
  use Denumerable.toEncodable.encode (⟨m, t⟩ : Σ n, Fin n → Bool)
  simp [Encodable.encode]
  have : (2 ^ m - 1 + Nat.ofBits t + 1).log2 = m := by
    apply Nat.le_antisymm
    . apply Nat.le_of_lt_succ
      rewrite [Nat.log2_lt (by simp)]
      apply Nat.lt_of_le_of_lt
      . apply Nat.add_le_add_right
        apply Nat.add_le_add_left
        apply Nat.le_pred_of_lt
        apply Nat.ofBits_lt_two_pow
      simp [Nat.pow_succ']
      rewrite [Nat.add_assoc, Nat.sub_add_cancel Nat.one_le_two_pow, ← Nat.sub_add_comm Nat.one_le_two_pow]
      simp +arith
    . simp [Nat.le_log2]
      omega
  use Nat.le_trans (Nat.le_of_eq this.symm) Nat.log2_add_one_le_self
  intro i
  simp [s]
  simp only [Denumerable.ofNat, Encodable.decode]
  simp [this]

section

variable {α} [TopologicalSpace α] [DiscreteTopology α]

instance {n} : HAppend (Fin n → α) (Nat → α) (Nat → α) where
  hAppend s t i := if h : i < n then s ⟨i, h⟩ else t (i - n)

def N {n} (t : Fin n → α) : Set (Nat → α)
  | x => ∀ i, t i = x i

instance [Inhabited α] {n} {t : Fin n → α} : Nonempty (N t) :=
  ⟨fun i => if h : i < n then t ⟨i, h⟩ else default, fun i => by simp⟩

theorem mem_N {α : Type*} {n} {t : Fin n → α} {x} : (x ∈ N t) = ∀ i, t i = x i := rfl

theorem N_agree {α : Type*} {n₁ n₂} {t₁ : Fin n₁ → α} {t₂ : Fin n₂ → α} (hn : n₁ ≤ n₂) (ht : ∀ i, t₁ i = t₂ (i.castLE hn)) : N t₂ ⊆ N t₁
  | _, hx, i => (ht i).trans (hx (i.castLE hn))

theorem N_open {n} {t : Fin n → α} : IsOpen (N t) := by
  simp [isOpen_pi_iff]
  intro x h
  use .range n, fun i b => if h : i < n then t ⟨i, h⟩ = b else True
  simp [mem_N] at h
  simp [Membership.mem, Set.Mem, h]
  intro y
  simp [mem_N]
  intro hy i
  rewrite [h i]
  apply hy <;> exact i.isLt

theorem N_closed {x : α} : IsClosed (N ![x]) := by
  constructor
  have : (N ![x])ᶜ = ⋃ y ∈ ({x}ᶜ : Set α), N ![y] := by
    ext z
    simp [mem_N]
    exact ⟨Ne.symm, Ne.symm⟩
  rewrite [this]
  apply isOpen_iUnion
  intro y
  apply isOpen_iUnion
  intro
  apply N_open

theorem contains_basic {U : Set (Nat → α)} (h : IsOpen U) {y} (h' : y ∈ U) : ∃ m, ∃ t : Fin m → α, y ∈ N t ∧ N t ⊆ U := by
  simp [isOpen_pi_iff] at h
  specialize h y h'
  rcases h with ⟨I, u, h₁, h₂⟩
  use I.max.elim 0 (· + 1), fun i => y i
  simp [mem_N]
  intro x h''
  apply h₂
  intro i hi
  refine h'' ⟨i, ?_⟩ ▸ h₁ i hi
  rcases I.le_max hi i rfl with ⟨m, h₁, h₂⟩
  rw [h₁]
  simp!
  exact Nat.lt_succ_of_le h₂

theorem contains_s {U : Set (Nat → Bool)} (h : IsOpen U) (h' : U.Nonempty) : ∃ n, N (s n) ⊆ U := by
  rcases h' with ⟨_, h'⟩
  let ⟨m, t, _, ht⟩ := contains_basic h h'
  let ⟨n, hn, hsn⟩ := s_dense t
  use n
  intro x hx
  apply ht
  intro i
  rw [hsn i]
  apply hx

theorem N_basis : TopologicalSpace.IsTopologicalBasis {A | ∃ m, ∃ t : Fin m → α, A = N t} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  . intro A ⟨m, t, h⟩
    exact h ▸ N_open
  . intro x U mem U_open
    let ⟨m, t, h⟩ := contains_basic U_open mem
    exists _, ⟨m, t, rfl⟩

def treelim {β} (f : ∀ n, (Fin n → α) → (Fin n → β)) (x : Nat → α) (n : Nat) : β :=
  f (n + 1) (fun i => x i) (Fin.last n)

theorem treelim_cont {β} [TopologicalSpace β] [DiscreteTopology β] (f : ∀ n, (Fin n → α) → (Fin n → β)) : Continuous (treelim f) := by
  constructor
  intro A hA
  replace hA := N_basis.open_eq_iUnion hA
  rcases hA with ⟨β, g, h, h'⟩
  cases h
  simp at h' ⊢
  apply isOpen_iUnion
  intro i
  specialize h' i
  rcases h' with ⟨m, t, h⟩
  rewrite [h]
  clear g h i β
  simp [Set.preimage, mem_N, treelim]
  simp [isOpen_pi_iff]
  intro g hg
  replace hg := funext hg
  cases hg
  use .range m, fun n => {g n}
  simp
  intro x
  simp
  intro hx i
  congr
  funext j
  simp [hx j (by omega)]

end

def 𝔾₀ (x y : Nat → Bool) : Prop :=
  ∃ n b, ∃ z : Nat → Bool, x = s n ++ (![b] ++ z) ∧ y = s n ++ (![!b] ++ z)

instance : IsSymm _ 𝔾₀ where
  symm _ _ | ⟨n, b, z, h₁, h₂⟩ => ⟨n, !b, z, h₂, b.not_not.symm ▸ h₁⟩

instance : IsIrrefl _ 𝔾₀ where
  irrefl x := by
    intro ⟨n, b, z, h₁, h₂⟩
    replace h₁ := congrFun h₁ n
    replace h₂ := congrFun h₂ n
    simp [s, HAppend.hAppend] at h₁ h₂
    have := h₁.symm.trans h₂
    simp at this

variable {X} [TopologicalSpace X]

theorem IsMeagre.union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t) : IsMeagre (s ∪ t) := by
  have := isMeagre_iUnion (s := fun n => if n = 0 then s else t) fun n => by dsimp; split; exact hs; exact ht
  refine Eq.mp ?_ this
  congr
  simp
  ext x
  constructor
  . simp
    intro i
    split <;> simp +contextual
  . intro h
    cases h with simp
    | inl h => use 0; simp [h]
    | inr h => use 1; simp [h]

theorem localize (A : Set X) (bp : BaireMeasurableSet A) (h : ¬IsMeagre A) : ∃ U, IsOpen U ∧ U.Nonempty ∧ IsMeagre (U \ A) := by
  simp [BaireMeasurableSet.iff_residualEq_isOpen] at bp
  rcases bp with ⟨U, hU, h'⟩
  use U, hU
  constructor
  . by_contra hU
    simp [Set.not_nonempty_iff_eq_empty] at hU
    cases hU
    simp [IsMeagre] at h
    simp [Filter.EventuallyEq, EmptyCollection.emptyCollection] at h'
    exact h h'
  . apply Filter.mem_of_superset h'
    intro x hx
    simp at hx ⊢
    intro h
    exact hx.mpr h

theorem dense_iff {A : Set X} : closure A = .univ ↔ ∀ (U : Set X), IsOpen U → U.Nonempty → (A ∩ U).Nonempty := by
  constructor
  . intro h U U_open U_nonempty
    by_contra h'
    have : A ⊆ Uᶜ := fun x hx hu => h' ⟨x, hx, hu⟩
    have := h ▸ closure_minimal this (by simp [U_open])
    simp at this
    simp [this] at U_nonempty
  . intro h
    ext x
    simp
    by_contra hx
    specialize h (closure A)ᶜ
    simp at h
    specialize h ⟨x, hx⟩
    have := Set.inter_subset_inter_right A (Set.compl_subset_compl_of_subset (subset_closure (s := A)))
    simp at this
    rewrite [this] at h
    simp at h

lemma preimage_val_empty_iff {X : Type*} {A B : Set X} : (Subtype.val ⁻¹' A : Set B) = ∅ ↔ A ∩ B = ∅ := by
  constructor
  . intro h
    ext x
    simp
    intro hA hB
    have := congrArg (⟨x, hB⟩ ∈ ·) h
    simp at this
    exact this hA
  . intro h
    ext ⟨x, hB⟩
    simp
    intro hA
    have : x ∈ A ∩ B := ⟨hA, hB⟩
    rewrite [h] at this
    simp at this

theorem somewhere_dense_iff {A : Set X} : (interior (closure A)).Nonempty ↔ ∃ (U : Set X), IsOpen U ∧ U.Nonempty ∧ closure (X := U) (Subtype.val ⁻¹' A) = .univ := by
  constructor
  . intro h
    exists _, by simp, h
    simp [dense_iff]
    intro U U_open
    rcases U_open with ⟨V, V_open, hu⟩
    cases hu
    contrapose
    simp [Set.nonempty_iff_ne_empty, ← Set.preimage_inter, preimage_val_empty_iff]
    intro h'
    have : A ⊆ (V ∩ interior (closure A))ᶜ :=
      fun x hA hV => have : x ∈ A ∩ V ∩ interior (closure A) := ⟨⟨hA, hV.left⟩, hV.right⟩; nomatch h' ▸ this
    have := closure_minimal this (by simp; exact IsOpen.inter V_open isOpen_interior)
    have : ¬(closure A ∩ V ∩ interior (closure A)).Nonempty := fun ⟨x, ⟨hA, hV⟩, hA'⟩ => this hA ⟨hV, hA'⟩
    rewrite [Set.inter_comm, ← Set.inter_assoc, Set.inter_eq_self_of_subset_left interior_subset] at this
    simp [Set.nonempty_iff_ne_empty, Set.inter_comm] at this
    exact this
  . intro ⟨U, U_open, U_nonempty, h⟩
    replace h := fun x => congrArg (x ∈ ·) h
    simp [closure_subtype] at h
    exact U_nonempty.mono <| .trans (interior_maximal h U_open) (interior_mono (closure_mono Set.inter_subset_right))

theorem nowhere_dense_iff {A : Set X} : IsNowhereDense A ↔ ∀ (U : Set X), IsOpen U → U.Nonempty → ∃ V : Set U, IsOpen V ∧ V.Nonempty ∧ Subtype.val ⁻¹' A ∩ V = ∅ := by
  rewrite [← not_iff_not]
  simp [IsNowhereDense, ← Set.nonempty_iff_ne_empty, somewhere_dense_iff, dense_iff]

theorem BaireSpace.iff_open_nonempty_nonmeager : BaireSpace X ↔ ∀ (U : Set X), IsOpen U → U.Nonempty → ¬IsMeagre U := by
  constructor
  . intro _ U U_open U_nonempty U_meager
    simp [IsMeagre, mem_residual] at U_meager
    rcases U_meager with ⟨A, hA, A_Gδ, A_dense⟩
    simp [isGδ_iff_eq_iInter_nat] at A_Gδ
    rcases A_Gδ with ⟨S, S_open, h⟩
    cases h
    have := A_dense.closure.mono (IsClosed.closure_subset_iff (by simp [U_open]) |>.mpr hA) |>.interior_compl
    simp [interior_eq_iff_isOpen.mpr U_open] at this
    cases this
    nomatch U_nonempty
  . intro h
    constructor
    intro S S_open S_dense
    by_contra h'
    simp [Dense] at h'
    simp [← Set.mem_compl_iff, ← interior_compl] at h'
    apply h (interior <| ⋃ n, (S n)ᶜ)
    . simp
    . exact h'
    . simp [isMeagre_iff_countable_union_isNowhereDense]
      use Set.range fun n => (S n)ᶜ
      simp
      constructor
      . intro n
        ext x
        simp [interior_eq_iff_isOpen.mpr (S_open n)]
        exact S_dense n x
      . constructor
        . apply Set.countable_range
        . exact interior_subset

theorem BaireSpace.comeager_nonempty [BaireSpace X] [Nonempty X] {A : Set X} (hA : IsMeagre Aᶜ) : A.Nonempty := by
  have := fun h => BaireSpace.iff_open_nonempty_nonmeager.mp inferInstance (interior Aᶜ) (by simp) h (hA.mono interior_subset)
  simp [Set.nonempty_compl] at this
  by_contra h
  simp [Set.nonempty_iff_ne_empty] at h
  cases h
  replace := fun x => congrArg (x ∈ ·) this
  simp at this

theorem isMeager_subspace {Y : Set X} {A : Set Y} (h : IsMeagre A) : IsMeagre (Subtype.val '' A) := by
  simp [isMeagre_iff_countable_union_isNowhereDense] at h ⊢
  rcases h with ⟨S, S_nowhereDense, S_countable, h⟩
  use (Subtype.val '' ·) '' S
  simp
  refine ⟨?_, S_countable.image _, ?_⟩
  . intro B hB
    specialize S_nowhereDense B hB
    simp [IsNowhereDense] at S_nowhereDense ⊢
    change interior {x | x ∈ closure B} = _ at S_nowhereDense
    simp [closure_subtype] at S_nowhereDense
    rewrite [← compl_compl (interior {x : Y | ↑x ∈ closure (Subtype.val '' B)}), ← closure_compl] at S_nowhereDense
    change {x | x ∈ closure _}ᶜ = _ at S_nowhereDense
    simp only [closure_subtype] at S_nowhereDense
    replace S_nowhereDense := fun x => congrArg (x ∈ ·) S_nowhereDense
    simp at S_nowhereDense
    change Y ⊆ _ at S_nowhereDense
    rewrite [Set.image] at S_nowhereDense
    simp at S_nowhereDense
    have : interior (closure (Subtype.val '' B)) ⊆ (interior (closure (Subtype.val '' B)))ᶜ := by
      trans
      . exact interior_subset
      apply closure_minimal
      . trans
        swap
        . trans
          . exact S_nowhereDense
          simp [← closure_compl]
          apply closure_mono
          intro
          simp
        . simp
      . simp
    simp [Set.subset_compl_iff_disjoint_right] at this
    exact this
  . intro _ hx
    simp
    exact h hx

theorem isMeager_subspace_open {U : Set X} {A : Set U} (hU : IsOpen U) : IsMeagre A ↔ IsMeagre (Subtype.val '' A) := by 
  constructor
  . exact isMeager_subspace
  . simp [isMeagre_iff_countable_union_isNowhereDense]
    intro S nowhereDense countable cover
    use (Subtype.val ⁻¹' ·) '' S
    refine ⟨?_, countable.image _, ?_⟩
    . intro B ⟨C, hC, hC'⟩
      cases hC'
      specialize nowhereDense C hC
      simp [nowhere_dense_iff] at nowhereDense ⊢
      intro V V_open V_nonempty
      specialize nowhereDense (Subtype.val '' V) (IsOpen.isOpenMap_subtype_val hU _ V_open) (V_nonempty.image _)
      rcases nowhereDense with ⟨W, W_open, W_nonempty, hW⟩
      use ((fun x => ⟨x, x, x.property, rfl⟩) ⁻¹' W)
      refine ⟨?_, ?_, ?_⟩
      . simp [IsOpen, instTopologicalSpaceSubtype, TopologicalSpace.induced] at W_open ⊢
        rcases W_open with ⟨W', W_open, h⟩
        cases h
        exists W', W_open
      . rcases W_nonempty with ⟨⟨x', ⟨x, hU⟩, hV, h⟩, hW⟩
        cases h
        refine ⟨⟨⟨x, hU⟩, hV⟩, hW⟩
      . ext ⟨⟨x, hU⟩, hV⟩
        simp
        intro hC hW'
        replace hW := congrArg (⟨x, ⟨x, hU⟩, hV, rfl⟩ ∈ ·) hW
        simp at hW
        exact hW hC hW'
    . simp [cover]

theorem BaireSpace.open_subspace [BaireSpace X] {U : Set X} (U_open : IsOpen U) : BaireSpace U := by
  rewrite [iff_open_nonempty_nonmeager]
  intro V V_open V_nonempty V_meager
  apply iff_open_nonempty_nonmeager.mp (U := U ∩ Subtype.val '' V)
  . infer_instance
  . simp
    exact IsOpen.isOpenMap_subtype_val U_open _ V_open
  . simp [V_nonempty]
  . simp
    rewrite [← isMeager_subspace_open U_open]
    exact V_meager

def Independent (G : X → X → Prop) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ¬G x y

theorem 𝔾₀_independent_meager {A} (bp : BaireMeasurableSet A) : Independent 𝔾₀ A → IsMeagre A := by
  contrapose
  intro nonmeager
  simp [Independent]
  let ⟨U, U_open, U_nonempty, A_comeager'⟩ := localize A bp nonmeager
  let ⟨n, h⟩ := contains_s U_open U_nonempty
  have A_comeager : IsMeagre (N (s n) \ A) := by
    apply Filter.mem_of_superset A_comeager'
    simp
    intro x
    specialize @h x
    simp +contextual [h]
  clear U U_open U_nonempty A_comeager' h
  let γ (x : Nat → Bool) i : Bool := if i = n then !x i else x i
  have γ_cont : Continuous γ := by
    simp [continuous_pi_iff, continuous_discrete_rng]
    intro i
    constructor
    all_goals
      simp [isOpen_pi_iff]
      intro x hx
      use {i}, fun _ => {x i}
      simp [γ] at hx ⊢
      by_cases h : i = n
      . simp [h] at hx ⊢
        simp [Set.preimage, hx]
      . simp [h] at hx ⊢
        exact hx
  have γ_invol : γ.Involutive := by
    intro x
    funext i
    dsimp [γ]
    split <;> simp
  let γ' : Homeomorph (Nat → Bool) (Nat → Bool) := {
    toFun := γ
    invFun := γ
    left_inv := γ_invol
    right_inv := γ_invol
    continuous_toFun := γ_cont
    continuous_invFun := γ_cont
  }
  have γA_comeager : IsMeagre (γ' '' (N (s n) \ A)) := by
    dsimp [IsMeagre]
    rewrite [← Set.image_compl_eq γ'.bijective, ← γ'.residual_map_eq]
    simp
    exact A_comeager
  rewrite [Set.image_diff γ'.injective] at γA_comeager
  have γ_stable : γ' '' N (s n) = N (s n) := by
    ext x
    simp [γ']
    constructor
    . simp
      intro y hy (.refl _) i
      simp [γ, Nat.ne_of_lt i.isLt]
      exact hy i
    . intro hx
      use γ x
      refine ⟨?_, γ_invol x⟩
      intro i
      simp [γ, Nat.ne_of_lt i.isLt]
      exact hx i
  rw [γ_stable] at γA_comeager
  have := A_comeager.union γA_comeager

  have := isMeager_subspace_open (N_open (t := s n)) (A := Subtype.val ⁻¹' (N (s n) \ (A ∩ γ' '' A)))
  simp [Set.diff_inter] at this
  have := this.mpr ‹_›
  simp [← Set.compl_eq_univ_diff, ← Set.compl_inter, ← Set.preimage_inter] at this

  let ⟨⟨_, hγN⟩, hγA, x, hA, h⟩ := (BaireSpace.open_subspace N_open).comeager_nonempty this
  cases h
  simp at hγA
  change γ x ∈ N (s n) at hγN
  rewrite [← γ_stable] at hγN
  simp at hγN
  rcases hγN with ⟨x', hN, h⟩
  replace h := congrArg γ h
  simp [γ', γ_invol x, γ_invol x'] at h
  cases h
  refine ⟨x, hA, γ x, hγA, n, x n, fun i => x (i + n + 1), ?_, ?_⟩
  . funext i
    simp [HAppend.hAppend]
    split
    . exact (hN ⟨i, ‹_›⟩).symm
    . split <;> congr <;> omega
  . funext i
    simp [HAppend.hAppend]
    split
    . simp [γ, Nat.ne_of_lt ‹_›]; exact (hN ⟨i, ‹_›⟩).symm
    next h =>
      have := Nat.le_of_not_gt h
      split
      next h =>
        simp [Nat.sub_eq_zero_iff_le] at h
        cases Nat.le_antisymm this h
        simp [γ]
      next h =>
        simp [Nat.sub_eq_zero_iff_le] at h
        simp [Nat.ne_of_gt h, γ]
        congr
        omega

structure Approximation (n : Nat) where
  f : (Fin n → Bool) → (Fin n → Nat)
  g : ∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → (Fin n → Nat)

def append {n k} (a : Fin k → Bool) (b : Bool) (c : Fin (n - (k + 1)) → Bool) (i : Fin n) : Bool :=
  if h : i < k then a ⟨i, h⟩ else if h' : i = k then b else c (.subNat (k + 1) (i.cast (by omega)) (by simp; omega))

structure Realization (n : Nat) (a : Approximation n) (Θ : (Nat → Nat) → X × X) (Φ : (Nat → Nat) → X) where
  φ : (Fin n → Bool) → (Nat → Nat)
  γ : ∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → (Nat → Nat)
  φ_f : ∀ s, φ s ∈ N (a.f s)
  γ_g : ∀ k t, γ k t ∈ N (a.g k t)
  edge : ∀ k t, Θ (γ k t) = (Φ (φ (append (s k) false t)), Φ (φ (append (s k) true t)))

structure Extension (n : Nat) (a : Approximation n) (b : Approximation (n + 1)) where
  f : ∀ s c i, a.f s i = b.f (Fin.lastCases c s) i.castSucc
  g : ∀ k t c i, a.g k t i = b.g k.castSucc (fun i => (i.cast (by simp; omega)).lastCases c t) i.castSucc

structure SetRealization (Y : Set X) {n a Θ Φ} (α : Realization n a Θ Φ) where
  image : Set.range (fun x => Φ (α.φ x)) ⊆ Y

def A {n} (a : Approximation n) (s : Fin n → Bool) (Y : Set X) (Θ : (Nat → Nat) → X × X) (Φ : (Nat → Nat) → X) : Set (Nat → Nat) :=
  { x | ∃ α : Realization n a Θ Φ, SetRealization Y α ∧ x = α.φ s }

structure GKernel (Y : Set X) (Θ Φ) where
  prop : ∀ n : Nat, ∀ a : Approximation n, ∀ s : Fin n → Bool, Independent (fun x y => ∃ z, Θ z = (Φ x, Φ y)) (A a s Y Θ Φ) → A a s Y Θ Φ = ∅

noncomputable def amalgamation {n} Θ Φ {a : Approximation n} (α₀ α₁ : @Realization X n a Θ Φ) (h : ∃ z, Θ z = (Φ (α₀.φ (s n)), Φ (α₁.φ (s n)))) : Realization (n + 1) ⟨fun s => Fin.lastCases (if s (Fin.last n) then α₁.φ (fun i => s i.castSucc) n else α₀.φ (fun i => s i.castSucc) n) (a.f fun i => s i.castSucc), Fin.lastCases (fun _ i => Classical.choose h i) fun k t => Fin.lastCases (if t (Fin.last (n - k - 1) |>.cast (by simp; omega)) then α₁.γ k (fun i => t (i.castSucc.cast (by simp; omega))) n else α₀.γ k (fun i => t (i.castSucc.cast (by simp; omega))) n) (a.g k fun i => t (i.castSucc.cast (by simp; omega)))⟩ Θ Φ where
  φ s := if s (Fin.last n) then α₁.φ fun i => s i.castSucc else α₀.φ fun i => s i.castSucc
  γ := Fin.lastCases (fun _ => Classical.choose h) fun k t => if t (Fin.last (n - k - 1) |>.cast (by simp; omega)) then α₁.γ k fun i => t (i.castSucc.cast (by simp; omega)) else α₀.γ k fun i => t (i.castSucc.cast (by simp; omega))
  φ_f s := by
    split
    . intro i
      cases i using Fin.lastCases with
      | last => simp [*]
      | cast i => simp; exact α₁.φ_f (fun i => s i.castSucc) i
    . intro i
      cases i using Fin.lastCases with
      | last => simp [*]
      | cast i => simp; exact α₀.φ_f (fun i => s i.castSucc) i
  γ_g k t := by
    cases k using Fin.lastCases with
    | last => intro; simp
    | cast k =>
      simp
      split
      . intro i
        cases i using Fin.lastCases with
        | last => simp
        | cast i => simp; exact α₁.γ_g k (fun i => t (i.castSucc.cast (by simp; omega))) i
      . intro i
        cases i using Fin.lastCases with
        | last => simp
        | cast i => simp; exact α₀.γ_g k (fun i => t (i.castSucc.cast (by simp; omega))) i
  edge k t := by
    cases k using Fin.lastCases with
    | last =>
      simp [append]
      exact Classical.choose_spec h
    | cast k =>
      have (b) : append (s ↑k) b t (Fin.last n) = t (Fin.last (n - k - 1) |>.cast (by simp; omega)) := by
        have : ¬n < k := by simp
        have : n ≠ k := by omega
        simp [append, *]
        congr
        ext
        simp
        omega
      simp [this]
      split
      . rewrite [α₁.edge k (fun i => t (i.castSucc.cast (by simp; omega)))]
        rfl
      . rewrite [α₀.edge k (fun i => t (i.castSucc.cast (by simp; omega)))]
        rfl

def Realized {n} (a : Approximation n) (Y : Set X) (Θ : (Nat → Nat) → X × X) (Φ : (Nat → Nat) → X) : Prop :=
  ∃ α : Realization n a Θ Φ, SetRealization Y α

example {n a Y Θ Φ} : @Realized X n a Y Θ Φ ↔ ∀ s, (A a s Y Θ Φ).Nonempty := by
  simp [Realized, A]
  constructor
  . intro ⟨α, h⟩ s
    exact ⟨α.φ s, α, h, rfl⟩
  . intro h
    specialize h default
    rcases h with ⟨_, α, h, _⟩
    exact ⟨α, h⟩

omit [TopologicalSpace X] in
lemma splitting {n a Y Θ Φ} (hY : GKernel Y Θ Φ) (h : @Realized X n a Y Θ Φ) : ∃ b : Approximation (n + 1), Extension n a b ∧ Realized b Y Θ Φ := by
  have : (A a (s n) Y Θ Φ).Nonempty := by
    rcases h with ⟨α, h⟩
    exact ⟨α.φ (s n), α, h, rfl⟩
  replace hY := fun h => have := hY.prop n a (s n) h ▸ this; (by simp at this : False)
  simp [Independent] at hY
  rcases hY with ⟨_, ⟨α₀, hα₀, h₀⟩, _, ⟨α₁, hα₁, h₁⟩, hY⟩
  cases h₀
  cases h₁
  refine ⟨_, ?_, amalgamation Θ Φ α₀ α₁ hY, ?_⟩
  . constructor <;> simp
  . constructor
    simp [amalgamation]
    intro x hx
    simp at hx
    rcases hx with ⟨y, hy⟩
    cases hy
    split
    . exact hα₁.image ⟨fun i => y i.castSucc, rfl⟩
    . exact hα₀.image ⟨fun i => y i.castSucc, rfl⟩

def CountableBorelChromatic (Y : Set X) (G : X → X → Prop) : Prop :=
  ∃ A : Nat → Set X, (∀ n, @MeasurableSet _ (borel X) (A n) ∧ Independent G (A n)) ∧ Y = ⋃ n, A n

variable [T2Space X]

lemma HW Θ Φ : ∃ Y, @GKernel X Y Θ Φ ∧ CountableBorelChromatic Yᶜ fun x y => ∃ z, Θ z = (x, y) :=
  sorry

theorem 𝔾₀_dichotomy {G} [IsSymm X G] (G_analytic : MeasureTheory.AnalyticSet fun (x, y) => G x y) : CountableBorelChromatic .univ G ≠ ∃ φ : 𝔾₀ →r G, Continuous φ := by
  borelize X (Nat → Bool)
  simp
  simp only [iff_iff_and_or_not_and_not, not_or]
  constructor
  . simp [CountableBorelChromatic]
    intro A hA cover φ cont
    have : IsMeagre (⋃ n, φ ⁻¹' A n) := by
      apply isMeagre_iUnion
      intro n
      apply 𝔾₀_independent_meager
      . use φ ⁻¹' A n
        simp
        exact cont.measurable (hA n).left
      . intro x hx y hy h
        exact (hA n).right (φ x) hx (φ y) hy (φ.map_rel h)
    have cover' : (⋃ n, φ ⁻¹' A n) = .univ :=
      by ext x; have := congrArg (φ x ∈ ·) cover; simp at this ⊢; exact this
    rewrite [cover'] at this
    refine BaireSpace.iff_open_nonempty_nonmeager.mp inferInstance _ ?_ ?_ this <;> simp
  simp only [not_and_or]
  simp
  simp [MeasureTheory.AnalyticSet] at G_analytic
  cases G_analytic with
  | inl h =>
    replace h := congrFun h
    simp [-eq_iff_iff, EmptyCollection.emptyCollection] at h
    replace h := funext fun a => funext (h a)
    cases h
    left
    use fun n _ => n = 0
    simp
    constructor
    . intro n
      cases n with simp
      | zero => change MeasurableSet .univ ∧ _; simp [Independent]
      | succ => change MeasurableSet ∅ ∧ _; simp [Independent]
    . ext x
      simp
      exact ⟨0, rfl⟩
  | inr h =>
  rcases h with ⟨Θ, Θ_cont, Θ_range⟩
  let Φ (x : Nat → Nat) : X := if x 0 = 0 then (Θ fun i => x i.succ).fst else (Θ fun i => x i.succ).snd
  have Φ_cont : Continuous Φ := by
    constructor
    intro U U_open
    have open0 : IsOpen {x | ∃ h : x 0 = 0, Φ x ∈ U} := by
      simp +contextual [Φ, -exists_prop]
      suffices IsOpen (N ![0] ∩ Prod.fst ∘ Θ ∘ (fun x i => x i.succ) ⁻¹' U) by
        refine Eq.mp ?_ this
        congr
        ext
        simp [mem_N]
        exact ⟨.symm, .symm⟩
      apply N_open.inter
      apply U_open.preimage _
      apply continuous_fst.comp
      apply Θ_cont.comp
      apply Pi.continuous_precomp
    have open' : IsOpen {x | ∃ h : x 0 ≠ 0, Φ x ∈ U} := by
      simp +contextual [Φ, -exists_prop]
      suffices IsOpen ((N ![0])ᶜ ∩ Prod.snd ∘ Θ ∘ (fun x i => x i.succ) ⁻¹' U) by
        refine Eq.mp ?_ this
        congr
        ext
        simp [mem_N]
        exact ⟨.symm, .symm⟩
      apply IsOpen.inter N_closed.isOpen_compl
      apply U_open.preimage _
      apply continuous_snd.comp
      apply Θ_cont.comp
      apply Pi.continuous_precomp
    simp at open0 open'
    change IsOpen ({x : ℕ → ℕ | x 0 = 0} ∩ Φ ⁻¹' U) at open0
    change IsOpen ({x : ℕ → ℕ | x 0 = 0}ᶜ ∩ Φ ⁻¹' U) at open'
    have := open0.union open'
    simp [← Set.union_inter_distrib_right] at this
    exact this

  let ⟨Y, Y_kernel, hY⟩ := HW Θ Φ
  by_cases (Y ∩ .range Φ).Nonempty
  case neg h =>
    left
    rcases hY with ⟨A, hA, cover⟩
    use fun n => n.casesOn Y A
    constructor
    . intro n
      cases n with
      | zero =>
        simp
        constructor
        . refine .of_compl ?_
          rewrite [cover]
          refine .iUnion ?_
          intro n
          exact (hA n).left
        . intro x hx y hy h'
          let ⟨z, hz⟩ := (congrArg ((x, y) ∈ ·) Θ_range).mpr h'
          refine h ⟨x, hx, fun n => n.casesOn 0 z, ?_⟩
          simp [Φ, hz]
      | succ n =>
        simp
        constructor
        . exact (hA n).left
        . intro x hx y hy h
          exact (hA n).right x hx y hy ((congrArg ((x, y) ∈ ·) Θ_range).mpr h)
    . ext x
      simp
      by_cases x ∈ Y
      case pos hx => exact ⟨0, hx⟩
      case neg hx =>
        change x ∈ Yᶜ at hx
        rewrite [cover] at hx
        simp at hx
        rcases hx with ⟨n, hx⟩
        exact ⟨n + 1, hx⟩

  case pos Y_nonempty =>
  right
  rcases Y_nonempty with ⟨y, hy, cy, hcy⟩
  let a : ∀ n, { a : Approximation n // Realized a Y Θ Φ } :=
    Nat.rec ⟨⟨nofun, nofun⟩, ⟨⟨fun _ => cy, nofun, nofun, nofun, nofun⟩, ⟨by simp [hcy, hy]⟩⟩⟩ fun n a => have := splitting Y_kernel a.property; ⟨Classical.choose this, Classical.choose_spec this |>.right⟩
  have a_extension n : Extension n (a n).val (a (n + 1)).val :=
    (Classical.choose_spec (splitting Y_kernel (a n).property)).left
  let φ : (Nat → Bool) → (Nat → Nat) := treelim fun n => (a n).val.f
  let γ (k : Nat) (x : Nat → Bool) (n : Nat) : Nat :=
    (a (n.max k + 1)).val.g ⟨k, by apply Nat.lt_succ_of_le; simp⟩ (fun i => x i) ⟨n, by apply Nat.lt_succ_of_le; simp⟩
  have φ_cont : Continuous φ := treelim_cont _
  refine ⟨⟨Φ ∘ φ, ?_⟩, Φ_cont.comp φ_cont⟩
  intro foo bar ⟨k, b, z, h, h'⟩
  cases h
  cases h'
  suffices Θ (γ k z) = (Φ (φ (s k ++ (![false] ++ z))), Φ (φ (s k ++ (![true] ++ z)))) by
    replace Θ_range := fun x => congrArg (x ∈ ·) Θ_range
    simp at Θ_range
    have := Θ_range _ _ |>.mp ⟨_, this⟩
    cases b with
    | false => exact this
    | true => apply symm; exact this
  let graph : Set _ := {(x, y₀, y₁) | Θ x = (Φ y₀, Φ y₁)}
  have : IsClosed graph := isClosed_eq Θ_cont.fst' (continuous_prodMk.mpr ⟨Φ_cont.comp (continuous_fst.comp continuous_snd), Φ_cont.comp (continuous_snd.comp continuous_snd)⟩)
  show (_, _, _) ∈ graph
  rewrite [← closure_eq_iff_isClosed.mpr this, mem_closure_iff]
  intro U U_open U_mem
  have := N_basis.prod (N_basis.prod N_basis) |>.isOpen_iff.mp U_open _ U_mem
  simp at this
  rcases this with ⟨_, ⟨_, ⟨n₁, _, _⟩, _, ⟨n₂, _, _⟩, _, ⟨n₃, _, _⟩, _⟩, mem, subset⟩
  subst_eqs
  simp [mem_N] at mem
  rcases mem with ⟨mem₁, mem₂, mem₃⟩
  replace mem₁ := funext mem₁
  replace mem₂ := funext mem₂
  replace mem₃ := funext mem₃
  subst_eqs
  let n' := (k + 1).max (n₁.max (n₂.max n₃))
  replace subset := Set.prod_mono (N_agree (n₂ := n') (t₂ := fun i => γ k z i) (by simp [n']) fun _ => rfl) (Set.prod_mono (N_agree (n₂ := n') (t₂ := fun i => φ (s k ++ (![false] ++ z)) i) (by simp [n']) fun _ => rfl) (N_agree (n₂ := n') (t₂ := fun i => φ (s k ++ (![true] ++ z)) i) (by simp [n']) fun _ => rfl)) |>.trans subset
  have hn : k < n' := by simp [n']
  generalize n' = n at subset hn
  clear n' n₁ n₂ n₃
  let t (i : Fin (n - (k + 1))) : Bool := z i
  have : (a n).val.g ⟨k, hn⟩ t = fun i => γ k z i.val := by
    simp [γ]
    suffices ∀ i : Fin n, ∀ h j, (a n).val.g ⟨k, hn⟩ t (j.castLE i.isLt) = (a (i + 1)).val.g ⟨k, Nat.lt_succ_of_le h⟩ (fun i => z i) j from funext fun i => this ⟨i.val.max k, by simp; omega⟩ (by simp) ⟨i, Nat.lt_succ_of_le <| by simp⟩
    intro i h
    cases n
    nomatch i
    case succ n =>
    induction i using Fin.reverseInduction with
    | last => simp [t]
    | cast i ih =>
      simp
      intro j
      specialize ih h.step j.castSucc
      simp at ih
      rewrite [ih, (a_extension (i + 1)).g ⟨k, Nat.lt_succ_of_le h⟩ (fun i => z i) (z (i - k)) j]
      congr
      funext j
      generalize hj : j.cast _ = j'
      generalize_proofs _ hj' at hj
      replace hj : j = j'.cast hj'.symm := by simp [← hj]
      cases hj
      simp
      cases j' using Fin.lastCases with simp
  rewrite [← this] at subset
  have : (a n).val.f (append (s k) false t) = fun i => φ (s k ++ (![false] ++ z)) i.val := by
    funext i
    generalize h : s k ++ (![false] ++ z) = t'
    have : append (s k) false t = fun i => t' i.val := by
      funext i
      simp [append, ← h, HAppend.hAppend]
      split
      . rfl
      . split
        . simp [*]
        next h₁ h₂ =>
          have := Nat.lt_or_lt_of_ne h₂ |>.resolve_left h₁
          have : i.val - k ≠ 0 := by omega
          simp [*, t]
          rfl
    rewrite [this]
    clear this h
    simp [φ, treelim]
    suffices ∀ j, (a n).val.f (fun i => t' i) (j.castLE i.isLt) = (a (i + 1)).val.f (fun i => t' i) j from this (Fin.last i)
    cases n
    nomatch i
    case succ n =>
    induction i using Fin.reverseInduction with
    | last => simp
    | cast i ih =>
      simp
      intro j
      specialize ih j.castSucc
      simp at ih
      rewrite [ih, (a_extension (i + 1)).f (fun i => t' i) (t' (i + 1)) j]
      congr
      funext k
      cases k using Fin.lastCases with simp
  rewrite [← this] at subset
  have : (a n).val.f (append (s k) true t) = fun i => φ (s k ++ (![true] ++ z)) i.val := by
    funext i
    generalize h : s k ++ (![true] ++ z) = t'
    have : append (s k) true t = fun i => t' i.val := by
      funext i
      simp [append, ← h, HAppend.hAppend]
      split
      . rfl
      . split
        . simp [*]
        next h₁ h₂ =>
          have := Nat.lt_or_lt_of_ne h₂ |>.resolve_left h₁
          have : i.val - k ≠ 0 := by omega
          simp [*, t]
          rfl
    rewrite [this]
    clear this h
    simp [φ, treelim]
    suffices ∀ j, (a n).val.f (fun i => t' i) (j.castLE i.isLt) = (a (i + 1)).val.f (fun i => t' i) j from this (Fin.last i)
    cases n
    nomatch i
    case succ n =>
    induction i using Fin.reverseInduction with
    | last => simp
    | cast i ih =>
      simp
      intro j
      specialize ih j.castSucc
      simp at ih
      rewrite [ih, (a_extension (i + 1)).f (fun i => t' i) (t' (i + 1)) j]
      congr
      funext k
      cases k using Fin.lastCases with simp
  rewrite [← this] at subset
  let ⟨α, _⟩ := (a n).property
  exact ⟨(_, _, _), subset ⟨α.γ_g ⟨k, hn⟩ t, α.φ_f _, α.φ_f _⟩, α.edge ⟨k, hn⟩ t⟩
