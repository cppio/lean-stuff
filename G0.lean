import Mathlib

open MeasureTheory (AnalyticSet)

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

def N {n} (t : Fin n → α) : Set (Nat → α) :=
  {x | ∀ i, t i = x i}

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
  refine cast ?_ this
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

theorem MeasureTheory.AnalyticSet.inter [T2Space X] {A B : Set X} (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (A ∩ B) := by
  refine cast ?_ <| iInter (s := fun n => Nat.casesOn n A fun _ => B) fun n => n.casesOn hA fun _ => hB
  congr
  ext
  simp
  constructor
  . intro h
    exact ⟨h 0, h 1⟩
  . intro ⟨hA, hB⟩
    intro n
    cases n with simp [*]

def BorelSet (Y : Set X) : Prop :=
  @MeasurableSet X (borel X) Y

def Independent (G : X → X → Prop) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ¬G x y

omit [TopologicalSpace X] in
theorem Independent.anti {G} {A₁ A₂ : Set X} (hA : A₁ ⊆ A₂) (indep : Independent G A₂) : Independent G A₁ := by
  intro x hx y hy
  exact indep x (hA hx) y (hA hy)

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
  deriving Countable

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

def A {n} (a : Approximation n) (s : Fin n → Bool) (Y : Set X) (Θ : (Nat → Nat) → X × X) (Φ : (Nat → Nat) → X) : Set X :=
  {x | ∃ α : Realization n a Θ Φ, SetRealization Y α ∧ x = Φ (α.φ s)}

omit [TopologicalSpace X] in
theorem A_monotone {n} {a : Approximation n} {s Θ Φ} {Y₁ Y₂ : Set X} (hY : Y₁ ⊆ Y₂) : A a s Y₁ Θ Φ ⊆ A a s Y₂ Θ Φ := by
  intro _ ⟨α, hα, h⟩
  exact ⟨α, ⟨hα.image.trans hY⟩, h⟩

theorem A_analytic [T2Space X] {n a s' Y Θ Φ} (Y_borel : BorelSet Y) (Θ_cont : Continuous Θ) (Φ_cont : Continuous Φ) : AnalyticSet (@A X n a s' Y Θ Φ) := by
  suffices AnalyticSet (Φ '' {x | ∃ α : Realization n a Θ Φ, SetRealization Y α ∧ x = α.φ s'}) by
    refine cast ?_ this
    congr
    simp [A]
    ext
    simp
    constructor
    . intro ⟨_, ⟨α, hα, h'⟩, h⟩
      cases h
      cases h'
      use α
    . intro ⟨α, hα, h⟩
      cases h
      use α.φ s'
      simp
      use α
  apply AnalyticSet.image_of_continuous _ Φ_cont
  suffices AnalyticSet ({(φ, γ) : ((Fin n → Bool) → ℕ → ℕ) × (∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → ℕ → ℕ) | ∀ s, φ s ∈ N (a.f s)} ∩ {(φ, γ) | ∀ k t, γ k t ∈ N (a.g k t)} ∩ {(φ, γ) | ∀ k t, Θ (γ k t) = (Φ (φ (append (s k) false t)), Φ (φ (append (s k) true t)))} ∩ {(φ, γ) | Set.range (fun x => Φ (φ x)) ⊆ Y}) by
    replace := this.image_of_continuous (f := fun (φ, γ) => φ s') ?_
    . refine cast ?_ this
      congr
      ext x
      simp
      constructor
      . simp
        intro φ γ φ_f γ_g edge image h
        cases h
        exact ⟨⟨φ, γ, φ_f, γ_g, edge⟩, ⟨image⟩, rfl⟩
      . simp
        intro α hα h
        cases h
        use α.φ
        simp
        exact ⟨⟨α.γ, ⟨α.φ_f, α.γ_g⟩, α.edge⟩, hα.image⟩
    . simp
      apply Continuous.fst' (f := fun φ : _ → _ => φ s')
      apply continuous_apply
  apply AnalyticSet.inter
  apply AnalyticSet.inter
  apply AnalyticSet.inter
  . apply MeasurableSet.analyticSet
    apply IsOpen.measurableSet
    suffices IsOpen ({φ : (Fin n → Bool) → ℕ → ℕ | ∀ s, φ s ∈ N (a.f s)} ×ˢ @Set.univ (∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → ℕ → ℕ)) by
      simp [SProd.sprod, Set.prod] at this
      exact this
    simp [isOpen_prod_iff']
    left
    suffices IsOpen (⋂ s, {φ : (Fin n → Bool) → ℕ → ℕ | φ s ∈ N (a.f s)}) by
      refine cast ?_ this
      congr
      ext
      simp
    apply isOpen_iInter_of_finite
    intro s
    apply N_open.preimage
    apply continuous_apply
  . apply MeasurableSet.analyticSet
    apply IsOpen.measurableSet
    suffices IsOpen (@Set.univ ((Fin n → Bool) → ℕ → ℕ) ×ˢ {γ : ∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → ℕ → ℕ | ∀ k t, γ k t ∈ N (a.g k t)}) by
      simp [SProd.sprod, Set.prod] at this
      exact this
    simp [isOpen_prod_iff']
    left
    suffices IsOpen (⋂ k, ⋂ t, {γ : ∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → ℕ → ℕ | γ k t ∈ N (a.g k t)}) by
      refine cast ?_ this
      congr
      ext
      simp
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro t
    apply N_open.preimage
    revert t
    rewrite [← continuous_pi_iff]
    apply continuous_apply
  . apply IsClosed.analyticSet
    simp [← isOpen_compl_iff, HasCompl.compl]
    suffices IsOpen (⋃ k : Fin n, ⋃ t : Fin (n - (k + 1)) → Bool, {(φ, γ) : ((Fin n → Bool) → ℕ → ℕ) × (∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → ℕ → ℕ) | Θ (γ k t) ≠ (Φ (φ (append (s k) false t)), Φ (φ (append (s k) true t)))}) by
      refine cast ?_ this
      congr
      ext
      simp
    apply isOpen_iUnion
    intro k
    apply isOpen_iUnion
    intro t
    simp [← isClosed_compl_iff, HasCompl.compl]
    apply isClosed_eq
    . apply Θ_cont.comp
      apply Continuous.snd' (f := fun γ : ∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → ℕ → ℕ => γ k t)
      revert t
      rewrite [← continuous_pi_iff]
      apply continuous_apply
    . simp
      constructor
      . apply Φ_cont.comp
        apply Continuous.fst' (f := fun φ : _ → _ => φ (append (s k) false t))
        apply continuous_apply
      . apply Φ_cont.comp
        apply Continuous.fst' (f := fun φ : _ → _ => φ (append (s k) true t))
        apply continuous_apply
  . apply MeasurableSet.analyticSet
    suffices MeasurableSet ({φ : (Fin n → Bool) → ℕ → ℕ | Set.range (fun x => Φ (φ x)) ⊆ Y} ×ˢ @Set.univ (∀ k : Fin n, (Fin (n - (k + 1)) → Bool) → ℕ → ℕ)) by
      simp [SProd.sprod, Set.prod, -measurableSet_setOf] at this
      exact this
    simp [measurableSet_prod, -measurableSet_setOf]
    left
    suffices MeasurableSet (⋂ x : Fin n → Bool, {φ : (Fin n → Bool) → ℕ → ℕ | Φ (φ x) ∈ Y}) by
      refine cast ?_ this
      congr
      ext φ
      simp
      constructor
      . intro h _ ⟨x, h⟩
        cases h
        exact h x
      . intro h x
        exact h ⟨x, rfl⟩
    apply MeasurableSet.iInter
    intro x
    apply Y_borel.preimage
    borelize X
    apply Continuous.measurable
    apply Φ_cont.comp
    apply continuous_apply

structure GKernel (Y : Set X) (Θ Φ) where
  prop : ∀ n : Nat, ∀ a : Approximation n, ∀ s : Fin n → Bool, Independent (fun x y => ∃ z, Θ z = (x, y)) (A a s Y Θ Φ) → A a s Y Θ Φ = ∅

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
    exact ⟨Φ (α.φ s), α, h, rfl⟩
  . intro h
    specialize h default
    rcases h with ⟨_, α, h, _⟩
    exact ⟨α, h⟩

omit [TopologicalSpace X] in
lemma splitting {n a Y Θ Φ} (hY : GKernel Y Θ Φ) (h : @Realized X n a Y Θ Φ) : ∃ b : Approximation (n + 1), Extension n a b ∧ Realized b Y Θ Φ := by
  have : (A a (s n) Y Θ Φ).Nonempty := by
    rcases h with ⟨α, h⟩
    exact ⟨Φ (α.φ (s n)), α, h, rfl⟩
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
  ∃ A : Nat → Set X, (∀ n, BorelSet (A n) ∧ Independent G (A n)) ∧ Y = ⋃ n, A n

def CountableBorelChromatic.sing {G} {Y : Set X} (indep : Independent G Y) (borel : BorelSet Y) : CountableBorelChromatic Y G := by
  use fun _ => Y
  simp [*]
  ext
  simp

theorem CountableBorelChromatic.iUnion {G ι} [Countable ι] {Y : ι → Set X} (h : ∀ i, CountableBorelChromatic (Y i) G) : CountableBorelChromatic (⋃ i, Y i) G := by
  by_cases Nonempty ι
  case neg h =>
    simp at h
    simp
    use fun _ => ∅
    simp [BorelSet, Independent]
  case pos =>
  have ⟨f, hf⟩ := exists_surjective_nat ι
  generalize hh : (fun i => Classical.choose (h i)) = h₁
  have h₂ := fun i => Classical.choose_spec (h i)
  simp [congrFun hh] at h₂
  clear hh h
  use fun n => h₁ (f n.unpair.1) n.unpair.2
  simp
  constructor
  . intro n
    exact (h₂ (f n.unpair.1)).left n.unpair.2
  . ext x
    simp
    constructor
    . intro ⟨i, hx⟩
      specialize hf i
      rcases hf with ⟨a, hf⟩
      cases hf
      rewrite [(h₂ (f a)).right] at hx
      simp at hx
      rcases hx with ⟨b, hx⟩
      use a.pair b
      simp
      exact hx
    . intro ⟨n, hn⟩
      use f n.unpair.1
      rewrite [(h₂ (f n.unpair.1)).right]
      simp
      use n.unpair.2

theorem CountableBorelChromatic.union {G} {Y₁ Y₂ : Set X} (h₁ : CountableBorelChromatic Y₁ G) (h₂ : CountableBorelChromatic Y₂ G) : CountableBorelChromatic (Y₁ ∪ Y₂) G := by
  have := iUnion (Y := fun n => if n = 0 then Y₁ else Y₂) fun n => by dsimp; split; exact h₁; exact h₂
  refine cast ?_ this
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

variable [T2Space X]

lemma grow (G : X → X → Prop) (G_analytic : AnalyticSet {(x, y) | G x y}) {A} (A_analytic : AnalyticSet A) (indep : Independent G A) : ∃ B, BorelSet B ∧ A ⊆ B ∧ Independent G B := by
  borelize X
  let A' := {x | ∃ y ∈ A, G x y}
  have : AnalyticSet A' := by
    simp [AnalyticSet] at G_analytic A_analytic
    cases G_analytic with
    | inl h =>
      replace h := fun x => congrArg (x ∈ ·) h
      simp at h
      simp [A', h]
      exact MeasureTheory.analyticSet_empty
     | inr G_analytic =>
    cases A_analytic with
    | inl h =>
      replace h := fun x => congrArg (x ∈ ·) h
      simp [A', h]
      exact MeasureTheory.analyticSet_empty
     | inr A_analytic =>
    rcases G_analytic with ⟨G_f, hG⟩
    rcases A_analytic with ⟨A_f, hA⟩
    let P := (fun (x, y) => (G_f x |>.snd, A_f y)) ⁻¹' Set.diagonal X
    have : IsClosed P := by
      apply isClosed_diagonal.preimage
      simp
      exact ⟨hG.left.fst'.snd, hA.left.snd'⟩
    have : A' = Prod.fst ∘ G_f ∘ Prod.fst '' P := by
      ext x
      simp [A', P]
      constructor
      . intro ⟨y, hy, h⟩
        have := congrArg ((x, y) ∈ ·) hG.right
        simp [h] at this
        rcases this with ⟨z, hz⟩
        use z
        simp [hz]
        have := congrArg (y ∈ ·) hA.right
        simp [hy] at this
        rcases this with ⟨w, hw⟩
        exact ⟨w, hw.symm⟩
      . simp
        intro x y h h
        cases h
        use A_f y
        constructor
        . have : A_f y ∈ Set.range A_f := ⟨y, rfl⟩
          rewrite [hA.right] at this
          exact this
        . rewrite [← h]
          have : G_f x ∈ Set.range G_f := ⟨x, rfl⟩
          rewrite [hG.right] at this
          exact this
    rw [this]
    clear this
    apply this.analyticSet.image_of_continuous
    exact hG.left.fst.fst'
  replace := A_analytic.measurablySeparable this
  have disjoint : Disjoint A A' := by
    simp [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp [A']
    exact indep x
  specialize this disjoint
  rcases this with ⟨B, hB, hB₁, B_borel⟩
  let A'' := {y | ∃ x ∈ B, G x y}
  have : AnalyticSet A'' := by
    have : A'' = Prod.snd '' ({(x, y) | G x y} ∩ B ×ˢ .univ) := by
      ext x
      simp [A'']
      constructor
      . intro ⟨y, hy, h⟩
        exact ⟨y, h, hy⟩
      . intro ⟨y, h, hy⟩
        exact ⟨y, hy, h⟩
    rewrite [this]
    apply AnalyticSet.image_of_continuous _ continuous_snd
    simp [AnalyticSet] at G_analytic
    cases G_analytic with
    | inl h =>
      replace h := fun x => congrArg (x ∈ ·) h
      simp at h
      simp [A', h]
      exact MeasureTheory.analyticSet_empty
     | inr G_analytic =>
    rcases G_analytic with ⟨G_f, hG⟩
    simp [← hG.right]
    have : MeasurableSet (G_f ⁻¹' B ×ˢ .univ) := by
      borelize (X × X)
      apply hG.left.measurable
      have : B ×ˢ @Set.univ X = Prod.fst ⁻¹' B := by
        ext
        simp
      rewrite [this]
      exact continuous_fst.measurable B_borel
    replace := this.analyticSet.image_of_continuous hG.left
    refine cast ?_ this
    congr
    ext ⟨x, y⟩
    simp
    constructor
    . intro ⟨z, h₁, h₂⟩
      exact ⟨⟨z, h₂⟩, (h₂ ▸ h₁ :)⟩
    . intro ⟨⟨z, h₁⟩, h₂⟩
      exact ⟨z, h₁ ▸ h₂, h₁⟩ 
  replace := A_analytic.measurablySeparable this
  have disjoint : Disjoint A A'' := by
    simp [Set.disjoint_iff_inter_eq_empty]
    ext y
    simp [A'']
    intro hy x hx h
    exact hB₁.not_mem_of_mem_left ⟨y, hy, h⟩ hx
  specialize this disjoint
  rcases this with ⟨B', hB', hB'₁, B'_borel⟩
  use B ∩ B', B_borel.inter B'_borel, Set.subset_inter hB hB'
  intro x hx y hy h
  exact hB'₁.not_mem_of_mem_left ⟨x, Set.mem_of_mem_inter_left hx, h⟩ (Set.mem_of_mem_inter_right hy)

open Ordinal Cardinal in
lemma HW Θ Φ (Θ_cont : Continuous Θ) (Φ_cont : Continuous Φ) : ∃ Y, @GKernel X Y Θ Φ ∧ CountableBorelChromatic Yᶜ fun x y => ∃ z, Θ z = (x, y) := by
  borelize X
  let G x y := (x, y) ∈ Set.range Θ
  have G_analytic : AnalyticSet {(x, y) | G x y} := by
    simp [AnalyticSet]
    exact .inr ⟨Θ, Θ_cont, rfl⟩
  let prime (Y : Set X) (Y_borel : BorelSet Y) : Set X :=
    letI growth (n : Nat) (s : Fin n → Bool) (a : Approximation n) (indep : Independent G (A a s Y Θ Φ)) : Set X :=
      haveI : AnalyticSet (A a s Y Θ Φ) := A_analytic Y_borel Θ_cont Φ_cont
      Classical.choose (grow G G_analytic this indep)
    Y \ ⋃ n, ⋃ s, ⋃ a, ⋃ indep, growth n s a indep
  have prime_borel Y Y_borel : BorelSet (prime Y Y_borel) := by
    apply Y_borel.diff
    simp
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro s
    apply MeasurableSet.iUnion
    intro a
    apply MeasurableSet.iUnion
    intro indep
    generalize_proofs pf
    exact (Classical.choose_spec pf).left
  have prime_cbc Y Y_borel (hY : CountableBorelChromatic Yᶜ G) : CountableBorelChromatic (prime Y Y_borel)ᶜ G := by
    simp [prime, Set.compl_diff]
    apply CountableBorelChromatic.union _ hY
    apply CountableBorelChromatic.iUnion
    intro n
    apply CountableBorelChromatic.iUnion
    intro s
    apply CountableBorelChromatic.iUnion
    intro a
    apply CountableBorelChromatic.iUnion
    intro indep
    generalize_proofs pf
    have := Classical.choose_spec pf
    apply CountableBorelChromatic.sing this.right.right this.left
  have prime_subset Y Y_borel : prime Y Y_borel ⊆ Y := Set.diff_subset
  let Ys (o : Ordinal.{0}) (ho : o < ω₁) : { Y : Set X // BorelSet Y ∧ CountableBorelChromatic Yᶜ G } := by
    induction o using Ordinal.limitRecOn with
    | zero => exact ⟨.univ, MeasurableSet.univ, fun _ => ∅, by simp [BorelSet, Independent]⟩
    | succ o ih =>
      haveI := (ih ((Order.lt_succ o).trans ho)).property
      exact ⟨_, prime_borel _ this.left, prime_cbc _ this.left this.right⟩
    | isLimit o _ ih =>
      have : Countable (Set.Iio o) := by
        apply (countable_iff_lt_aleph_one (Set.Iio o)).mpr
        simp [Set.Iio, ← lift_card]
        have : ℵ₁ = Ordinal.card.{0} ω₁ := rfl
        rewrite [this, Ordinal.IsInitial.card_lt_card]
        . exact ho
        . apply isInitial_omega
      refine ⟨⋂ o' : Set.Iio o, ih o'.val o'.property (o'.property.trans ho), ?_, ?_⟩
      . apply MeasurableSet.iInter
        intro ⟨o', ho'⟩
        exact (ih o' ho' (ho'.trans ho)).property.left
      . rewrite [Set.compl_iInter]
        apply CountableBorelChromatic.iUnion
        intro ⟨o', ho'⟩
        exact (ih o' ho' (ho'.trans ho)).property.right
  have antitone {o₁ o₂ ho₁ ho₂} (ho : o₁ ≤ o₂) : (Ys o₂ ho₂).val ⊆ Ys o₁ ho₁ := by
    induction o₂ using Ordinal.limitRecOn with
    | zero => simp at ho; simp [ho]
    | succ o₂ ih =>
      by_cases o₁ ≤ o₂
      case neg ho' => simp [antisymm ho (Order.succ_le_of_lt (lt_of_not_ge ho'))]
      case pos ho =>
        refine .trans ?_ <| @ih ((Order.lt_succ o₂).trans ho₂) ho
        simp [Ys, prime_subset]
    | isLimit o₂ _ ih =>
      by_cases o₁ < o₂
      case neg ho' => simp [antisymm ho (le_of_not_gt ho')]
      case pos ho =>
        simp [Ys, -Set.iInter_coe_set, *]
        exact Set.iInter_subset _ (⟨o₁, ho⟩ : Set.Iio o₂)
  let indeps (Y : Set X) := {⟨n, s, a⟩ : Σ n, (Fin n → Bool) × Approximation n | Independent G (A a s Y Θ Φ)}
  have indeps_antitone {Y₁ Y₂ : Set X} (hY : Y₁ ⊆ Y₂) : indeps Y₂ ⊆ indeps Y₁ := by
    intro ⟨n, s, a⟩ h
    simp [indeps] at h ⊢
    exact h.anti (A_monotone hY)
  have indeps_countable Y : (indeps Y).Countable := Set.Countable.mono (Set.subset_univ _) Subtype.countable
  let indeps' o ho := indeps (Ys o ho)

  suffices ∃ o ho, indeps' o ho = indeps' (Order.succ o) (Ordinal.IsLimit.succ_lt (isLimit_omega 1) ho) by
    rcases this with ⟨o, ho, h⟩
    replace h := subset_of_eq h.symm
    replace h := fun n s a => @h ⟨n, s, a⟩
    simp [indeps', indeps] at h
    refine ⟨Ys (Order.succ o) (Ordinal.IsLimit.succ_lt (isLimit_omega 1) ho), ?_, (Ys _ _).property.right⟩
    constructor
    intro n a s indep
    change Independent G _ at indep
    specialize h n s a indep
    simp [Ys, -Set.iInter_coe_set]
    change A a s (prime _ (Ys _ _).property.left) Θ Φ = _
    simp [prime, ← Set.subset_empty_iff]
    trans
    . apply A_monotone
      apply Set.diff_subset_diff_right
      trans
      swap
      exact Set.subset_iUnion _ n
      trans
      swap
      exact Set.subset_iUnion _ s
      trans
      swap
      exact Set.subset_iUnion _ a
      exact Set.subset_iUnion _ h
    generalize_proofs pf
    have hB := Classical.choose_spec pf
    generalize Classical.choose pf = B at hB
    clear pf
    trans
    . apply A_monotone
      apply Set.diff_subset_diff_right
      exact hB.right.left
    clear hB B
    intro x hx
    simp [A] at hx ⊢
    rcases hx with ⟨α, hα, h⟩
    cases h
    have := fun x => @hα.image x
    simp at this
    exact (this s).right α ⟨hα.image.trans Set.diff_subset⟩ rfl

  have indeps'_monotone {o₁ o₂ ho₁ ho₂} (ho : o₁ ≤ o₂) : indeps' o₁ ho₁ ⊆ indeps' o₂ ho₂ := indeps_antitone (antitone ho)
  have indeps'_countable o ho : (indeps' o ho).Countable := indeps_countable (Ys o ho)

  let all := ⋃ o, ⋃ ho, indeps' o ho
  let appear n (s : Fin n → Bool) (a : Approximation n) : {o : Ordinal // o < ω₁} := by
    refine ⟨sInf {o | ∃ ho, ⟨n, s, a⟩ ∈ indeps' o ho}, ?_⟩
    by_cases {o | ∃ ho, ⟨n, s, a⟩ ∈ indeps' o ho}.Nonempty
    case pos h =>
      rcases h with ⟨x, hx⟩
      exact lt_of_le_of_lt (csInf_le' hx) hx.fst
    case neg h =>
      simp [Set.nonempty_iff_ne_empty] at h
      rewrite [h]
      simp
      apply omega_pos
  let indices := (fun ⟨n, s, a⟩ => appear n s a) '' all
  have : Countable indices := by
    apply Set.Countable.image
    exact Set.Countable.mono (Set.subset_univ _) Subtype.countable
  by_cases all.Nonempty
  case neg h =>
    simp [Set.nonempty_iff_ne_empty] at h
    have : ⋃ o, ⋃ ho, indeps' o ho = all := rfl
    rewrite [h] at this
    simp [← Set.subset_empty_iff] at this
    simp at this
    simp [this]
    exact ⟨0, omega_pos 1⟩
  case pos nonempty_all =>
  have : Nonempty indices := by
    rcases nonempty_all with ⟨⟨n, s, a⟩, h⟩
    simp
    exact ⟨_, (appear n s a).property, ⟨n, s, a⟩, h, rfl⟩
  have ⟨f, hf⟩ := exists_surjective_nat indices
  let O := lsub fun n => f n
  have hO : O < ω₁ := by
    apply Ordinal.lsub_lt_ord
    . simp [isRegular_aleph_one.cof_omega_eq]
      exact aleph0_lt_aleph_one
    intro n
    exact (f n).val.property
  have : all = ⋃ o ∈ indices, indeps' o.val o.property := by
    ext ⟨n, s, a⟩
    simp [all]
    constructor
    . intro ⟨o, ho, h⟩
      use appear n s a
      simp [indices, all]
      refine ⟨⟨n, s, a, ?_⟩, ?_⟩
      . simp
        exact ⟨o, ho, h⟩
      . have : (appear n s a).val ∈ {o | ∃ ho, ⟨n, s, a⟩ ∈ indeps' o ho} := csInf_mem ⟨o, ho, h⟩
        exact this
    . intro ⟨o, ho, _, h⟩
      exact ⟨o, ho, h⟩
  replace : all = indeps' O hO := by
    apply le_antisymm
    swap
    . simp [all]
      trans
      swap
      . exact Set.subset_iUnion _ O
      exact Set.subset_iUnion _ hO
    rewrite [this]
    simp
    intro o ho h
    apply indeps'_monotone
    apply le_of_lt
    specialize hf ⟨_, h⟩
    rcases hf with ⟨n, hn⟩
    replace hn : o = f n := by simp [hn]
    cases hn
    apply Ordinal.lt_lsub
  use O, hO
  apply le_antisymm
  . apply indeps'_monotone
    exact Order.le_succ O
  . rewrite [← this]
    simp [all]
    trans
    swap
    . exact Set.subset_iUnion _ (Order.succ O)
    exact Set.subset_iUnion _ (Ordinal.IsLimit.succ_lt (isLimit_omega 1) hO)

theorem 𝔾₀_dichotomy {G} [IsSymm X G] (G_analytic : AnalyticSet {(x, y) | G x y}) : CountableBorelChromatic .univ G ≠ ∃ φ : 𝔾₀ →r G, Continuous φ := by
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
  simp [AnalyticSet] at G_analytic
  cases G_analytic with
  | inl h =>
    replace h := congrFun h
    simp [-eq_iff_iff, EmptyCollection.emptyCollection, setOf] at h
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
        refine cast ?_ this
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
        refine cast ?_ this
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

  let ⟨Y, Y_kernel, hY⟩ := HW Θ Φ Θ_cont Φ_cont
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

example {Y G} (Y_meas : BorelSet Y) : CountableBorelChromatic Y G ↔ ∃ c : Y → Nat, @Measurable _ _ (@Subtype.instMeasurableSpace X Y (borel X)) _ c ∧ ∀ n, Independent G (Subtype.val '' (c ⁻¹' {n})) := by
  borelize X
  constructor
  . intro ⟨A, hA, hY⟩
    use fun x => sInf {n | x.val ∈ A n}
    constructor
    . intro U U_meas
      suffices MeasurableSet (⋃ n ∈ U, (fun x : Y => sInf {n | x.val ∈ A n}) ⁻¹' {n}) by
        simp at this  
        exact this
      apply MeasurableSet.sUnion (Set.countable_range _)
      simp
      intro n
      apply MeasurableSet.sUnion (Set.countable_range _)
      simp
      intro hn
      simp [Set.preimage, -measurableSet_setOf]
      suffices MeasurableSet (A n \ ⋃ i < n, A i) by
        apply MeasurableSet.of_subtype_image
        refine cast ?_ this
        congr
        ext x
        simp [hY]
        constructor
        . intro ⟨h, h'⟩
          refine ⟨?_, n, h⟩
          rewrite [Nat.sInf_def ⟨n, h⟩]
          simp [Nat.find_eq_iff, h]
          exact h'
        . intro ⟨h, h'⟩
          have := Nat.sInf_mem (s := {n | x ∈ A n}) h'
          rewrite [h] at this
          refine ⟨this, ?_⟩
          intro n' hn'
          exact Nat.not_mem_of_lt_sInf (h ▸ hn')
      apply (hA n).left.diff
      apply MeasurableSet.iUnion
      intro n
      apply MeasurableSet.iUnion
      intro hn
      exact (hA n).left
    . intro n x hx y hy h
      simp at hx hy
      refine (hA n).right x ?_ y ?_ h
      . have := congrArg (x ∈ ·) hY
        simp [hx.right] at this
        have := Nat.sInf_mem (s := {n | x ∈ A n}) this
        rewrite [hx.left] at this
        exact this
      . have := congrArg (y ∈ ·) hY
        simp [hy.right] at this
        have := Nat.sInf_mem (s := {n | y ∈ A n}) this
        rewrite [hy.left] at this
        exact this
  . intro ⟨c, c_Meas, c_Indep⟩
    use fun n => Subtype.val '' (c ⁻¹' {n})
    simp
    constructor
    . intro n
      constructor
      . apply Y_meas.subtype_image
        apply c_Meas
        simp
      . exact c_Indep n
    . ext x
      simp
      constructor
      . intro h
        exact ⟨c ⟨x, h⟩, h, rfl⟩
      . intro ⟨_, h, _⟩
        exact h
