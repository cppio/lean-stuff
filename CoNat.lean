def CoNat := { f : Nat → Bool // ∀ i, f i || !f i.succ }
--def CoNat := { f : Nat → Bool // ∀ i, f i.succ → f i }

def CoNat.ofNat (n : Nat) : CoNat :=
  ⟨(Nat.blt · n), λ _ => by simp [← Bool.not_eq_true]; exact if h : _ then .inl h else .inr (.step <| Nat.le_of_not_lt h)⟩

def CoNat.inf : CoNat :=
  ⟨λ _ => true, λ _ => rfl⟩

-- Based on "Infinite sets that satisfy the principle of omniscience in any variety of constructive mathematics" by Martín Escardó

theorem lemma32 {x : CoNat} (h : x.val n = false) : ∃ k, k ≤ n ∧ x = .ofNat k :=
  lemma32 n.zero_le λ _ hj => nomatch hj
where
  lemma32 {k} (hk : k ≤ n) (hx : ∀ i, i < k → x.val i) : ∃ k, k ≤ n ∧ x = .ofNat k := by
    generalize hm : n - k = m
    induction m generalizing k with
    | zero =>
      cases k.zero_add ▸ Nat.eq_add_of_sub_eq hk hm
      exact ⟨n, .refl, Subtype.eq <| funext λ i => .symm <| if hi : i < n then by simp [CoNat.ofNat, hi, hx] else by
        apply Eq.trans (b := false)
        . simp [CoNat.ofNat, ← Bool.not_eq_true, hi]
        . apply Eq.symm
          have := Nat.ge_of_not_lt hi
          clear hi
          induction this with
          | refl => exact h
          | step _ ih =>
            have := x.property ‹_›
            simp [ih] at this
            exact this
      ⟩
    | succ m ih =>
      cases hx' : x.val k with
      | false =>
        exact ⟨k, hk, Subtype.eq <| funext λ i => .symm <| if hi : i < k then by simp [CoNat.ofNat, hi, hx] else by
          apply Eq.trans (b := false)
          . simp [CoNat.ofNat, ← Bool.not_eq_true, hi]
          . apply Eq.symm
            have := Nat.ge_of_not_lt hi
            clear hi
            induction this with
            | refl => exact hx'
            | step _ ih =>
              have := x.property ‹_›
              simp [ih] at this
              exact this
        ⟩
      | true =>
        apply ih (k := k.succ)
        . apply Nat.lt_of_le_of_ne hk
          intro h
          cases h
          cases h.symm.trans hx'
        . intro i hi
          cases hi with
          | refl => exact hx'
          | step hi => apply hx; exact hi
        . apply Nat.sub_eq_of_eq_add
          exact Nat.eq_add_of_sub_eq hk hm |>.trans <| m.succ_add k

theorem lemma33 {x : CoNat} (hx : ∀ n, x ≠ .ofNat n) : x = .inf :=
  Subtype.eq <| funext λ i =>
    match h : x.val i with
    | true => rfl
    | false => have ⟨k, _, hk⟩ := lemma32 h; nomatch hx k hk

theorem lemma34 (x : CoNat) : ¬(x ≠ .inf ∧ ∀ n, x ≠ .ofNat n) :=
  λ h => h.left <| lemma33 h.right

theorem Nat.blt_irrefl : blt n n = false := by
  simp [← Bool.not_eq_true]

theorem Nat.blt_succ_self : blt n n.succ = true := by
  simp [Nat.lt_succ_self]

section

variable (p : CoNat → Bool)

def CoNat.find' : Nat → Bool
  | .zero => p (.ofNat .zero)
  | .succ i => find' i && p (.ofNat i.succ)

def CoNat.find : CoNat :=
  ⟨find' p, λ i => by dsimp [find']; cases find' .. <;> rfl⟩

theorem CoNat.find_ (p : CoNat → Bool) (h : p (find p)) : ∀ x, p x := by
  have h₁ : ∀ n, find p ≠ .ofNat n := by
    intro n hn
    rw [hn] at h
    have : find' p n = Nat.blt n n := congrFun (congrArg Subtype.val hn) n
    rw [Nat.blt_irrefl] at this
    cases n with
    | zero => cases h.symm.trans this
    | succ n =>
      dsimp only [find'] at this
      simp [← Bool.not_eq_true] at this
      apply this
      have := congrFun (congrArg Subtype.val hn) n
      simp [find, ofNat, Nat.blt_succ_self] at this
      exact this
      exact h
  have h₂ : find p = .inf := lemma33 h₁
  have h₃ : ∀ n, p (.ofNat n) := λ n =>
    have : find' p n := congrFun (congrArg Subtype.val h₂) n
    match n with
    | .zero => this
    | .succ n => by simp [find'] at this; exact this.right
  intro x
  cases hx : p x with
  | true => rfl
  | false =>
    apply False.elim
    apply lemma34 x ⟨_, _⟩
    . intro h
      cases h
      cases hx.symm.trans <| h₂ ▸ h
    . intro n h
      cases h
      cases hx.symm.trans <| h₃ n

def CoNat.forall : Bool :=
  p <| find p

end

instance [BEq α] : BEq (CoNat → α) where
  beq f g := CoNat.forall λ x => f x == g x

instance [BEq α] [LawfulBEq α] : LawfulBEq (CoNat → α) where
  eq_of_beq {f g} h := funext (LawfulBEq.eq_of_beq <| CoNat.find_ (λ x => f x == g x) h ·)
  rfl := LawfulBEq.rfl (α := α)

instance [BEq α] [LawfulBEq α] : DecidableEq α
  | a, b =>
    match h : a == b with
    | true => isTrue <| eq_of_beq h
    | false => isFalse (nomatch show _ = true from h.symm.trans <| · ▸ LawfulBEq.rfl)
