import Common.Meta
import Mathlib.Logic.Equiv.Defs

private structure Sig where
  Nat : Type
  «Nat.zero» : Nat
  «Nat.succ» : Nat → Nat
  «Nat.rec₀» {motive : Nat → Prop} : motive «Nat.zero» → (∀ n, motive n → motive («Nat.succ» n)) → ∀ n, motive n
  «Nat.rec₀_zero» {motive} zero succ : @«Nat.rec₀» motive zero succ «Nat.zero» = zero
  «Nat.rec₀_succ» {motive} zero succ n : @«Nat.rec₀» motive zero succ («Nat.succ» n) = succ n (@«Nat.rec₀» motive zero succ n)
  «Nat.rec₁» {motive : Nat → Type} : motive «Nat.zero» → (∀ n, motive n → motive («Nat.succ» n)) → ∀ n, motive n
  «Nat.rec₁_zero» {motive} zero succ : @«Nat.rec₁» motive zero succ «Nat.zero» = zero
  «Nat.rec₁_succ» {motive} zero succ n : @«Nat.rec₁» motive zero succ («Nat.succ» n) = succ n (@«Nat.rec₁» motive zero succ n)
  «Nat.rec₂» {motive : Nat → Type 1} : motive «Nat.zero» → (∀ n, motive n → motive («Nat.succ» n)) → ∀ n, motive n
  «Nat.rec₂_zero» {motive} zero succ : @«Nat.rec₂» motive zero succ «Nat.zero» = zero
  «Nat.rec₂_succ» {motive} zero succ n : @«Nat.rec₂» motive zero succ («Nat.succ» n) = succ n (@«Nat.rec₂» motive zero succ n)
  «Nat.zero_ne_succ» n : «Nat.zero» ≠ «Nat.succ» n
  «Nat.succ_inj» {n m} : «Nat.succ» n = «Nat.succ» m → n = m
  «Nat.ne_succ_self» {n} : n ≠ «Nat.succ» n

private structure Sig' (Imp : Sig) where
  «Nat.rec» {motive : Imp.Nat → Sort u} : motive Imp.«Nat.zero» → (∀ n, motive n → motive (Imp.«Nat.succ» n)) → ∀ n, motive n
  «Nat.rec_zero» {motive} zero succ : @«Nat.rec» motive zero succ Imp.«Nat.zero» = zero
  «Nat.rec_succ» {motive} zero succ n : @«Nat.rec» motive zero succ (Imp.«Nat.succ» n) = succ n (@«Nat.rec» motive zero succ n)

attribute [elab_as_elim] Sig.«Nat.rec₀» Sig.«Nat.rec₁» Sig.«Nat.rec₂»
attribute [simp] Sig.«Nat.rec₀_zero» Sig.«Nat.rec₀_succ» Sig.«Nat.rec₁_zero» Sig.«Nat.rec₁_succ» Sig.«Nat.rec₂_zero» Sig.«Nat.rec₂_succ»

instance : Nonempty (Sig'.{u} Imp) :=
  let lt (n : Imp.«Nat») : Imp.«Nat» → Type := Imp.«Nat.rec₂» Empty λ m ih => n = m ⊕' ih
  let le (n m : Imp.«Nat») : Type := n = m ⊕' lt n m
  have not_lt_self {n} : lt n n → False := Imp.«Nat.rec₀» (by simp) (λ n ih h => by simp at h; cases h with | inl h => sorry | inr h => (conv at h => change lt (Imp.«Nat.succ» n) n); sorry) n
  have subsingleton_lt {n m} (h₁ h₂ : lt n m) : h₁ = h₂ :=
    @Sig.«Nat.rec₀» Imp
      (λ m => (h₁ h₂ : lt n m) → h₁ = h₂)
      (λ h₁ h₂ => by simp at h₁; cases h₁)
      (λ m ih h₁ h₂ => by
        rename_i M H₁ H₂; clear M H₁ H₂
        dsimp at h₁ h₂ ih
        have : _ = h₁ := cast_cast (by simp; rfl) (by simp) h₁; rw [← this]; clear this
        generalize (cast _ h₁) = h₁'; clear h₁; rename _ => h₁
        have : _ = h₂ := cast_cast (by simp; rfl) (by simp) h₂; rw [← this]; clear this
        generalize (cast _ h₂) = h₂'; clear h₂; rename _ => h₂
        congr
        cases h₁ with
        | inl h₁ =>
          cases h₂ with
          | inl h₂ => rfl
          | inr h₂ => cases h₁; cases not_lt_self h₂
        | inr h₁ =>
          cases h₂ with
          | inl h₂ => cases h₂; cases not_lt_self h₁
          | inr h₂ => congr; apply ih
      ) m h₁ h₂
  have subsingleton_le {n m} (h₁ h₂ : le n m) : h₁ = h₂ := by
    cases h₁ with
    | inl h₁ =>
      cases h₂ with
      | inl h₂ => rfl
      | inr h₂ => cases h₁; cases not_lt_self h₂
    | inr h₁ =>
      cases h₂ with
      | inl h₂ => cases h₂; cases not_lt_self h₁
      | inr h₂ => congr; apply subsingleton_lt
  have lt_of_succ_le {n m} : le (Imp.«Nat.succ» n) m → lt n m := λ h => sorry
  have lt_succ_of_le {n m} : le n m → lt n (Imp.«Nat.succ» m) := λ h => sorry
  have not_lt_zero {n} : lt n Imp.«Nat.zero» → False := λ h => by simp [Sig.«Nat.rec₂_zero»] at h; cases h
  have le_of_lt_succ {n m} : lt n (Imp.«Nat.succ» m) → le n m := λ h => sorry
  have le_succ_of_lt {n m} : lt n m → le (Imp.«Nat.succ» n) m := λ h => sorry
  have zero_le {n} : le Imp.«Nat.zero» n := sorry
  have lt_succ_self {n} : lt n (Imp.«Nat.succ» n) := sorry
  have rec' {motive : Imp.«Nat» → Sort u} (zero : motive Imp.«Nat.zero») (succ : ∀ n, motive n → motive (Imp.«Nat.succ» n)) :=
    @Sig.«Nat.rec₀» Imp
      (λ n => ∃ (f : ∀ m, le m n → motive m), f Imp.«Nat.zero» zero_le = zero ∧ ∀ m h, f (Imp.«Nat.succ» m) (le_succ_of_lt h) = succ m (f m (PSum.inr h)))
      ⟨λ m h => h.casesOn (· ▸ zero) (nomatch not_lt_zero ·), by dsimp; apply Eq.trans; apply congrArg; apply subsingleton_le; exact PSum.inl rfl; rfl, λ _ h => not_lt_zero h |>.elim⟩
      λ n ih => ⟨λ m h => h.casesOn (· ▸ succ n (Classical.choose ih n (PSum.inl rfl))) (Classical.choose ih m <| le_of_lt_succ ·),
        by dsimp; apply Eq.trans; apply congrArg; apply subsingleton_le; apply PSum.inr; apply lt_succ_of_le; apply zero_le
           dsimp; apply Eq.trans; apply congrArg; apply subsingleton_le; apply zero_le
           exact Classical.choose_spec ih |>.left,
        by intro m h
           dsimp
           cases le_of_lt_succ h with
           | inl h =>
             cases h
             apply Eq.trans
             . apply congrArg; apply subsingleton_le; apply PSum.inl; rfl
             . apply congrArg (succ n <| Classical.choose ih n ·); apply subsingleton_le
           | inr h =>
             have h' : lt (Sig.«Nat.succ» Imp m) (Sig.«Nat.succ» Imp n) := lt_succ_of_le <| le_succ_of_lt h
             apply Eq.trans; apply congrArg; apply subsingleton_le; exact PSum.inr h'
             dsimp
             have := Classical.choose_spec ih |>.right m h
             apply Eq.trans (Eq.trans _ this) _
             . apply congrArg; apply subsingleton_le
             . apply congrArg (succ m <| Classical.choose ih m ·); apply subsingleton_le
        ⟩
  ⟨{
    «Nat.rec» := λ zero succ n => Classical.choose (rec' zero succ n) n (PSum.inl rfl)
    «Nat.rec_zero» := λ zero succ => by
      apply Eq.trans _ <| Classical.choose_spec (rec' zero succ Imp.«Nat.zero») |>.left
      apply congrArg
      apply subsingleton_le
    «Nat.rec_succ» := λ zero succ n => by
      have := Classical.choose_spec (rec' zero succ (Imp.«Nat.succ» n)) |>.right n lt_succ_self
      simp
      apply Eq.trans (Eq.trans _ this) _
      . apply congrArg; apply subsingleton_le
      . apply congrArg
        clear this
        induction n using Sig.«Nat.rec₀»
        next =>
          have := Classical.choose_spec (rec' zero succ (Imp.«Nat.succ» Imp.«Nat.zero»)) |>.left
          apply Eq.trans (Eq.trans _ this) _
          . apply congrArg; apply subsingleton_le
          . have := Classical.choose_spec (rec' zero succ Imp.«Nat.zero») |>.left
            apply Eq.symm
            apply Eq.trans _ this
            apply congrArg; apply subsingleton_le
        next n ih =>
          have := Classical.choose_spec (rec' zero succ (Imp.«Nat.succ» (Imp.«Nat.succ» n))) |>.right n sorry
          apply Eq.trans (Eq.trans _ this) _
          . apply congrArg; apply subsingleton_le
          . clear this
            have := Classical.choose_spec (rec' zero succ (Imp.«Nat.succ» (Imp.«Nat.succ» n))) |>.right n sorry
            sorry
  }⟩

private def Impl : Sig where
  Nat := Nat
  «Nat.zero» := .zero
  «Nat.succ» := .succ
  «Nat.rec₀» := @Nat.rec
  «Nat.rec₀_zero» _ _ := rfl
  «Nat.rec₀_succ» _ _ _ := rfl
  «Nat.rec₁» := @Nat.rec
  «Nat.rec₁_zero» _ _ := rfl
  «Nat.rec₁_succ» _ _ _ := rfl
  «Nat.rec₂» := @Nat.rec
  «Nat.rec₂_zero» _ _ := rfl
  «Nat.rec₂_succ» _ _ _ := rfl
  «Nat.zero_ne_succ» _ := (nomatch ·)
  «Nat.succ_inj» := Nat.succ.inj
  «Nat.ne_succ_self» := (nomatch ·)

private def Impl' : Sig' Impl where
  «Nat.rec» := @Nat.rec
  «Nat.rec_zero» _ _ := rfl
  «Nat.rec_succ» _ _ _ := rfl

private opaque Imp : Sig := Impl
private opaque Imp' : Sig' Imp := unsafe opaque_def% Imp ▸ Impl'
def Nat' : Type := Imp.Nat
def Nat'.zero : Nat' := Imp.«Nat.zero»
def Nat'.succ : Nat' → Nat' := Imp.«Nat.succ»
@[elab_as_elim] def Nat'.rec {motive : Nat' → Sort u} : (zero : motive .zero) → (succ : ∀ n, motive n → motive n.succ) → ∀ n, motive n := Imp'.«Nat.rec»
@[simp] theorem Nat'.rec_zero : ∀ zero succ, @Nat'.rec motive zero succ .zero = zero := Imp'.«Nat.rec_zero»
@[simp] theorem Nat'.rec_succ : ∀ zero succ n, @Nat'.rec motive zero succ (.succ n) = succ n (@Nat'.rec motive zero succ n) := Imp'.«Nat.rec_succ»
