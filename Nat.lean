import Common.Meta
import Mathlib.Logic.Equiv.Defs

private structure Sig where
  Nat : Type
  «Nat.zero» : Nat
  «Nat.succ» : Nat → Nat
  «Nat.rec₀» {motive : Nat → Prop} : motive «Nat.zero» → (∀ n, motive n → motive («Nat.succ» n)) → ∀ n, motive n

private structure Sig' (Imp : Sig) where
  «Nat.rec» {motive : Imp.Nat → Sort u} : motive Imp.«Nat.zero» → (∀ n, motive n → motive (Imp.«Nat.succ» n)) → ∀ n, motive n
  «Nat.rec_zero» {motive} zero succ : @«Nat.rec» motive zero succ Imp.«Nat.zero» = zero
  «Nat.rec_succ» {motive} zero succ n : @«Nat.rec» motive zero succ (Imp.«Nat.succ» n) = succ n (@«Nat.rec» motive zero succ n)

/-
instance : Nonempty (Sig' Imp) := ⟨{
  «Nat.rec» := λ {motive} zero succ n => Classical.choice <| @Sig.«Nat.rec₀» Imp (Nonempty <| motive ·) ⟨zero⟩ (⟨succ · <| Classical.choice ·⟩) n
}⟩
-/

instance : Nonempty (Sig' Imp) :=
  let rec' {motive : _ → _} (zero : motive _) (succ : ∀ n, motive n → motive _) := 
    @Sig.«Nat.rec₀» Imp (λ n => ∃ x, (∀ (h : n = Imp.«Nat.zero»), h ▸ x = zero) ∧ (∀ n' (h : n = Imp.«Nat.succ» n'), h ▸ x = succ n' sorry)) ⟨zero, λ _ => rfl, sorry⟩ (λ n ih => ⟨succ n (Classical.choose ih), sorry, sorry⟩)
  ⟨{
    «Nat.rec» := λ zero succ n => Classical.choose (rec' zero succ n)
    «Nat.rec_zero» := λ zero succ => Classical.choose_spec (rec' zero succ Imp.«Nat.zero») |>.left rfl
    «Nat.rec_succ» := λ zero succ n => by dsimp only []; show Classical.choose (rec' zero succ (Imp.«Nat.succ» n)) = succ n (Classical.choose (rec' zero succ n)); have := Classical.choose_spec (rec' zero succ (Imp.«Nat.succ» n)) |>.right n rfl; dsimp only [] at this; apply this.trans; clear this; sorry
  }⟩

private def Impl : Sig where
  Nat := Nat
  «Nat.zero» := .zero
  «Nat.succ» := .succ
  «Nat.rec₀» := @Nat.rec

private def Impl' : Sig' Impl where
  «Nat.rec» := @Nat.rec
  «Nat.rec_zero» _ _ := rfl
  «Nat.rec_succ» _ _ _ := rfl

private opaque Imp₁ : Sig := Impl
private opaque Imp₁' : Sig' Imp₁ := unsafe opaque_def% Imp₁ ▸ Impl'
def Nat₁ : Type := Imp₁.Nat
def Nat₁.zero : Nat₁ := Imp₁.«Nat.zero»
def Nat₁.succ : Nat₁ → Nat₁ := Imp₁.«Nat.succ»
def Nat₁.rec {motive : Nat₁ → Sort u} : motive .zero → (∀ n, motive n → motive n.succ) → ∀ n, motive n := Imp₁'.«Nat.rec»
@[simp] theorem Nat₁.rec_zero : ∀ zero succ, @Nat₁.rec motive zero succ .zero = zero := Imp₁'.«Nat.rec_zero»
@[simp] theorem Nat₁.rec_succ : ∀ zero succ n, @Nat₁.rec motive zero succ (.succ n) = succ n (@Nat₁.rec motive zero succ n) := Imp₁'.«Nat.rec_succ»

private opaque Imp₂ : Sig := Impl
private opaque Imp₂' : Sig' Imp₂ := unsafe opaque_def% Imp₂ ▸ Impl'
def Nat₂ : Type := Imp₂.Nat
def Nat₂.zero : Nat₂ := Imp₂.«Nat.zero»
def Nat₂.succ : Nat₂ → Nat₂ := Imp₂.«Nat.succ»
def Nat₂.rec {motive : Nat₂ → Sort u} : motive .zero → (∀ n, motive n → motive n.succ) → ∀ n, motive n := Imp₂'.«Nat.rec»
@[simp] theorem Nat₂.rec_zero : ∀ zero succ, @Nat₂.rec motive zero succ .zero = zero := Imp₂'.«Nat.rec_zero»
@[simp] theorem Nat₂.rec_succ : ∀ zero succ n, @Nat₂.rec motive zero succ (.succ n) = succ n (@Nat₂.rec motive zero succ n) := Imp₂'.«Nat.rec_succ»

example : Nat₁ ≃ Nat₂ where
  toFun := Nat₁.rec .zero λ _ => .succ
  invFun := Nat₂.rec .zero λ _ => .succ
  left_inv := Nat₁.rec (by simp) λ _ hn => by simp [hn]
  right_inv := Nat₂.rec (by simp) λ _ hn => by simp [hn]
