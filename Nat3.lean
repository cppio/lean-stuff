import Common.Meta
import Mathlib.Logic.Equiv.Defs

structure Sig where
  Nat : Type
  «Nat.zero» : Nat
  «Nat.succ» : Nat → Nat
  «Nat.rec₀» {motive : Nat → Prop} : motive «Nat.zero» → (∀ n, motive n → motive («Nat.succ» n)) → ∀ n, motive n

structure Sig' (Imp : Sig) where
  «Nat.rec» {motive : Imp.Nat → Sort u} : motive Imp.«Nat.zero» → (∀ n, motive n → motive (Imp.«Nat.succ» n)) → ∀ n, motive n
  «Nat.rec_zero» {motive} zero succ : @«Nat.rec» motive zero succ Imp.«Nat.zero» = zero
  «Nat.rec_succ» {motive} zero succ n : @«Nat.rec» motive zero succ (Imp.«Nat.succ» n) = succ n (@«Nat.rec» motive zero succ n)

attribute [elab_as_elim] Sig.«Nat.rec₀» Sig'.«Nat.rec»
attribute [simp] Sig'.«Nat.rec_zero» Sig'.«Nat.rec_succ»

instance : Nonempty (Sig'.{u} Imp) :=
  have rec₀ {motive : Imp.Nat → Sort (max 1 u)} (zero : motive Imp.«Nat.zero») (succ : ∀ n, motive n → motive (Imp.«Nat.succ» n)) n : motive n :=
    Classical.choice <| Imp.«Nat.rec₀» ⟨zero⟩ (⟨succ · <| Classical.choice ·⟩) n
  have rec {motive : Imp.Nat → Sort u} (zero : motive Imp.«Nat.zero») (succ : ∀ n, motive n → motive (Imp.«Nat.succ» n)) :=
    @Sig.«Nat.rec₀» Imp
      (λ n => ∃ x : motive n, @rec₀ (λ m => motive m → Prop) (λ x => x = zero) (λ n ih x => ∃ y, x = succ n y ∧ ih y) n x)
      ⟨zero, by dsimp; sorry⟩
      λ n hn => ⟨succ n (Classical.choose hn), sorry⟩
  ⟨{
    «Nat.rec» := λ zero succ n => Classical.choose <| rec zero succ n
    «Nat.rec_zero» := λ zero succ => have := Classical.choose_spec <| rec zero succ Imp.«Nat.zero»; by dsimp only []; sorry
    «Nat.rec_succ» := λ zero succ n => have := Classical.choose_spec <| rec zero succ (Imp.«Nat.succ» n); by dsimp only []; sorry
  }⟩

def Impl : Sig where
  Nat := Nat
  «Nat.zero» := .zero
  «Nat.succ» := .succ
  «Nat.rec₀» := @Nat.rec

def Impl' : Sig' Impl where
  «Nat.rec» := @Nat.rec
  «Nat.rec_zero» _ _ := rfl
  «Nat.rec_succ» _ _ _ := rfl

opaque Imp₁ : Sig := Impl
opaque Imp₁' : Sig' Imp₁ := unsafe opaque_def% Imp₁ ▸ Impl'

opaque Imp₂ : Sig := Impl
opaque Imp₂' : Sig' Imp₂ := unsafe opaque_def% Imp₂ ▸ Impl'

structure Sig.Equiv (Imp₁ Imp₂ : Sig) where
  equiv : Imp₁.Nat ≃ Imp₂.Nat
  toFun_zero : equiv.toFun Imp₁.«Nat.zero» = Imp₂.«Nat.zero»
  invFun_zero : equiv.invFun Imp₂.«Nat.zero» = Imp₁.«Nat.zero»
  toFun_succ n : equiv.toFun (Imp₁.«Nat.succ» n) = Imp₂.«Nat.succ» (equiv.toFun n)
  invFun_succ n : equiv.invFun (Imp₂.«Nat.succ» n) = Imp₁.«Nat.succ» (equiv.invFun n)

structure Sig'.Equiv (Imp₁' : Sig' Imp₁) (Imp₂' : Sig' Imp₂) where
  equiv : Sig.Equiv Imp₁ Imp₂
  toFun_rec {motive} zero succ n : @Sig'.«Nat.rec» Imp₁ Imp₁' (motive <| equiv.equiv.toFun ·) (equiv.toFun_zero ▸ zero : motive _) (λ n ih => (equiv.toFun_succ n ▸ succ (equiv.equiv.toFun n) ih : motive _)) n = @Sig'.«Nat.rec» Imp₂ Imp₂' motive zero succ (equiv.equiv.toFun n)
  invFun_rec {motive} zero succ n : @Sig'.«Nat.rec» Imp₂ Imp₂' (motive <| equiv.equiv.invFun ·) (equiv.invFun_zero ▸ zero : motive _) (λ n ih => (equiv.invFun_succ n ▸ succ (equiv.equiv.invFun n) ih : motive _)) n = @Sig'.«Nat.rec» Imp₁ Imp₁' motive zero succ (equiv.equiv.invFun n)

theorem swap_eq_rec {β : α → _} {a a'} (h : a = a') {b : β a} {b' : β a'} : h ▸ b' = b → h ▸ b = b' :=
  by cases h; exact .symm

theorem rec_cast {n n' : Imp.Nat} (h : n = n') : h ▸ @Sig'.«Nat.rec» Imp Imp' motive zero succ n = @Sig'.«Nat.rec» Imp Imp' motive zero succ n' :=
  by cases h; rfl

theorem Imp₁'_Equiv_Imp₂' : Imp₁'.Equiv Imp₂' where
  equiv.equiv.toFun := Imp₁'.«Nat.rec» Imp₂.«Nat.zero» λ _ => Imp₂.«Nat.succ»
  equiv.equiv.invFun := Imp₂'.«Nat.rec» Imp₁.«Nat.zero» λ _ => Imp₁.«Nat.succ»
  equiv.equiv.left_inv := Imp₁'.«Nat.rec» (by simp) λ _ => by simp; apply congrArg
  equiv.equiv.right_inv := Imp₂'.«Nat.rec» (by simp) λ _ => by simp; apply congrArg
  equiv.toFun_zero := by simp
  equiv.invFun_zero := by simp
  equiv.toFun_succ := by simp
  equiv.invFun_succ := by simp
  toFun_rec {motive} zero succ n := by
    dsimp only []
    refine Imp₁'.«Nat.rec» ?_ (λ _ _ => ?_) n <;> clear n
      <;> simp <;> apply swap_eq_rec
      <;> (apply Eq.trans; apply rec_cast; simp)
    apply Eq.symm; congr
  invFun_rec {motive} zero succ n := by
    dsimp only []
    refine Imp₂'.«Nat.rec» ?_ (λ _ _ => ?_) n <;> clear n
      <;> simp <;> apply swap_eq_rec
      <;> (apply Eq.trans; apply rec_cast; simp)
    apply Eq.symm; congr
