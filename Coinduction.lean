import Lean

namespace Coinduction

set_option autoImplicit false

/-
codata Stream (α : Type u) : Type u where
  hd : α
  tl : Stream α
-/

inductive Stream.Approx.{u} (α : Type u) : (ℓ : Nat) → Type u
  | «⋯» : Approx α .zero
  | mk {ℓ} (hd : α) (tl : Approx α ℓ) : Approx α ℓ.succ

inductive Stream.Approx.Agree.{u} {α : Type u} : ∀ {ℓ₁ ℓ₂}, (x₁ : Approx α ℓ₁) → (x₂ : Approx α ℓ₂) → Prop
  | «⋯» {ℓ₂} {x₂ : Approx α ℓ₂} : Agree .«⋯» x₂
  | mk {ℓ₁ ℓ₂} {hd : α} {tl₁ : Approx α ℓ₁} {tl₂ : Approx α ℓ₂} (tl : Agree tl₁ tl₂) : Agree (.mk hd tl₁) (.mk hd tl₂)

def Stream.{u} (α : Type u) : Type u :=
  { f : (ℓ : Nat) → Stream.Approx α ℓ // ∀ ℓ, (f ℓ).Agree (f ℓ.succ) }

def Stream.hd.{u} {α : Type u} (self : Stream α) : α :=
  let .mk hd _ := self.val (.succ .zero); hd

def Stream.tl.{u} {α : Type u} (self : Stream α) : Stream α where
  val ℓ := let .mk _ tl := self.val ℓ.succ; tl
  property ℓ := by
    have := self.property ℓ.succ
    dsimp only
    generalize self.val ℓ.succ = x₁ at this
    generalize self.val ℓ.succ.succ = x₂ at this
    cases x₁ with | mk tl₁ =>
    cases x₂ with | mk tl₂ =>
    cases this with | mk tl =>
    exact tl

def Stream.corec.{s, u} {σ : Sort s} {α : Type u} (hd : (s : σ) → α) (tl : (s : σ) → σ) (s : σ) : Stream α where
  val ℓ := @Nat.rec (fun ℓ => (s : σ) → Approx α ℓ) (fun _ => .«⋯») (fun _ f s => .mk (hd s) (f (tl s))) ℓ s
  property ℓ := Nat.rec (fun _ => .«⋯») (fun _ h s => .mk (h (tl s))) ℓ s

theorem Stream.hd_corec.{s, u} {σ : Sort s} {α : Type u} (hd : (s : σ) → α) (tl : (s : σ) → σ) (s : σ) : Stream.hd (corec hd tl s) = hd s := rfl
theorem Stream.tl_corec.{s, u} {σ : Sort s} {α : Type u} (hd : (s : σ) → α) (tl : (s : σ) → σ) (s : σ) : Stream.tl (corec hd tl s) = corec hd tl (tl s) := rfl

def rep.{u} {α : Type u} (x : α) : Stream α :=
  .corec (fun _ => x) (·) ()

def even.{u} {α : Type u} (xs : Stream α) : Stream α :=
  .corec (fun xs => xs.hd) (fun xs => xs.tl.tl) xs

def odd.{u} {α : Type u} (xs : Stream α) : Stream α :=
  even xs.tl

def merge.{u} {α : Type u} (xs ys : Stream α) : Stream α :=
  .corec (fun (xs, _) => xs.hd) (fun (xs, ys) => (ys, xs.tl)) (xs, ys)

/-
codata Stream.Eq.{u} {α : Type u} (xs ys : Stream α) : Type u where
  hd : xs.hd = ys.hd
  tl : Eq xs.tl ys.tl
-/

inductive Stream.Eq.Approx.{u} {α : Type u} : (xs ys : Stream α) → (ℓ : Nat) → Prop where
  | «⋯» {xs ys} : Approx xs ys .zero
  | mk {ℓ xs ys} (hd : xs.hd = ys.hd) (tl : Approx xs.tl ys.tl ℓ) : Approx xs ys ℓ.succ

/-
inductive Stream.Eq.Approx.Agree.{u} {α : Type u} : {xs ys : Stream α} → ∀ {ℓ₁ ℓ₂}, (x₁ : Approx xs ys ℓ₁) → (x₂ : Approx xs ys ℓ₂) → Prop
  | «⋯» {ℓ₂ xs ys} (x₂ : Approx xs ys ℓ₂) : Agree .«⋯» x₂
  | mk {ℓ₁ ℓ₂} {xs ys : Stream α} {hd : xs.hd = ys.hd} {tl₁ : Approx xs.tl ys.tl ℓ₁} {tl₂ : Approx xs.tl ys.tl ℓ₂} (tl : Agree tl₁ tl₂) : Agree (.mk hd tl₁) (.mk hd tl₂)
-/

def Stream.Eq.{u} {α : Type u} (xs ys : Stream α) : Prop :=
  (ℓ : Nat) → Eq.Approx xs ys ℓ

def Stream.Eq.hd.{u} {α : Type u} {xs ys : Stream α} (self : Eq xs ys) : xs.hd = ys.hd :=
  let .mk hd _ := self (.succ .zero); hd

def Stream.Eq.tl.{u} {α : Type u} {xs ys : Stream α} (self : Eq xs ys) : Eq xs.tl ys.tl
  | ℓ => let .mk _ tl := self ℓ.succ; tl

def Stream.Eq.corec.{s, u} {α : Type u} {σ : (xs ys : Stream α) → Sort s} (hd : ∀ {xs ys}, (s : σ xs ys) → xs.hd = ys.hd) (tl : ∀ {xs ys}, (s : σ xs ys) → σ xs.tl ys.tl) {xs ys : Stream α} (s : σ xs ys) : Eq xs ys
  | ℓ => @Nat.rec (fun ℓ => ∀ {xs ys}, (s : σ xs ys) → Approx xs ys ℓ) (fun _ => .«⋯») (fun _ f _ _ s => .mk (hd s) (f (tl s))) ℓ xs ys s

theorem merge_even_odd.{u} {α : Type u} (xs : Stream α) : Stream.Eq xs (merge (even xs) (odd xs)) :=
  .corec (σ := fun xs ys => merge (even xs) (odd xs) = ys) (fun | .refl _ => rfl) (fun | .refl _ => rfl) rfl

/-
mutual

inductive SP.{u, v} (α : Type u) (β : Type v) : Type (max u v)
  | get (f : α → SP α β)
  | put (b : β) (sp : SP' α β)

codata SP'.{u, v} (α : Type u) (β : Type v) : Type (max u v) where
  force : SP α β

end
-/
