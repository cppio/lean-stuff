import Parametric

class ParaF (τ : (Fin2 n → Type u) → Type u) :=
  prop : ∀ {α β}, (∀ i, α i → β i → Prop) → τ α → τ β → Prop

instance : ParaF λ α => α i where
  prop r := r i

instance : @ParaF n λ _ => α where
  prop _ := Eq

instance [ParaF τ] [ParaF τ'] : ParaF λ α => τ α → τ' α where
  prop r f f' := ∀ x x', ParaF.prop r x x' → ParaF.prop r (f x) (f' x')

class ParaT (α : Type u) :=
  prop : α → Prop

instance {τ : Type u → Type u} [I : @ParaF 1 λ α => τ (α 0)] : ParaT (∀ {α}, τ α) where
  prop f := ∀ {α β} (r : α → β → Prop), I.prop (λ _ => r) f f

instance {τ : Type u → Type u → Type u} [I : @ParaF 2 λ α => τ (α 0) (α 1)] : ParaT (∀ {α β}, τ α β) where
  prop f := ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop), @ParaF.prop _ _ I (λ | 0 => α | 1 => β) (λ | 0 => α' | 1 => β') (λ | 0 => r | 1 => s) f f

example : ParaT.prop (@f : ∀ {α β}, α → β → α) =
  ∀ {α α'} (r : α → α' → Prop),
    ∀ {β β'} (s : β → β' → Prop),
      ∀ x x', r x x' →
        ∀ y y', s y y' →
          r (f x y) (f x' y')
:= rfl

def Para (α) [I : ParaT α] := Subtype I.prop

instance [ParaT α] : CoeFun (Para α) λ _ => α where
  coe := Subtype.val

macro "parametric" : tactic => `(tactic| (destruct Para; repeat (first | intro _ | apply_assumption)))

def Para.mk [ParaT α] (x : α) (h : ParaT.prop x := by parametric) : Para α := ⟨x, h⟩

section Empty

example : ParaT.prop (@e : ∀ {α}, α) =
  ∀ {α β} (r : α → β → Prop),
    r e e
:= rfl

abbrev Empty' := Para (∀ {α}, α)

def Empty'.ofEmpty : Empty → Empty'
  := Empty.rec

example : Empty' ≃ Empty where
  toFun e := @e _
  invFun := .ofEmpty
  right_inv e := by
    induction e
  left_inv e := nomatch (@e Empty)

end Empty

section Unit

example : ParaT.prop (@u : ∀ {α}, α → α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ t t', r t t' →
      r (u t) (u t')
:= rfl

abbrev Unit' := Para (∀ {α}, α → α)

@[simp] def Unit'.unit : Unit' := .mk λ t => t

def Unit'.ofUnit : Unit → Unit'
  | .unit => unit

example : Unit' ≃ Unit where
  toFun u := u .unit
  invFun := .ofUnit
  right_inv u := by
    induction u
    case unit => rfl
  left_inv | ⟨_, h⟩ => by
    unfold Unit'.ofUnit
    dsimp
    congr
    funext _ t
    exact h (λ u x => Unit'.ofUnit u t = x) Unit.unit t rfl

end Unit

section Bool

example : ParaT.prop (@b : ∀ {α}, α → α → α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ f f', r f f' →
      ∀ t t', r t t' →
        r (b f t) (b f' t')
:= rfl

abbrev Bool' := Para (∀ {α}, α → α → α)

@[simp] def Bool'.false : Bool' := .mk λ f _ => f
@[simp] def Bool'.true  : Bool' := .mk λ _ t => t

def Bool'.ofBool : Bool → Bool'
  | .false => false
  | .true  => true

example : Bool' ≃ Bool where
  toFun b := b .false .true
  invFun := .ofBool
  right_inv b := by
    induction b
    case false => rfl
    case true => rfl
  left_inv | ⟨_, h⟩ => by
    unfold Bool'.ofBool
    dsimp
    split
      <;> rename_i h'
      <;> congr
      <;> funext _ f t
      <;> have := h' ▸ h (λ b x => Bool'.ofBool b f t = x) Bool.false f rfl Bool.true t rfl
      <;> exact this

end Bool

section Nat

example : ParaT.prop (@n : ∀ {α}, α → (α → α) → α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ z z', r z z' →
      ∀ s s', (∀ x x', r x x' → r (s x) (s' x')) →
        r (n z s) (n z' s')
:= rfl

abbrev Nat' := Para (∀ {α}, α → (α → α) → α)

@[simp] def Nat'.zero            : Nat' := .mk λ z _ => z
@[simp] def Nat'.succ (n : Nat') : Nat' := .mk λ z s => s (n z s)

def Nat'.ofNat : Nat → Nat'
  | .zero   => zero
  | .succ n => succ (ofNat n)

example : Nat' ≃ Nat where
  toFun n := n .zero .succ
  invFun := .ofNat
  right_inv n := by
    induction n
    case zero => rfl
    case succ ih => exact congrArg Nat.succ ih
  left_inv | ⟨_, h⟩ => by
    unfold Nat'.ofNat
    dsimp
    split
      <;> rename_i h'
      <;> congr
      <;> funext _ z s
      <;> have := h' ▸ h (λ n x => Nat'.ofNat n z s = x) Nat.zero z rfl Nat.succ s λ _ _ => congrArg s
      <;> exact this

end Nat
