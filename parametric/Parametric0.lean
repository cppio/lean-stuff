import Parametric

class ParaF (ϕ : Type u → Type u) :=
  prop : ∀ {α β}, (α → β → Prop) → ϕ α → ϕ β → Prop

attribute [simp] ParaF.prop

instance : ParaF λ α => α where
  prop r := r

instance : ParaF λ _ => α where
  prop _ := Eq

instance [ParaF ϕ] [ParaF φ] : ParaF λ α => ϕ α → φ α where
  prop r f g := ∀ x y, ParaF.prop r x y → ParaF.prop r (f x) (g y)

class ParaT (α : Type u) :=
  prop : α → Prop

attribute [simp] ParaT.prop

instance [ParaF ϕ] : ParaT (∀ {α}, ϕ α) where
  prop f := ∀ {α β} (r : α → β → Prop), ParaF.prop r f f

def Para (α) [I : ParaT α] := Subtype I.prop

instance [ParaT α] : CoeFun (Para α) λ _ => α where
  coe := Subtype.val

macro_rules | `(tactic| para_step) => `(tactic| destruct Para)

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

section List

inductive lift (r : α → β → Prop) : List α → List β → Prop
  | nil  : lift r [] []
  | cons : r x y → lift r xs ys → lift r (x :: xs) (y :: ys)

theorem lift_map (g : α → β) : ∀ l, lift (λ x y => g x = y) l (l.map g)
  | [] => .nil
  | _::l => .cons rfl (lift_map g l)

theorem lift_to_map {g : α → β} : lift (λ x y => g x = y) xs ys → xs.map g = ys
  | .nil => rfl
  | .cons h h' => congrArg₂ _ h (lift_to_map h')

theorem lift_concat : lift r (x::xs) (y::ys) → lift r (xs.concat x) (ys.concat y)
  | .cons h .nil => .cons h .nil
  | .cons h (.cons h₁ h₂) => .cons h₁ (lift_concat (.cons h h₂))

instance [ParaF ϕ] : ParaF no_index λ α => List (ϕ α) where
  prop r := lift (ParaF.prop r)

macro_rules | `(tactic| para_step) => `(tactic| intro (h : lift _ _ _); induction h)

example : ParaT.prop (@f : ∀ {α}, List α → List α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ xs ys, lift r xs ys →
      lift r (f xs) (f ys)
:= rfl

example : ParaT.prop @List.reverse := by
  parametric
  simp only [List.reverse_cons, ← List.concat_eq_append]
  apply lift_concat
  parametric

example : ParaT.prop @List.dropLast := by
  parametric
  rename_i h _
  cases h
  parametric

example (f : Para (∀ {α}, List α → List α)) (g : α → β) (l) : (f l).map g = f (l.map g) :=
  lift_to_map (f.2 _ l _ (lift_map g l))

example : ParaT.prop (@f : ∀ {α}, (α → Bool) → List α → List α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ g h, (∀ x y, r x y → g x = h y) →
      ∀ xs ys, lift r xs ys →
        lift r (f g xs) (f h ys)
:= rfl

example : ParaT.prop @List.filter := by
  parametric
  rename_i h _ _ _ _ _ _ h' _ _
  unfold List.filter
  rw [h _ _ h']
  parametric

example : ParaT.prop @List.takeWhile := by
  parametric
  rename_i h _ _ _ _ _ _ h' _ _
  unfold List.takeWhile
  rw [h _ _ h']
  parametric

example : ParaT.prop @List.dropWhile := by
  parametric
  rename_i h _ _ _ _ _ _ h' _ _
  unfold List.dropWhile
  rw [h _ _ h']
  parametric

example (f : Para (∀ {α}, (α → Bool) → List α → List α)) (g : α → β) (h l) : (f (h ∘ g) l).map g = f h (l.map g) :=
  lift_to_map (f.2 (λ x y => g x = y) _ h (λ _ _ => congrArg h) l _ (lift_map g l))

example : ParaT.prop λ {α} x => List.map (λ f : α → α => f x) := by parametric

end List
