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

@[simp]
def lift (r : α → β → Prop) : List α → List β → Prop
  | [],    []    => True
  | x::xs, y::ys => r x y ∧ lift r xs ys
  | _,     _     => False

theorem lift_map (g : α → β) : ∀ l, lift (λ x y => g x = y) l (l.map g)
  | [] => trivial
  | _::l => ⟨rfl, lift_map g l⟩

theorem lift_to_map {g : α → β} : ∀ {l l'}, lift (λ x y => g x = y) l l' → l.map g = l'
  | [],   [],   _ => rfl
  | _::_, _::_, h => congrArg₂ _ h.1 (lift_to_map h.2)

theorem lift_concat : ∀ {xs ys}, lift r (x::xs) (y::ys) → lift r (xs.concat x) (ys.concat y)
  | [], [], h => h
  | _::_, _::_, ⟨h₁, h₂, h₃⟩ => ⟨h₂, lift_concat ⟨h₁, h₃⟩⟩

instance [ParaF ϕ] : ParaF no_index λ α => List (ϕ α) where
  prop r := lift (ParaF.prop r)

example : ParaT.prop (@f : ∀ {α}, List α → List α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ l l', lift r l l' →
      lift r (f l) (f l')
:= rfl

example : ParaT.prop (@List.reverse) := by
  intro _ _ r
  let rec h : ∀ l l', lift r l l' → lift r l.reverse l'.reverse
  | [], [], _ => by parametric
  | x::xs, y::ys, ⟨_, _⟩ => by
    simp only [List.reverse_cons, ← List.concat_eq_append]
    apply lift_concat
    parametric h
  exact h

example : ParaT.prop (@List.dropLast) := by
  intro _ _ r
  let rec h : ∀ l l', lift r l l' → lift r l.dropLast l'.dropLast
  | [], [], _ => by parametric
  | _::[], _::[], _ => by parametric
  | _::_::_, _::_::_, ⟨_, _⟩ => by parametric h
  exact h

example (f : Para (∀ {α}, List α → List α)) (g : α → β) (l) : (f l).map g = f (l.map g) :=
  lift_to_map (f.2 _ l _ (lift_map g l))

example : ParaT.prop (@f : ∀ {α}, (α → Bool) → List α → List α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ g h, (∀ x y, r x y → g x = h y) →
      ∀ l l', lift r l l' →
        lift r (f g l) (f h l')
:= rfl

example : ParaT.prop (@List.filter) := by
  intro _ _ r g h hgh
  let rec h : ∀ l l', lift r l l' → lift r (l.filter g) (l'.filter h)
  | [], [], _ => by parametric
  | x::_, y::_, ⟨h', _⟩ => by
    unfold List.filter
    rw [hgh x y h']
    parametric h
  exact h

example : ParaT.prop (@List.takeWhile) := by
  intro _ _ r g h hgh
  let rec h : ∀ l l', lift r l l' → lift r (l.takeWhile g) (l'.takeWhile h)
  | [], [], _ => by parametric
  | x::_, y::_, ⟨h', _⟩ => by
    unfold List.takeWhile
    rw [hgh x y h']
    parametric h
  exact h

example : ParaT.prop (@List.dropWhile) := by
  intro _ _ r g h hgh
  let rec h : ∀ l l', lift r l l' → lift r (l.dropWhile g) (l'.dropWhile h)
  | [], [], _ => by parametric
  | x::_, y::_, ⟨h', _⟩ => by
    unfold List.dropWhile
    rw [hgh x y h']
    parametric h
  exact h

example (f : Para (∀ {α}, (α → Bool) → List α → List α)) (g : α → β) (h l) : (f (h ∘ g) l).map g = f h (l.map g) :=
  lift_to_map (f.2 (λ x y => g x = y) _ h (λ _ _ => congrArg h) l _ (lift_map g l))

example : ParaT.prop λ {α} x => List.map (λ f : α → α => f x) := by
  intro α β r x y _
  let rec h : ∀ l l', lift (λ (f : α → α) (g : β → β) => ∀ x y, r x y → r (f x) (g y)) l l' → lift r (l.map λ f => f x) (l'.map λ g => g y)
  | [], [], _ => by parametric
  | _::_, _::_, ⟨_, _⟩ => by parametric h
  exact h

end List
