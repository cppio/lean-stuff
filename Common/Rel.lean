variable {α : Sort u} (r : α → α → Prop)

class Reflexive : Prop where
  refl : r x x

theorem Reflexive.ofEq {r : α → α → Prop} [Reflexive r] {x y} (h : x = y) : r x y := h ▸ refl

class Symmetric : Prop where
  symm : r x y → r y x

class Transitive : Prop where
  trans : r x y → r y z → r x z

class abbrev Equivalence' : Prop := Reflexive r, Symmetric r, Transitive r

inductive ReflexiveTransitiveClosure : α → α → Prop
  | base : r x y → ReflexiveTransitiveClosure x y
  | refl : ReflexiveTransitiveClosure x x
  | trans : ReflexiveTransitiveClosure x y → ReflexiveTransitiveClosure y z → ReflexiveTransitiveClosure x z

instance ReflexiveTransitiveClosure.instReflexive : Reflexive (ReflexiveTransitiveClosure r) := ⟨@refl α r⟩
instance ReflexiveTransitiveClosure.instTransitive : Transitive (ReflexiveTransitiveClosure r) := ⟨@trans α r⟩

section rec

variable {r} {motive : ∀ x y, ReflexiveTransitiveClosure r x y → Prop}
  (base : ∀ {x y} h, motive x y (base h))
  (refl : ∀ {x}, motive x x refl)

def ReflexiveTransitiveClosure.recl
  (trans : ∀ {x y z} h₁ h₂, motive x y h₁ → motive x z (trans h₁ (.base h₂)))
: ∀ {x y} h, motive x y h :=
  @rec α r motive base refl λ {x y z} h₁ h₂ ih₁ _ =>
    @rec α r (λ y z h₂ => ∀ h₁, motive x y h₁ → motive x z (.trans h₁ h₂))
      (λ h₂ h₁ => trans h₁ h₂)
      (λ _ ih₁ => ih₁)
      (λ h₂ _ r₁ r₂ h₁ ih₁ => r₁ h₁ ih₁ |> r₂ (.trans h₁ h₂))
    y z h₂ h₁ ih₁

def ReflexiveTransitiveClosure.recr
  (trans : ∀ {x y z} h₁ h₂, motive y z h₂ → motive x z (trans (.base h₁) h₂))
: ∀ {x y} h, motive x y h :=
  @rec α r motive base refl λ {x y z} h₁ h₂ _ =>
    @rec α r (λ x y h₁ => ∀ h₂, motive y z h₂ → motive x z (.trans h₁ h₂))
      trans
      (λ _ ih₂ => ih₂)
      (λ _ h₁ r₁ r₂ h₂ ih₂ => r₁ (.trans h₁ h₂) <| r₂ h₂ ih₂)
    x y h₁ h₂

end rec

def ReflexiveTransitiveClosure.lift {β : Sort v} {r s} {f : α → β} (h : ∀ {x y}, r x y → s (f x) (f y)) :
  ∀ {x y}, ReflexiveTransitiveClosure r x y → ReflexiveTransitiveClosure s (f x) (f y)
:=
  @rec α r _
    (base <| h ·)
    refl
    (λ _ _ => trans)

inductive EquivalenceClosure : α → α → Prop
  | base : r x y → EquivalenceClosure x y
  | refl : EquivalenceClosure x x
  | symm : EquivalenceClosure x y → EquivalenceClosure y x
  | trans : EquivalenceClosure x y → EquivalenceClosure y z → EquivalenceClosure x z

instance EquivalenceClosure.instReflexive : Reflexive (EquivalenceClosure r) := ⟨@refl α r⟩
instance EquivalenceClosure.instSymmetric : Symmetric (EquivalenceClosure r) := ⟨@symm α r⟩
instance EquivalenceClosure.instTransitive : Transitive (EquivalenceClosure r) := ⟨@trans α r⟩

def EquivalenceClosure.lift {β : Sort v} {r s} {f : α → β} (h : ∀ {x y}, r x y → s (f x) (f y)) :
  ∀ {x y}, EquivalenceClosure r x y → EquivalenceClosure s (f x) (f y)
:=
  @rec α r _
    (base <| h ·)
    refl
    (λ _ => symm)
    (λ _ _ => trans)
