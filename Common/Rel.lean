variable {α : Sort u} (r : α → α → Prop)

class Reflexive : Prop where
  refl : r x x

variable {r} in
theorem Reflexive.ofEq [Reflexive r] {x y} (h : x = y) : r x y :=
  h ▸ refl

class Symmetric : Prop where
  symm : r x y → r y x

class Transitive : Prop where
  trans : r x y → r y z → r x z

namespace Eq
instance instReflexive : Reflexive (@Eq α) := ⟨@refl α⟩
instance instSymmetric : Symmetric (@Eq α) := ⟨@symm α⟩
instance instTransitive : Transitive (@Eq α) := ⟨@trans α⟩
end Eq

inductive ReflexiveClosure : α → α → Prop
  | base : r x y → ReflexiveClosure x y
  | refl : ReflexiveClosure x x

namespace ReflexiveClosure

instance instReflexive : Reflexive (ReflexiveClosure r) := ⟨@refl α r⟩

section rec

variable {r} {motive : ∀ x y, ReflexiveClosure r x y → Prop}
  (base : ∀ {x y} h, motive x y (base h))
  (refl : ∀ {x}, motive x x refl)

theorem rec' {x} : ∀ {y} h, motive x y h :=
  @rec α r x (motive x) (@base x) refl

end rec

section map

variable {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} {f : α → β}

theorem map [Reflexive s] (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, ReflexiveClosure r x y → s (f x) (f y) :=
  @rec' α r _ @h Reflexive.refl

theorem map' (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, ReflexiveClosure r x y → ReflexiveClosure s (f x) (f y) :=
  @map α β r _ f _ (base <| h ·)

end map

end ReflexiveClosure

inductive SymmetricClosure : α → α → Prop
  | base : r x y → SymmetricClosure x y
  | symm : SymmetricClosure x y → SymmetricClosure y x

namespace SymmetricClosure

instance instSymmetric : Symmetric (SymmetricClosure r) := ⟨@symm α r⟩

section rec

variable {r} {motive : ∀ x y, SymmetricClosure r x y → Prop}
  (base : ∀ {x y} h, motive x y (base h))
  (symm : ∀ {x y} h, motive y x (symm (.base h)))

theorem rec' {x y} h : motive x y h :=
  @rec α r (λ x y h => motive x y h ∧ motive y x (.symm h))
    (λ h => ⟨base h, symm h⟩)
    (λ _ ih => ⟨ih.2, ih.1⟩)
  x y h |>.1

end rec

section map

variable {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} {f : α → β}

theorem map [Symmetric s] (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, SymmetricClosure r x y → s (f x) (f y) :=
  @rec α r _ @h λ _ => Symmetric.symm

theorem map' (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, SymmetricClosure r x y → SymmetricClosure s (f x) (f y) :=
  @map α β r _ f _ (base <| h ·)

end map

end SymmetricClosure

inductive TransitiveClosure : α → α → Prop
  | base : r x y → TransitiveClosure x y
  | trans : TransitiveClosure x y → TransitiveClosure y z → TransitiveClosure x z

namespace TransitiveClosure

instance instTransitive : Transitive (TransitiveClosure r) := ⟨@trans α r⟩

section rec

variable {r} {motive : ∀ x y, TransitiveClosure r x y → Prop}
  (base : ∀ {x y} h, motive x y (base h))

theorem recl (trans : ∀ {x y z} h₁ h₂, motive x y h₁ → motive x z (trans h₁ (.base h₂)))
: ∀ {x y} h, motive x y h :=
  @rec α r motive @base λ {x y z} h₁ h₂ ih₁ _ =>
    @rec α r (λ y z h₂ => ∀ h₁, motive x y h₁ → motive x z (.trans h₁ h₂))
      (λ h₂ h₁ => trans h₁ h₂)
      (λ h₂ _ r₁ r₂ h₁ ih₁ => r₁ h₁ ih₁ |> r₂ (.trans h₁ h₂))
    y z h₂ h₁ ih₁

theorem recr (trans : ∀ {x y z} h₁ h₂, motive y z h₂ → motive x z (trans (.base h₁) h₂))
: ∀ {x y} h, motive x y h :=
  @rec α r motive @base λ {x y z} h₁ h₂ _ =>
    @rec α r (λ x y h₁ => ∀ h₂, motive y z h₂ → motive x z (.trans h₁ h₂))
      trans
      (λ _ h₁ r₁ r₂ h₂ ih₂ => r₁ (.trans h₁ h₂) <| r₂ h₂ ih₂)
    x y h₁ h₂

end rec

section map

variable {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} {f : α → β}

theorem map [Transitive s] (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, TransitiveClosure r x y → s (f x) (f y) :=
  @rec α r _ @h λ _ _ => Transitive.trans

theorem map' (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, TransitiveClosure r x y → TransitiveClosure s (f x) (f y) :=
  @map α β r _ f _ (base <| h ·)

end map

end TransitiveClosure

instance SymmetricClosure.instReflexive [Reflexive r] : Reflexive (SymmetricClosure r) where
  refl := base Reflexive.refl

instance TransitiveClosure.instReflexive [Reflexive r] : Reflexive (TransitiveClosure r) where
  refl := base Reflexive.refl

instance ReflexiveClosure.instSymmetric [Symmetric r] : Symmetric (ReflexiveClosure r) where
  symm := @rec' α r _ (λ h => base <| Symmetric.symm h) refl

instance TransitiveClosure.instSymmetric [Symmetric r] : Symmetric (TransitiveClosure r) where
  symm := @rec α r _ (λ h => base <| Symmetric.symm h) λ _ _ h₁ h₂ => trans h₂ h₁

instance ReflexiveClosure.instTransitive [Transitive r] : Transitive (ReflexiveClosure r) where
  trans h₁ :=
    @rec' α r (λ x y _ => ∀ z, ReflexiveClosure r y z → ReflexiveClosure r x z) (λ h₁ z h₂ =>
      @rec' α r (λ y z _ => ∀ x, r x y → ReflexiveClosure r x z)
        (λ h₂ _ h₁ => base <| Transitive.trans h₁ h₂)
        (λ _ => base)
      _ z h₂ _ h₁
    ) (λ _ h₂ => h₂) _ _ h₁ _

abbrev ReflexiveTransitiveClosure := ReflexiveClosure (TransitiveClosure r)

namespace ReflexiveTransitiveClosure

variable {r}

theorem base (h : r x y) : ReflexiveTransitiveClosure r x y :=
  .base (.base h)

theorem refl : ReflexiveTransitiveClosure r x x :=
  .refl

theorem trans : ReflexiveTransitiveClosure r x y → ReflexiveTransitiveClosure r y z → ReflexiveTransitiveClosure r x z :=
  Transitive.trans

section rec

variable {motive : ∀ x y, ReflexiveTransitiveClosure r x y → Prop}
  (base : ∀ {x y} h, motive x y (base h))
  (refl : ∀ {x}, motive x x refl)

theorem rec (trans : ∀ {x y z} h₁ h₂, motive x y h₁ → motive y z h₂ → motive x z (trans h₁ h₂))
: ∀ {x y} h, motive x y h :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.rec α r _ @base λ h₁ h₂ => @trans _ _ _ (ReflexiveClosure.base h₁) (ReflexiveClosure.base h₂)
  ) @refl

theorem recl (trans : ∀ {x y z} h₁ h₂, motive x y h₁ → motive x z (trans h₁ (.base h₂)))
: ∀ {x y} h, motive x y h :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.recl α r _ @base λ h₁ => @trans _ _ _ (ReflexiveClosure.base h₁)
  ) @refl

theorem recr
  (trans : ∀ {x y z} h₁ h₂, motive y z h₂ → motive x z (trans (.base h₁) h₂))
: ∀ {x y} h, motive x y h :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.recr α r _ @base λ h₁ h₂ => @trans _ _ _ h₁ (ReflexiveClosure.base h₂)
  ) @refl

end rec

section map

variable {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} {f : α → β}

theorem map [Reflexive s] [Transitive s] (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, ReflexiveTransitiveClosure r x y → s (f x) (f y) :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.rec α r _ @h λ _ _ => Transitive.trans
  ) Reflexive.refl

theorem map' (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, ReflexiveTransitiveClosure r x y → ReflexiveTransitiveClosure s (f x) (f y) :=
  @map α β r _ f _ _ (base <| h ·)

end map

end ReflexiveTransitiveClosure

abbrev EquivalenceClosure := ReflexiveTransitiveClosure (SymmetricClosure r)

namespace EquivalenceClosure

variable {r}

theorem base (h : r x y) : EquivalenceClosure r x y :=
  .base (.base h)

theorem refl : EquivalenceClosure r x x :=
  .refl

theorem symm : EquivalenceClosure r x y → EquivalenceClosure r y x :=
  Symmetric.symm

theorem trans : EquivalenceClosure r x y → EquivalenceClosure r y z → EquivalenceClosure r x z :=
  .trans

section rec

variable {motive : ∀ x y, EquivalenceClosure r x y → Prop}
  (base : ∀ {x y} h, motive x y (base h))
  (refl : ∀ {x}, motive x x refl)
  (symm : ∀ {x y} h, motive y x (symm (.base h)))

theorem rec (trans : ∀ {x y z} h₁ h₂, motive x y h₁ → motive y z h₂ → motive x z (trans h₁ h₂))
: ∀ {x y} h, motive x y h :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.rec α _ _ (
      @SymmetricClosure.rec' α r _ @base @symm
    ) λ h₁ h₂ => @trans _ _ _ (ReflexiveClosure.base h₁) (ReflexiveClosure.base h₂)
  ) @refl

theorem recl (trans : ∀ {x y z} h₁ h₂, motive x y h₁ → motive x z (trans h₁ (ReflexiveTransitiveClosure.base h₂)))
: ∀ {x y} h, motive x y h :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.recl α _ _ (
      @SymmetricClosure.rec' α r _ @base @symm
    ) λ h₁ => @trans _ _ _ (ReflexiveClosure.base h₁)
  ) @refl

theorem recr
  (trans : ∀ {x y z} h₁ h₂, motive y z h₂ → motive x z (trans (ReflexiveTransitiveClosure.base h₁) h₂))
: ∀ {x y} h, motive x y h :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.recr α _ _ (
      @SymmetricClosure.rec' α r _ @base @symm
    ) λ h₁ h₂ => @trans _ _ _ h₁ (ReflexiveClosure.base h₂)
  ) @refl

end rec

section map

variable {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} {f : α → β}

theorem map [Reflexive s] [Symmetric s] [Transitive s] (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, EquivalenceClosure r x y → s (f x) (f y) :=
  @ReflexiveClosure.rec' α _ _ (
    @TransitiveClosure.rec α _ _ (
      @SymmetricClosure.rec α r _ @h λ _ => Symmetric.symm
    ) λ _ _ => Transitive.trans
  ) Reflexive.refl

theorem map' (h : ∀ {x y}, r x y → s (f x) (f y))
: ∀ {x y}, EquivalenceClosure r x y → EquivalenceClosure s (f x) (f y) :=
  @map α β r _ f _ _ _ (base <| h ·)

end map

end EquivalenceClosure

@[simp]
theorem ReflexiveClosure_ReflexiveClosure : ReflexiveClosure (ReflexiveClosure r) = ReflexiveClosure r :=
  funext λ _ => funext λ _ => propext ⟨.map id, .base⟩

@[simp]
theorem SymmetricClosure_SymmetricClosure : SymmetricClosure (SymmetricClosure r) = SymmetricClosure r :=
  funext λ _ => funext λ _ => propext ⟨.map id, .base⟩

@[simp]
theorem TransitiveClosure_TransitiveClosure : TransitiveClosure (TransitiveClosure r) = TransitiveClosure r :=
  funext λ _ => funext λ _ => propext ⟨.map id, .base⟩

@[simp]
theorem TransitiveClosure_ReflexiveClosure : TransitiveClosure (ReflexiveClosure r) = ReflexiveTransitiveClosure r :=
  funext λ _ => funext λ _ => propext ⟨
    TransitiveClosure.map (f := id) <| ReflexiveClosure.map' .base,
    ReflexiveTransitiveClosure.map (f := id) λ h => .base <| .base h
  ⟩

@[simp]
theorem TransitiveClosure_SymmetricClosure_ReflexiveClosure : TransitiveClosure (SymmetricClosure (ReflexiveClosure r)) = EquivalenceClosure r :=
  funext λ _ => funext λ _ => propext ⟨
    TransitiveClosure.map (f := id) <| SymmetricClosure.map <| ReflexiveClosure.map' λ h => .base <| .base h,
    EquivalenceClosure.map (f := id) λ h => .base <| .base <| .base h
  ⟩

def Diamond := ∀ {x x₁ x₂}, r x x₁ → r x x₂ → ∃ x', r x₁ x' ∧ r x₂ x'

variable {r} in
theorem ReflexiveTransitiveClosure.diamond (h : Diamond r) : Diamond (ReflexiveTransitiveClosure r) := λ {x x₁ x₂} h₁ h₂ => by
  induction h₁ using rec generalizing x₂ with
  | @base _ x₁ h₁ =>
    suffices ∃ x', _ ∧ _ from
      let ⟨x', hx, hx'⟩ := this
      ⟨x', hx, .base hx'⟩
    induction h₂ using rec generalizing x₁ with
    | base h₂ =>
      let ⟨x₁, hx₁, hx₁'⟩ := h h₁ h₂
      exact ⟨_, .base hx₁, hx₁'⟩
    | refl => exact ⟨x₁, .refl, h₁⟩
    | trans _ _ ih₂ ih₂' =>
      let ⟨x₁, hx₁, hx₁'⟩ := ih₂ h₁
      let ⟨x₂, hx₂, hx₂'⟩ := ih₂' hx₁'
      exact ⟨x₂, .trans hx₁ hx₂, hx₂'⟩
  | refl => exact ⟨x₂, h₂, refl⟩
  | trans _ _ ih₁ ih₁' =>
    let ⟨x₁, hx₁, hx₁'⟩ := ih₁ h₂
    let ⟨x₂, hx₂, hx₂'⟩ := ih₁' hx₁
    exact ⟨x₂, hx₂, .trans hx₁' hx₂'⟩
