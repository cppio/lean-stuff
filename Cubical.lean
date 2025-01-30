def I : Type := Squash Bool
def i0 : I := .mk false
def i1 : I := .mk true

protected def I.lift₁ (f : Bool → Bool) : I → I :=
  Quot.lift (λ x => .mk (f x)) λ _ _ h => Quot.sound h

protected def I.lift₂ (f : Bool → Bool → Bool) : I → I → I :=
  Quot.lift (λ x => Quot.lift (λ y => .mk (f x y)) λ _ _ h => Quot.sound h) λ x x' h => by
    suffices (λ y => Squash.mk (f x y)) = (λ y => .mk (f x' y)) by
      dsimp
      funext _
      congr
    exact funext λ _ => Quot.sound h

def I.and : I → I → I := I.lift₂ Bool.and
def I.or : I → I → I := I.lift₂ Bool.or
def I.not : I → I := I.lift₁ Bool.not

def Path (x y : α) := { f : I → α // f i0 = x ∧ f i1 = y }

instance {x y : α} : CoeFun (Path x y) (λ _ => I → α) where
  coe p := p.1

def Path.h0 (p : Path x y) : p i0 = x := p.2.1
def Path.h1 (p : Path x y) : p i1 = y := p.2.2

def refl (x : α) : Path x x :=
  ⟨λ _ => x, rfl, rfl⟩

example (p : Path x y) : Eq x y :=
  p.h0.symm.trans ((congrArg p (Quot.sound trivial)).trans p.h1)

def sym (p : Path x y) : Path y x :=
  ⟨λ i => p (I.not i), p.h1, p.h0⟩

def funExt {β : α → _} {f g : (x : α) → β x} (p : (x : α) → Path (f x) (g x)) : Path f g :=
  ⟨λ i x => p x i, funext λ x => (p x).h0, funext λ x => (p x).h1⟩
