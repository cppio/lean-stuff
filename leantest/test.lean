inductive eq₁ {α} : α → α → Prop
| refl {x} : eq₁ x x
-- | symm {x y} : eq₁ y x → eq₁ x y

inductive eq₂ {α} (x) : α → Prop
| refl : eq₂ x

def typeof {α} (_ : α) := α
#reduce typeof $ @eq₁.rec
#reduce typeof $ @eq₂.rec

def eq₂.rec' {α} {motive : α → α → Sort*} (f : ∀ {x}, motive x x) {x} : ∀ {y}, eq₂ x y → motive x y :=
@eq₂.rec α x (motive x) f

def eq₁.rec' : ∀ {α x} {motive : α → Sort*}, motive x → ∀ {y}, eq₁ x y → motive y :=
λ α x motive f y h, @eq₁.rec α (λ x' y', x = x' → motive y') (λ x' h', h' ▸ f) x y h rfl
