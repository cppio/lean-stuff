/-!
Variations of Cantor's theorem
-/

/--
# No surjective f : α → 𝒫 α
We want to create p ∈ 𝒫 α such that p ∉ f[α].
We have α attributes to choose (whether or not x ∈ p for each x ∈ α) and we have α constraints (p ≠ f x for each x ∈ α).
We can achieve the result by making each attribute satisfy the corresponding constraint: ensure that x ∈ p or x ∉ p forces p ≠ f x.
We can do so by setting x ∈ p ↔ x ∉ f x, and so p = {x ∈ α | x ∉ f x} suffices.
-/
def cantor_sur (f : α → (α → Prop)) : { g : α → Prop // ∀ x, ¬(∀ y, g y ↔ f x y) } :=
  ⟨fun x => ¬f x x, fun x h => not_iff_self (h x)⟩

/--
# No injective f : 𝒫 α → α
To disprove injectivity, we need to find an element of α whose preimage is not a subsingleton.
The only way we can get elements of α is through f, so we wish to find a p ∈ 𝒫 α such that f⁻¹[f p] ≠ {p}.
In other words, we want to choose p so that f p is not in the set of points whose preimages are singletons.
There are at most α such points to avoid, and we have α attributes to choose from, which suggests we can diagonalize as follows:
If x has singleton preimage, then we want x ∈ p ↔ x ∉ f⁻¹ x.
It doesn't matter whether x ∈ p when x doesn't have singleton preimage, and we can use this flexibility to simplify the condition.
We can let x ∈ p ↔ x ∉ q x, where q x ∈ 𝒫 x is defined in such a way that it equals the unique element of the preimage of x, if it exists.
There are two simple ways of achieving this: ⋃ f⁻¹[x] and ⋂ f⁻¹[x], since ⋃ {s} = ⋂ {s} = s.
Thus, we can define p = {x ∈ α | x ∉ ⋃ f⁻¹[x]}, or equivalently using ⋂.
Now observe that f p ∈ p ↔ f p ∉ ⋃ f⁻¹[f p].
If f were injective, then f⁻¹[f p] = {p}, but this means f p ∈ p ↔ f p ∉ p, a contradiction.

Alternatively, we can make use of the fact that an injection from 𝒫 α → α implies a surjection from α → 𝒫 α.
In general, turning an injection β → α to a surjection α → β requires arbitrarily choosing an element of β to for points not in the image of the injection, and also requires excluded middle to determine whether each point is in fact in the image.
However, in the special case β = 𝒫 α, we have two natural elements to choose from: ∅ and 𝒫 α.
Furthermore, we can define the function without using excluded middle:
Suppose we want to define g x = p if f p = x (p is unique if it exists since f is assumed to be injective) and g x = ∅ otherwise.
Then, y ∈ g x ↔ ∃ p, f p = x ∧ y ∈ p, so we see that g x = ⋃ f⁻¹[x].
Similarly, if we use 𝒫 α instead of ∅, we get g x = ⋂ f⁻¹[x].
Inlining the construction from the previous theorem, we get that the witness of the non-surjectivity of g, and hence the non-injectivity of f, is {x ∈ α | x ∉ g x} = {x ∈ α | x ∉ ⋃ f⁻¹[x]}, which is the same set as in the first proof.
-/
def cantor_inj (f : (α → Prop) → α) : { g // ¬(∀ {h}, f g = f h → g = h) } :=
  let g x := ∀ h, x = f h → ¬h x
  ⟨g, fun inj => @not_iff_self (g (f g)) ⟨fun p _ q => inj q ▸ p, fun p => p g rfl⟩⟩

/--
# No injective f : 𝒫 𝒫 α → α
Cantor's theorem tells us that |α| < |𝒫 α|, and so intuitively |𝒫 𝒫 α| is even bigger.
Given an injection 𝒫 𝒫 α → α, we could compose it with an injection 𝒫 α → 𝒫 𝒫 α to get an injection 𝒫 α → α, contradicting the previous result.
A simple choice of the injection 𝒫 α → 𝒫 𝒫 α is p ↦ {p}.
-/
def cantor_inj₂ (f : ((α → Prop) → Prop) → α) : { g // ¬∀ {h}, f g = f h → g = h } :=
  let ⟨s, hs⟩ := cantor_inj fun x => f (Eq x)
  ⟨Eq s, fun h => hs fun h' => (congrFun (h h') _).mpr rfl⟩

/--
# No surjective f : α → 𝒫 𝒫 α
As in the previous proof, we want to compose a hypothetical surjection f : α → 𝒫 𝒫 α with a surjection 𝒫 𝒫 α → 𝒫 α to get a surjection α → 𝒫 α, contradicting the first statement of the theorem.
Unlike the previous proof, where there was a natural injection α → 𝒫 α that works for all α, including 𝒫 α, in this case there isn't a natural surjection 𝒫 α → α.
However, there is a natural surjection 𝒫 𝒫 α → 𝒫 α.
We know that p ↦ {p} is an injection 𝒫 α → 𝒫 𝒫 α, and we can try to find an explicit left inverse as our desired surjection.
We can use the same trick as in the proof of no injective 𝒫 α → α: use ⋃ or ⋂, which is surjective since ⋃ {p} = ⋂ {p} = p.
Then, when given p ∉ (⋂ ∘ f)[α], we get that {p} ∉ f[α].
-/
def cantor_sur₂ (f : α → ((α → Prop) → Prop)) : { g // ∀ x, g ≠ f x } :=
  let ⟨foo, bar⟩ := cantor_sur fun x y : α => ∀ p, f x p → p y
  ⟨fun p => p = foo, fun x h => bar x fun _ => ⟨fun h' _ hp => (h ▸ hp) ▸ h', fun h' => h' foo (h ▸ rfl)⟩⟩

/--
A variant from the paper "A variation of Reynolds-Hurkens Paradox" by Thierry Coquand.
-/
def cantor_sur₂' (f : α → ((α → Prop) → Prop)) (δ : α → α) (hδ : ∀ {x p}, f (δ x) p ↔ f x (p ∘ δ)) : { g : (α → Prop) → Prop // ∀ x, ¬(∀ p, f x p = g (p ∘ δ)) } :=
  let X₀ p := ∀ x, p x → ¬f x p
  ⟨X₀, fun x h =>
    let p₀ x := ∀ p, p (δ x) → ¬f x p
    have s₁ x (h : p₀ x) : p₀ (δ x) := fun p h₁ h₂ => h (p ∘ δ) h₁ (hδ.mp h₂)
    have s₂ p (h : X₀ p) : X₀ (p ∘ δ) := fun x h₁ h₂ => h (δ x) h₁ (hδ.mpr h₂)
    have l₁ : X₀ p₀ := fun x h => h p₀ (s₁ x h)
    have l₂ : p₀ x := fun p h₁ h₂ => (h p ▸ h₂) x h₁ (h _ ▸ s₂ _ (h p ▸ h₂))
    l₁ x l₂ (h p₀ ▸ s₂ p₀ l₁)
  ⟩

/--
Reynolds-Hurkens-Coquand Paradox
-/
theorem no_impredicative
  (Pi : (Type u → Type u) → Type u)
  (lam : ∀ {F}, (∀ A, F A) → Pi F)
  (app : ∀ {F}, Pi F → ∀ A, F A)
  (app_lam : ∀ {F} f A, @app F (lam f) A = f A)
: False :=
  let T X := (X → Prop) → Prop
  let map {X Y} (f : X → Y) (F : T X) : T Y := fun q => F fun x => q (f x)
  let A := Pi fun X => (T X → X) → X
  let intro (u : T A) : A := lam fun X f => f (map (fun a : A => app a X f) u)
  let elim (a : A) : T A := app a _ (map intro)
  let δ := intro ∘ elim
  have conv {u} : elim (intro u) = map δ u := congrFun (app_lam (F := fun X => _ → X) _ _) _
  (cantor_sur₂' elim δ (by intros; dsimp [δ]; rw [conv]; rfl)).property (intro _) (congrFun conv)
