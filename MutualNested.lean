def Monotone (f : Prop → Prop) : Prop :=
  ∀ ⦃p p'⦄, (p → p') → f p → f p'

def Monotone₂ (f : Prop → Prop → Prop) : Prop :=
  ∀ ⦃p p' q q'⦄, (p → p') → (q → q') → f p q → f p' q'

namespace Inductive

-- ∀ p, (f p → p) → p
def μ (f : Prop → Prop) (hf : Monotone f) : Prop :=
  f (μ f hf)
  least_fixpoint monotonicity hf

namespace μ

def rec : ∀ p, (f p → p) → μ f hf → p :=
  fixpoint_induct f hf

def fold : f (μ f hf) → μ f hf :=
  (eq_def f hf).mpr

def mono₁ (hf : Monotone₂ f) : Monotone fun p => μ (f p) fun _ _ => hf id :=
  fun _ _ hp => rec _ <| fold ∘ hf hp id

def mono₂ (hf : Monotone₂ f) : Monotone fun q => μ (f · q) fun _ _ hp => hf hp id :=
  fun _ _ hq => rec _ <| fold ∘ hf id hq

end μ

mutual

-- ∀ p q, (f p q → p) → (g p q → q) → p
def P (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  f (P f g hf hg) (Q f g hf hg)
  least_fixpoint monotonicity fun _ _ ⟨hp, hq⟩ => hf hp hq

-- ∀ p q, (f p q → p) → (g p q → q) → q
def Q (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  g (P f g hf hg) (Q f g hf hg)
  least_fixpoint monotonicity fun _ _ ⟨hp, hq⟩ => hg hp hq

end

namespace P

unseal P in
def rec p q (hp : f p q → p) (hq : g p q → q) : P f g hf hg → p :=
  fun ⟨_, ⟨_, h⟩, hp'⟩ => (h ⟨p, q⟩ ⟨hp, hq⟩).left hp'

def fold : f (P f g hf hg) (Q f g hf hg) → P f g hf hg :=
  (eq_def f g hf hg).mpr

end P

namespace Q

unseal Q in
def rec p q (hp : f p q → p) (hq : g p q → q) : Q f g hf hg → q :=
  fun ⟨_, ⟨_, h⟩, hq'⟩ => (h ⟨p, q⟩ ⟨hp, hq⟩).right hq'

def fold : g (P f g hf hg) (Q f g hf hg) → Q f g hf hg :=
  (eq_def f g hf hg).mpr

end Q

def P₁ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  μ (fun p => f p (μ (fun q => g p q) fun _ _ => hg id)) fun _ _ h => hf h (μ.mono₁ hg h)

def Q₁ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  μ (fun q => g (P₁ f g hf hg) q) fun _ _ => hg id

def Q₂ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  μ (fun q => g (μ (fun p => f p q) fun _ _ hp => hf hp id) q) fun _ _ h => hg (μ.mono₂ hf h) h

def P₂ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  μ (fun p => f p (Q₂ f g hf hg)) fun _ _ hp => hf hp id

theorem nested₁_eq_nested₂ : (P₁ f g hf hg ↔ P₂ f g hf hg) ∧ (Q₁ f g hf hg ↔ Q₂ f g hf hg) where
  left.mp := μ.rec (P₂ ..) (μ.fold ∘ hf id (μ.rec (Q₂ ..) (μ.fold ∘ id)))
  left.mpr := μ.rec (P₁ ..) (μ.fold ∘ hf id (μ.rec (Q₁ ..) (μ.fold ∘ hg (μ.rec (P₁ f g hf hg) (μ.fold ∘ id)) id)))
  right.mp := μ.rec (Q₂ ..) (μ.fold ∘ hg (μ.rec (P₂ ..) (μ.fold ∘ hf id (μ.rec (Q₂ f g hf hg) (μ.fold ∘ id)))) id)
  right.mpr := μ.rec (Q₁ ..) (μ.fold ∘ hg (μ.rec (P₁ ..) (μ.fold ∘ id)) id)

theorem mutual_eq_nested₁ : (P f g hf hg ↔ P₁ f g hf hg) ∧ (Q f g hf hg ↔ Q₁ f g hf hg) where
  left.mp := P.rec (P₁ ..) (Q₁ ..) (μ.fold ∘ id) μ.fold
  left.mpr := μ.rec (P ..) (P.fold ∘ hf id (μ.rec (Q ..) Q.fold))
  right.mp := Q.rec (P₁ ..) (Q₁ ..) (μ.fold ∘ id) μ.fold
  right.mpr := μ.rec (Q ..) (Q.fold ∘ hg (μ.rec (P ..) (P.fold ∘ hf id (μ.rec (Q ..) Q.fold))) id)

theorem mutual_eq_nested₂ : (P f g hf hg ↔ P₂ f g hf hg) ∧ (Q f g hf hg ↔ Q₂ f g hf hg) where
  left.mp := P.rec (P₂ ..) (Q₂ ..) (μ.fold ∘ id) (μ.fold ∘ id)
  left.mpr := μ.rec (P ..) (P.fold ∘ hf id (μ.rec (Q ..) (Q.fold ∘ hg (μ.rec (P ..) P.fold) id)))
  right.mp := Q.rec (P₂ ..) (Q₂ ..) (μ.fold ∘ id) (μ.fold ∘ id)
  right.mpr := μ.rec (Q ..) (Q.fold ∘ hg (μ.rec (P ..) P.fold) id)

end Inductive

namespace Coinductive

-- ∃ p, (p → f p) ∧ p
def ν (f : Prop → Prop) (hf : Monotone f) : Prop :=
  f (ν f hf)
  greatest_fixpoint monotonicity fun _ _ h => hf h

namespace ν

def corec : ∀ p, (p → f p) → p → ν f hf :=
  fixpoint_induct f hf

def unfold : ν f hf → f (ν f hf) :=
  (eq_def f hf).mp

def mono₁ (hf : Monotone₂ f) : Monotone fun p => ν (f p) fun _ _ => hf id :=
  fun _ _ hp => corec _ <| hf hp id ∘ unfold

def mono₂ (hf : Monotone₂ f) : Monotone fun q => ν (f · q) fun _ _ hp => hf hp id :=
  fun _ _ hq => corec _ <| hf id hq ∘ unfold

end ν

mutual

-- ∃ p q, (p → f p q) ∧ (q → g p q) ∧ p
def P (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  f (P f g hf hg) (Q f g hf hg)
  greatest_fixpoint monotonicity id fun _ _ ⟨hp, hq⟩ => hf hp hq

-- ∃ p q, (p → f p q) ∧ (q → g p q) ∧ q
def Q (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  g (P f g hf hg) (Q f g hf hg)
  greatest_fixpoint monotonicity id fun _ _ ⟨hp, hq⟩ => hg hp hq

end

namespace P

unseal P in
def corec p q (hp : p → f p q) (hq : q → g p q) (hp' : p) : P f g hf hg :=
  fun _ ⟨_, h⟩ => (h ⟨p, q⟩ ⟨hp, hq⟩).left hp'

def unfold : P f g hf hg → f (P f g hf hg) (Q f g hf hg) :=
  (eq_def f g hf hg).mp

end P

namespace Q

unseal Q in
def corec p q (hp : p → f p q) (hq : q → g p q) (hq' : q) : Q f g hf hg :=
  fun _ ⟨_, h⟩ => (h ⟨p, q⟩ ⟨hp, hq⟩).right hq'

def unfold : Q f g hf hg → g (P f g hf hg) (Q f g hf hg) :=
  (eq_def f g hf hg).mp

end Q

def P₁ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  ν (fun p => f p (ν (fun q => g p q) fun _ _ => hg id)) fun _ _ h => hf h (ν.mono₁ hg h)

def Q₁ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  ν (fun q => g (P₁ f g hf hg) q) fun _ _ => hg id

def Q₂ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  ν (fun q => g (ν (fun p => f p q) fun _ _ hp => hf hp id) q) fun _ _ h => hg (ν.mono₂ hf h) h

def P₂ (f g : Prop → Prop → Prop) (hf : Monotone₂ f) (hg : Monotone₂ g) : Prop :=
  ν (fun p => f p (Q₂ f g hf hg)) fun _ _ hp => hf hp id

theorem nested₁_eq_nested₂ : (P₁ f g hf hg ↔ P₂ f g hf hg) ∧ (Q₁ f g hf hg ↔ Q₂ f g hf hg) where
  left.mp := ν.corec (P₁ ..) (hf id (ν.corec (Q₁ ..) (hg (ν.corec (P₁ f g hf hg) ν.unfold) id ∘ ν.unfold)) ∘ ν.unfold)
  left.mpr := ν.corec (P₂ ..) (hf id (ν.corec (Q₂ ..) ν.unfold) ∘ ν.unfold)
  right.mp := ν.corec (Q₁ ..) (hg (ν.corec (P₁ ..) ν.unfold) id ∘ ν.unfold)
  right.mpr := ν.corec (Q₂ ..) (hg (ν.corec (P₂ ..) (hf id (ν.corec (Q₂ f g hf hg) ν.unfold) ∘ ν.unfold)) id ∘ ν.unfold)

theorem mutual_eq_nested₁ : (P f g hf hg ↔ P₁ f g hf hg) ∧ (Q f g hf hg ↔ Q₁ f g hf hg) where
  left.mp := ν.corec (P ..) (hf id (ν.corec (Q ..) Q.unfold) ∘ P.unfold)
  left.mpr := P.corec (P₁ ..) (Q₁ ..) ν.unfold ν.unfold
  right.mp := ν.corec (Q ..) (hg (ν.corec (P ..) (hf id (ν.corec (Q ..) Q.unfold) ∘ P.unfold)) id ∘ Q.unfold)
  right.mpr := Q.corec (P₁ ..) (Q₁ ..) ν.unfold ν.unfold

theorem mutual_eq_nested₂ : (P f g hf hg ↔ P₂ f g hf hg) ∧ (Q f g hf hg ↔ Q₂ f g hf hg) where
  left.mp := ν.corec (P ..) (hf id (ν.corec (Q ..) (hg (ν.corec (P ..) P.unfold) id ∘ Q.unfold)) ∘ P.unfold)
  left.mpr := P.corec (P₂ ..) (Q₂ ..) ν.unfold ν.unfold
  right.mp := ν.corec (Q ..) (hg (ν.corec (P ..) P.unfold) id ∘ Q.unfold)
  right.mpr := Q.corec (P₂ ..) (Q₂ ..) ν.unfold ν.unfold

end Coinductive
