def iter (f : α → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => iter f (f x) n

theorem iter_succ : iter f x n.succ = f (iter f x n) := by
  induction n generalizing x with apply_assumption

def Foo : Type :=
  (hd : Nat → Nat) × (∀ s, Fin (hd s)) × (∀ s, Fin (hd (.succ s)))

def Foo.hd (self : Foo) : Nat :=
  self.1 .zero

def Foo.tl (self : Foo) : Foo :=
  ⟨(self.1 ·.succ), (self.2.1 ·.succ), (self.2.2 ·.succ)⟩

def Foo.good (self : Foo) : Fin self.hd :=
  self.2.1 .zero

def Foo.bad (self : Foo) : Fin self.tl.hd :=
  self.2.2 .zero

def Foo.corec (σ : Sort u) (hd : σ → Nat) (tl : σ → σ) (good : ∀ s, Fin (hd s)) (bad : ∀ s, Fin (hd (tl s))) (s : σ) : Foo :=
  ⟨(hd <| iter tl s ·), (good <| iter tl s ·), fun n => (bad (iter tl s n)).cast (congrArg hd iter_succ.symm)⟩

theorem Foo.hd_corec σ hd tl good bad s : (corec σ hd tl good bad s).hd = hd s :=
  rfl

theorem Foo.tl_corec σ hd tl good bad s : (corec σ hd tl good bad s).tl = corec σ hd tl good bad (tl s) :=
  rfl

theorem Foo.good_corec σ hd tl good bad s : (corec σ hd tl good bad s).good = good s :=
  rfl

theorem Foo.bad_corec σ hd tl good bad s : (corec σ hd tl good bad s).bad = bad s :=
  rfl

def Bar.Approx : Nat → (α : Type) × (α → Type)
  | 0 => ⟨Unit, fun _ => Unit⟩
  | ℓ + 1 => ⟨(hd : Nat) × (tl : (Approx ℓ).1) × Fin hd × ((Approx ℓ).2 tl), fun s => Fin s.1⟩

def Bar.Approx.Agree : ∀ ℓ ℓ', (a : (Approx ℓ).1) → (a' : (Approx ℓ').1) → Prop × ((Approx ℓ).2 a → (Approx ℓ').2 a' → Prop)
  | 0, _, _, _ => (True, fun _ _ => True)
  | _ + 1, 0, _, _ => (True, fun _ _ => True)
  | ℓ + 1, ℓ' + 1, a, a' => (∃ hd : a.1 = a'.1, (Agree ℓ ℓ' a.2.1 a'.2.1).1 ∧ a.2.2.1 = hd ▸ a'.2.2.1 ∧ (Agree ℓ ℓ' a.2.1 a'.2.1).2 a.2.2.2 a'.2.2.2, fun lhs (rhs : Fin _) => ∃ hd : a.1 = a'.1, hd ▸ lhs = rhs)

def Bar : Type :=
  { f : ∀ ℓ, (Bar.Approx ℓ).1 // ∀ ℓ ℓ', (Bar.Approx.Agree ℓ ℓ' (f ℓ) (f ℓ')).1 }

def Bar.hd (self : Bar) : Nat :=
  (self.1 (.succ .zero)).1

def Bar.tl (self : Bar) : Bar :=
  ⟨fun ℓ => (self.1 ℓ.succ).2.1, fun ℓ ℓ' => (self.2 ℓ.succ ℓ'.succ).2.1⟩

def Bar.good (self : Bar) : Fin self.hd :=
  (self.1 (.succ .zero)).2.2.1

def Bar.bad (self : Bar) : Fin self.tl.hd :=
  (self.1 (.succ (.succ .zero))).2.2.2

def Bar.corec' (σ : Sort u) (hd : σ → Nat) (tl : σ → σ) (good : ∀ s, Fin (hd s)) (bad : ∀ s, Fin (hd (tl s))) (s : σ) : ∀ ℓ, (x : (Approx ℓ).1) × (Fin (hd s) → (Approx ℓ).2 x)
  | 0 => ⟨(), fun _ => ()⟩
  | ℓ + 1 => ⟨⟨hd s, (corec' σ hd tl good bad (tl s) ℓ).1, good s, (corec' σ hd tl good bad (tl s) ℓ).2 (bad s)⟩, id⟩

def Bar.corec (σ : Sort u) (hd : σ → Nat) (tl : σ → σ) (good : ∀ s, Fin (hd s)) (bad : ∀ s, Fin (hd (tl s))) (s : σ) : Bar :=
  .mk (corec' σ hd tl good bad s · |>.1) fun ℓ ℓ' => by
    induction ℓ generalizing s ℓ' with | zero => constructor | succ ℓ ih =>
    cases ℓ' with | zero => constructor | succ ℓ' =>
    refine ⟨rfl, ih (tl s) ℓ', rfl, ?_⟩
    cases ℓ with | zero => constructor | succ ℓ =>
    cases ℓ' with | zero => constructor | succ ℓ' =>
    exact ⟨rfl, rfl⟩

theorem Bar.hd_corec σ hd tl good bad s : (corec σ hd tl good bad s).hd = hd s :=
  rfl

theorem Bar.tl_corec σ hd tl good bad s : (corec σ hd tl good bad s).tl = corec σ hd tl good bad (tl s) :=
  rfl

theorem Bar.good_corec σ hd tl good bad s : (corec σ hd tl good bad s).good = good s :=
  rfl

theorem Bar.bad_corec σ hd tl good bad s : (corec σ hd tl good bad s).bad = bad s :=
  rfl

axiom OhNo : Type
axiom OhNo.hd (self : OhNo) : Nat
axiom OhNo.tl (self : OhNo) : OhNo
axiom OhNo.ohno (self : OhNo) (n : Nat) : Fin (hd <| n.rec self fun _ => tl)
