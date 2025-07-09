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

def Baz.Approx : Nat → (α : Type) × (α → Type × Type × Type)
  | 0 => ⟨Unit, fun _ => (Unit, Unit, Unit)⟩
  | ℓ + 1 => ⟨(hd : Nat) × (tl : (Approx ℓ).1) × Fin hd × ((Approx ℓ).2 tl).1 × ((Approx ℓ).2 tl).2.1, fun s => (Fin (s.1 + 1), ((Approx ℓ).2 s.2.1).2.2, Fin (s.1 + 2))⟩

def Baz.Approx.Agree : ∀ ℓ ℓ', (a : (Approx ℓ).1) → (a' : (Approx ℓ').1) → (p : Prop) × (p → (((Approx ℓ).2 a).1 → ((Approx ℓ').2 a').1 → Prop) × (((Approx ℓ).2 a).2.1 → ((Approx ℓ').2 a').2.1 → Prop) × (((Approx ℓ).2 a).2.2 → ((Approx ℓ').2 a').2.2 → Prop))
  | 0, _, _, _ => ⟨True, fun _ => (fun _ _ => True, fun _ _ => True, fun _ _ => True)⟩
  | _ + 1, 0, _, _ => ⟨True, fun _ => (fun _ _ => True, fun _ _ => True, fun _ _ => True)⟩
  | ℓ + 1, ℓ' + 1, a, a' => ⟨∃ hd : a.1 = a'.1, ∃ tl : (Agree ℓ ℓ' a.2.1 a'.2.1).1, a.2.2.1 = hd ▸ a'.2.2.1 ∧ ((Agree ℓ ℓ' a.2.1 a'.2.1).2 tl).1 a.2.2.2.1 a'.2.2.2.1, fun h => (fun (lhs rhs : Fin _) => h.1 ▸ lhs = rhs, ((Agree ℓ ℓ' a.2.1 a'.2.1).2 h.2.1).2.2, fun (lhs rhs : Fin _) => h.1 ▸ lhs = rhs)⟩

def Baz : Type :=
  { f : ∀ ℓ, (Baz.Approx ℓ).1 // ∀ ℓ ℓ', (Baz.Approx.Agree ℓ ℓ' (f ℓ) (f ℓ')).1 }

def Baz.hd (self : Baz) : Nat :=
  (self.1 (.succ .zero)).1

def Baz.tl (self : Baz) : Baz :=
  ⟨fun ℓ => (self.1 ℓ.succ).2.1, fun ℓ ℓ' => (self.2 ℓ.succ ℓ'.succ).2.1⟩

def Baz.zero (self : Baz) : Fin self.hd :=
  (self.1 (.succ .zero)).2.2.1

def Baz.one (self : Baz) : Fin (self.tl.hd + 1) :=
  (self.1 (.succ (.succ .zero))).2.2.2.1

def Baz.two (self : Baz) : Fin (self.tl.tl.hd + 2) :=
  (self.1 (.succ (.succ (.succ .zero)))).2.2.2.2

def Baz.corec' (σ : Sort u) (hd : σ → Nat) (tl : σ → σ) (zero : ∀ s, Fin (hd s)) (one : ∀ s, Fin (hd (tl s) + 1)) (two : ∀ s, Fin (hd (tl (tl s)) + 2)) (s : σ) : ∀ ℓ, (x : (Baz.Approx ℓ).1) × (Fin (hd s + 1) → ((Baz.Approx ℓ).2 x).1) × (Fin (hd (tl s) + 2) → ((Baz.Approx ℓ).2 x).2.1) × (Fin (hd s + 2) → ((Baz.Approx ℓ).2 x).2.2)
  | 0 => ⟨(), fun _ => (), fun _ => (), fun _ => ()⟩
  | ℓ + 1 => ⟨⟨hd s, (corec' σ hd tl zero one two (tl s) ℓ).1, zero s, (corec' σ hd tl zero one two (tl s) ℓ).2.1 (one s), (corec' σ hd tl zero one two (tl s) ℓ).2.2.1 (two s)⟩, id, (corec' σ hd tl zero one two (tl s) ℓ).2.2.2, id⟩

def Baz.corec (σ : Sort u) (hd : σ → Nat) (tl : σ → σ) (zero : ∀ s, Fin (hd s)) (one : ∀ s, Fin (hd (tl s) + 1)) (two : ∀ s, Fin (hd (tl (tl s)) + 2)) (s : σ) : Baz :=
  .mk (corec' σ hd tl zero one two s · |>.1) fun ℓ ℓ' => by
    induction ℓ generalizing s ℓ' with | zero => constructor | succ ℓ ih =>
    cases ℓ' with | zero => constructor | succ ℓ' =>
    refine ⟨rfl, ih (tl s) ℓ', rfl, ?_⟩
    cases ℓ with | zero => constructor | succ ℓ =>
    cases ℓ' with | zero => constructor | succ ℓ' =>
    rfl

theorem Baz.hd_corec hd tl zero one two : (corec σ hd tl zero one two s).hd = hd s :=
  rfl

theorem Baz.tl_corec hd tl zero one two : (corec σ hd tl zero one two s).tl = corec σ hd tl zero one two (tl s) :=
  rfl

theorem Baz.zero_corec hd tl zero one two : (corec σ hd tl zero one two s).zero = zero s :=
  rfl

theorem Baz.one_corec hd tl zero one two : (corec σ hd tl zero one two s).one = one s :=
  rfl

theorem Baz.two_corec hd tl zero one two : (corec σ hd tl zero one two s).two = two s :=
  rfl

theorem iter_comp {f : β → β} {g : α → β} {h : α → α} (eq : ∀ x, f (g x) = g (h x)): iter f (g x) n = g (iter h x n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact (congrArg (iter f · n) (eq x)).trans ih

theorem rec_comp {f : β → β} {g : α → β} {h : α → α} (eq : ∀ x, f (g x) = g (h x)) {n : Nat}: n.rec (g x) (fun _ => f) = g (n.rec x fun _ => h) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact (congrArg f ih).trans (eq _)

def Qux.Approx : Nat → (α : Type) × (α → (Nat → Option Nat) × (Nat → Option Nat))
  | 0 => ⟨Unit, fun _ => (fun _ => none, fun _ => none)⟩
  | ℓ + 1 => ⟨(hd : Nat) × (tl : (Approx ℓ).1) × (∀ n, (((Approx ℓ).2 tl).1 n).elim Unit (Fin <| · + n)) × (∀ n, (((Approx ℓ).2 tl).2 n).elim Unit (Fin <| · + n)), fun s => (fun n => n.casesOn (some s.1) ((Approx ℓ).2 s.2.1).1, fun n => n.casesOn (some s.1) ((Approx ℓ).2 s.2.1).2)⟩

axiom Qux : Type
axiom Qux.hd (self : Qux) : Nat
axiom Qux.tl (self : Qux) : Qux
axiom Qux.val₁ (self : Qux) (n : Nat) : Fin (hd (n.rec self fun _ => tl) + n)
axiom Qux.val₂ (self : Qux) (n : Nat) : Fin (hd (iter tl self n) + n)
axiom Qux.corec (σ : Sort u) (hd : σ → Nat) (tl : σ → σ) (val₁ : ∀ s n, Fin (hd (n.rec s fun _ => tl) + n)) (val₂ : ∀ s n, Fin (hd (iter tl s n) + n)) (s : σ) : Qux
axiom Qux.hd_corec σ hd tl val₁ val₂ s : (corec σ hd tl val₁ val₂ s).hd = hd s
axiom Qux.tl_corec σ hd tl val₁ val₂ s : (corec σ hd tl val₁ val₂ s).tl = corec σ hd tl val₁ val₂ (tl s)
axiom Qux.val₁_corec {σ hd tl val₁ val₂} s : (corec σ hd tl val₁ val₂ s).val₁ n = (val₁ s n).cast (congrArg (· + n) (.trans (.symm (hd_corec σ hd tl val₁ val₂ (n.rec s fun _ => tl))) (congrArg Qux.hd (.symm (rec_comp (tl_corec σ hd tl val₁ val₂))))))
axiom Qux.val₂_corec {σ hd tl val₁ val₂} s : (corec σ hd tl val₁ val₂ s).val₂ n = (val₂ s n).cast (congrArg (· + n) (.trans (.symm (hd_corec σ hd tl val₁ val₂ (iter tl s n))) (congrArg Qux.hd (.symm (iter_comp (tl_corec σ hd tl val₁ val₂))))))

variable {α : Type} {β : α → Type} (γ : ∀ a, β a → α → Type)

def WW.Approx : Nat → (Approx : Type) × ∀ hd, (β hd → Approx) → Type
  | 0 => ⟨Unit, fun _ _ => Unit⟩
  | ℓ + 1 => ⟨(hd : α) × (tl : β hd → (Approx ℓ).1) × (Approx ℓ).2 hd tl, fun hd tl => ∀ b, γ hd b (tl b).1⟩

variable {γ} in
def WW.Agree : (p : (Approx γ ℓ).1 → (Approx γ ℓ').1 → Prop) × ∀ {hd tl tl'}, (∀ b, p (tl b) (tl' b)) → (Approx γ ℓ).2 hd tl → (Approx γ ℓ').2 hd tl' → Prop :=
  match ℓ, ℓ' with
  | 0, _ => ⟨fun _ _ => True, fun _ _ _ => True⟩
  | _ + 1, 0 => ⟨fun _ _ => True, fun _ _ _ => True⟩
  | _ + 1, _ + 1 => ⟨fun a a' => ∃ hhd : a.1 = a'.1, ∃ htl, Agree.2 htl a.2.2 (hhd.symm.rec (motive := fun hd hhd => (Approx γ _).2 hd (fun b => a'.2.1 (hhd ▸ b :))) a'.2.2), fun htl c c' => ∀ b, c b = (htl b).1 ▸ c' b⟩

def WW : Type :=
  { f : ∀ ℓ, (WW.Approx γ ℓ).1 // ∀ ℓ ℓ', WW.Agree.1 (f ℓ) (f ℓ') }

variable {γ}

def WW.hd (self : WW γ) : α :=
  (self.1 1).1

def WW.tl (self : WW γ) (b : β self.hd) : WW γ :=
  ⟨fun ℓ => (self.1 ℓ.succ).2.1 ((self.2 1 ℓ.succ).1 ▸ b), fun ℓ ℓ' => cast (by grind only) ((self.2 ℓ.succ ℓ'.succ).2.1 ((self.2 1 ℓ.succ).1 ▸ b))⟩

def WW.val (self : WW γ) b : γ self.hd b (self.tl b).hd :=
  (self.2 2 1).1.rec (motive := fun hd hhd => γ hd ((self.2 1 2).1.trans hhd ▸ b) _) ((self.1 2).2.2 ((self.2 1 2).1 ▸ b))

def WW.corec' (σ : Type u) (hd : σ → α) (tl : ∀ s, β (hd s) → σ) (val : ∀ s b, γ (hd s) b (hd (tl s b))) : ∀ ℓ, (f : σ → (Approx γ ℓ).1) × ∀ s, (Approx γ ℓ).2 (hd s) fun b => f (tl s b)
  | 0 => ⟨fun _ => (), fun _ => ()⟩
  | ℓ + 1 => ⟨fun s => ⟨hd s, fun b => (corec' σ hd tl val ℓ).1 (tl s b), (corec' σ hd tl val ℓ).2 s⟩, val⟩

def WW.corec (σ : Type u) (hd : σ → α) (tl : ∀ s, β (hd s) → σ) (val : ∀ s b, γ (hd s) b (hd (tl s b))) (s : σ) : WW γ :=
  .mk (fun ℓ => (corec' σ hd tl val ℓ).1 s) fun ℓ ℓ' => by
    induction ℓ generalizing s ℓ' with | zero => constructor | succ ℓ ih =>
    cases ℓ' with | zero => constructor | succ ℓ' =>
    refine ⟨rfl, fun b => ih (tl s b) ℓ', ?_⟩
    cases ℓ with | zero => constructor | succ ℓ =>
    cases ℓ' with | zero => constructor | succ ℓ' =>
    intro
    rfl

theorem WW.hd_corec σ hd tl val s : (@corec α β γ σ hd tl val s).hd = hd s :=
  rfl

theorem WW.tl_corec σ hd tl val s b : (@corec α β γ σ hd tl val s).tl b = corec σ hd tl val (tl s b) :=
  rfl

theorem WW.val_corec σ hd tl val s b : (@corec α β γ σ hd tl val s).val b = val s b :=
  rfl
