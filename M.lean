def Eq.revRec {α : Sort u} {a : α} {motive : ∀ b, a = b → Sort v} {b} h (m : motive b h) : motive a rfl :=
  h.symm.rec (motive := fun a' h' => motive a' (h.trans h')) m

namespace M

variable {α : Type u} (β : (a : α) → Type v)

private def Approx : (ℓ : Nat) → Type (max u v)
  | .zero => PUnit
  | .succ ℓ => Σ a, (b : β a) → Approx ℓ

variable {β}

private def Approx.Agree : ∀ {ℓ ℓ'}, (m : Approx β ℓ) → (m' : Approx β ℓ') → Prop
  | .zero, _, _, _ | .succ _, .zero, _, _ => True
  | .succ _, .succ _, a, a' => ∃ h : a.fst = a'.fst, ∀ b, Approx.Agree (a.snd b) (a'.snd (h ▸ b))

end M

@[irreducible]
def M {α : Type u} (β : (a : α) → Type v) : Type (max u v) :=
  { f : ∀ ℓ, M.Approx β ℓ // ∀ ℓ ℓ', (f ℓ).Agree (f ℓ') }

namespace M

unseal M

variable {α : Type u} {β : (a : α) → Type v}

@[irreducible]
def hd (m : M β) : α :=
  (m.val (.succ .zero)).fst

unseal hd

private theorem hd_eq {m : M β} (h : m.val (.succ ℓ) = ⟨a, t⟩) : hd m = a :=
  (h ▸ (m.property (.succ .zero) ℓ.succ).1 :)

@[irreducible]
def tl (m : M β) (b : β m.hd) : M β where
  val ℓ := (m.val ℓ.succ).snd (hd_eq rfl ▸ b)
  property ℓ ℓ' := by have := (m.property ℓ.succ ℓ'.succ).2 (hd_eq rfl ▸ b); grind only

unseal tl

private theorem tl_eq {m : M β} (h : m.val (.succ ℓ) = ⟨a, t⟩) b : (tl m (hd_eq h ▸ b)).val ℓ = t b := by
  obtain ⟨rfl, ⟨⟩⟩ := Sigma.ext_iff.mp h
  dsimp only [tl]
  grind only

theorem ext {r : (m m' : M β) → Prop} (hd : ∀ {m m'}, (h : r m m') → m.hd = m'.hd) (tl : ∀ {m m'} h b, r (tl m b) (tl m' (hd h ▸ b))) {m m'} (h : r m m') : m = m' := by
  apply Subtype.eq
  funext ℓ
  induction ℓ generalizing m m' with
  | zero => rfl
  | succ ℓ ih =>
    cases h₁ : m.val ℓ.succ
    cases hd_eq h₁
    cases h₂ : m'.val ℓ.succ
    cases (hd h).trans (hd_eq h₂)
    exact congrArg _ <| funext fun b => tl_eq h₁ b ▸ tl_eq h₂ b ▸ ih (tl h b)

variable {C : Sort w} (hd : (c : C) → α) (tl : ∀ c, (b : β (hd c)) → C) (c : C)

@[irreducible]
def corec : M β where
  val ℓ := ℓ.rec (fun _ => ⟨⟩) (fun _ corec c => ⟨hd c, fun b => corec (tl c b)⟩) c
  property ℓ := ℓ.rec (fun _ _ => ⟨⟩) (fun _ corec c ℓ' => ℓ'.casesOn ⟨⟩ fun ℓ' => ⟨rfl, fun b => corec (tl c b) ℓ'⟩) c

unseal corec

@[simp]
theorem hd_corec : (corec hd tl c).hd = hd c := rfl

@[simp]
theorem tl_corec : (corec hd tl c).tl b = corec hd tl (tl c b) := rfl

unif_hint {rhs : α} where hd c ≟ rhs ⊢ (corec hd tl c).hd ≟ rhs
unif_hint {b : β (corec hd tl c).hd} {rhs : M β} where corec hd tl (tl c b) ≟ rhs ⊢ (corec hd tl c).tl b ≟ rhs
unif_hint {b : β (hd c)} {rhs : M β} where corec hd tl (tl c b) ≟ rhs ⊢ (corec hd tl c).tl b ≟ rhs

variable (hd : α) (tl : (b : β hd) → M β)

@[irreducible]
def mk : M β where
  val ℓ := ℓ.casesOn ⟨⟩ fun ℓ => ⟨hd, fun b => (tl b).val ℓ⟩
  property ℓ ℓ' := ℓ.casesOn ⟨⟩ fun ℓ => ℓ'.casesOn ⟨⟩ fun ℓ' => ⟨rfl, fun b => (tl b).property ℓ ℓ'⟩

unseal mk

@[simp]
theorem hd_mk : (mk hd tl).hd = hd := rfl

@[simp]
theorem tl_mk : (mk hd tl).tl = tl := rfl

unif_hint {rhs : α} where hd ≟ rhs ⊢ (mk hd tl).hd ≟ rhs
unif_hint {rhs : (b : β hd) → M β} where tl ≟ rhs ⊢ (mk hd tl).tl ≟ rhs
unif_hint {b : β hd} {rhs : M β} where tl b ≟ rhs ⊢ (mk hd tl).tl b ≟ rhs
unif_hint {b : β (mk hd tl).hd} {rhs : M β} where tl b ≟ rhs ⊢ (mk hd tl).tl b ≟ rhs

end M

namespace IM

variable {ι : Type u} {α : (i : ι) → Type v} {β : ∀ i, (a : α i) → Type w} (s : ∀ i a, (b : β i a) → ι)

private def Approx (i : ι) : (ℓ : Nat) → Type (max u v w)
  | .zero => PUnit
  | .succ ℓ => Σ a, ∀ b, Approx (s i a b) ℓ

variable {s}

private def Approx.Agree : ∀ {ℓ ℓ'}, (m : Approx s i ℓ) → (m' : Approx s i ℓ') → Prop
  | .zero, _, _, _ | .succ _, .zero, _, _ => True
  | .succ _, .succ ℓ', a, a' => ∃ h : a.fst = a'.fst, ∀ b, Approx.Agree (a.snd b) (h.revRec (motive := fun a h => Approx s (s i a (h ▸ b)) ℓ') (a'.snd (h ▸ b)))

end IM

@[irreducible]
def IM {ι : Type u} {α : (i : ι) → Type v} {β : ∀ i, (a : α i) → Type w} (s : ∀ i a, (b : β i a) → ι) (i : ι) : Type (max u v w) :=
  { f : ∀ ℓ, IM.Approx s i ℓ // ∀ ℓ ℓ', (f ℓ).Agree (f ℓ') }

namespace IM

unseal IM

variable {ι : Type u} {α : (i : ι) → Type v} {β : ∀ i, (a : α i) → Type w} {s : ∀ i a, (b : β i a) → ι}

@[irreducible]
def hd (m : IM s i) : α i :=
  (m.val (.succ .zero)).fst

unseal hd

private theorem hd_eq {m : IM s i} (h : m.val (.succ ℓ) = ⟨a, t⟩) : hd m = a :=
  (h ▸ (m.property (.succ .zero) ℓ.succ).1 :)

@[irreducible]
def tl (m : IM s i) (b : β i m.hd) : IM s (s i m.hd b) where
  val ℓ := (hd_eq rfl).revRec (motive := fun a h => Approx s (s i a (h ▸ b)) ℓ) ((m.val ℓ.succ).snd (hd_eq rfl ▸ b))
  property ℓ ℓ' := by have := (m.property ℓ.succ ℓ'.succ).2 (hd_eq rfl ▸ b); grind only [Eq.revRec]

unseal tl

private theorem tl_eq {m : IM s i} (h : m.val (.succ ℓ) = ⟨a, t⟩) b : ((hd_eq h).symm.revRec (motive := fun a h => IM s (s i a (h ▸ b))) (tl m (hd_eq h ▸ b))).val ℓ = t b := by
  have : (congrArg Sigma.fst h).symm.revRec (motive := fun a h => Approx s (s i a (h ▸ b)) ℓ) ((m.val ℓ.succ).snd (congrArg Sigma.fst h ▸ b)) = t b := by
    obtain ⟨rfl, ⟨⟩⟩ := Sigma.ext_iff.mp h
    rfl
  cases hd_eq h
  exact this

theorem ext {r : ∀ i, (m m' : IM s i) → Prop} (hd : ∀ {i m m'}, (h : r i m m') → m.hd = m'.hd) (tl : ∀ {i m m'} (h : r i m m') b, r (s i m.hd b) (tl m b) ((hd h).revRec (motive := fun a h => IM s (s i a (h ▸ b))) (tl m' (hd h ▸ b)))) {i m m'} (h : r i m m') : m = m' := by
  apply Subtype.eq
  funext ℓ
  induction ℓ generalizing i with
  | zero => rfl
  | succ ℓ ih =>
    cases h₁ : m.val ℓ.succ
    cases hd_eq h₁
    cases h₂ : m'.val ℓ.succ
    cases (hd h).trans (hd_eq h₂)
    exact congrArg _ <| funext fun b => tl_eq h₁ b ▸ tl_eq h₂ b ▸ ih (tl h b)

variable {C : (i : ι) → Sort x} (hd : ∀ {i}, (c : C i) → α i) (tl : ∀ {i} c, (b : β i (hd c)) → C (s i (hd c) b)) {i} (c : C i)

@[irreducible]
def corec : IM s i where
  val ℓ := ℓ.rec (fun _ _ => ⟨⟩) (fun _ corec i c => ⟨hd c, fun b => corec (s i (hd c) b) (tl c b)⟩) i c
  property ℓ := ℓ.rec (fun _ _ _ => ⟨⟩) (fun _ corec i c ℓ' => ℓ'.casesOn ⟨⟩ fun ℓ' => ⟨rfl, fun b => corec (s i (hd c) b) (tl c b) ℓ'⟩) i c

unseal corec

@[simp]
theorem hd_corec : (corec @hd @tl c).hd = hd c := rfl

@[simp]
theorem tl_corec : (corec @hd @tl c).tl b = corec @hd @tl (tl c b) := rfl

unif_hint {rhs : α i} where hd c ≟ rhs ⊢ (corec @hd @tl c).hd ≟ rhs
unif_hint {b : β i (corec @hd @tl c).hd} {rhs : IM s (s i (corec @hd @tl c).hd b)} where corec @hd @tl (tl c b) ≟ rhs ⊢ (corec @hd @tl c).tl b ≟ rhs
unif_hint {b : β i (corec @hd @tl c).hd} {rhs : IM s (s i (hd c) b)} where corec @hd @tl (tl c b) ≟ rhs ⊢ (corec @hd @tl c).tl b ≟ rhs
unif_hint {b : β i (hd c)} {rhs : IM s (s i (corec @hd @tl c).hd b)} where corec @hd @tl (tl c b) ≟ rhs ⊢ (corec @hd @tl c).tl b ≟ rhs
unif_hint {b : β i (hd c)} {rhs : IM s (s i (hd c) b)} where corec @hd @tl (tl c b) ≟ rhs ⊢ (corec @hd @tl c).tl b ≟ rhs

variable (hd : α i) (tl : (b : β i hd) → IM s (s i hd b))

@[irreducible]
def mk : IM s i where
  val ℓ := ℓ.casesOn ⟨⟩ fun ℓ => ⟨hd, fun b => (tl b).val ℓ⟩
  property ℓ ℓ' := ℓ.casesOn ⟨⟩ fun ℓ => ℓ'.casesOn ⟨⟩ fun ℓ' => ⟨rfl, fun b => (tl b).property ℓ ℓ'⟩

unseal mk

@[simp]
theorem hd_mk : (mk hd tl).hd = hd := rfl

@[simp]
theorem tl_mk : (mk hd tl).tl = tl := rfl

unif_hint {rhs : α i} where hd ≟ rhs ⊢ (mk hd tl).hd ≟ rhs
unif_hint {rhs : (b : β i hd) → IM s (s i hd b)} where tl ≟ rhs ⊢ (mk hd tl).tl ≟ rhs
unif_hint {b : β i hd} {rhs : IM s (s i hd b)} where tl b ≟ rhs ⊢ (mk hd tl).tl b ≟ rhs
unif_hint {b : β i (mk hd tl).hd} {rhs : IM s (s i hd b)} where tl b ≟ rhs ⊢ (mk hd tl).tl b ≟ rhs

end IM
