namespace M

variable {α : Type u} (β : (a : α) → Type v)

private inductive Approx : (ℓ : Nat) → Type (max u v)
  | hole : Approx .zero
  | node a (t : (b : β a) → Approx ℓ) : Approx ℓ.succ

variable {β}

private inductive Approx.Agree : (m : Approx β ℓ) → (m' : Approx β ℓ') → Prop
  | hole {m' : Approx β ℓ'} : Agree hole m'
  | node a {t : (b : β a) → Approx β ℓ} {t' : (b : β a) → Approx β ℓ'} (h : ∀ b, Agree (t b) (t' b)) : Agree (node a t) (node a t')

private theorem Approx.Agree.refl : {m : Approx β ℓ} → Agree m m
  | .hole => hole
  | .node a _ => .node a fun _ => refl

private theorem Approx.Agree.trans {m : Approx β ℓ} {m' : Approx β ℓ'} {m'' : Approx β ℓ''} : (h : Agree m m') → (h' : Agree m' m'') → Agree m m''
  | hole, _ => hole
  | node a h, node _ h' => node a fun b => trans (h b) (h' b)

end M

@[irreducible]
def M {α : Type u} (β : (a : α) → Type v) : Type (max u v) :=
  { f : ∀ ℓ, M.Approx β ℓ // ∀ ℓ, (f ℓ).Agree (f ℓ.succ) }

namespace M

unseal M

variable {α : Type u} {β : (a : α) → Type v}

private theorem property (m : M β) {ℓ ℓ'} : (h : ℓ ≤ ℓ') → (m.val ℓ).Agree (m.val ℓ')
  | .refl => .refl
  | .step h => (m.property h).trans (m.2 _)

@[irreducible]
def hd (m : M β) : α :=
  let .node a _ := m.val (.succ .zero)
  a

unseal hd

private theorem hd_eq {m : M β} (h : m.val (.succ ℓ) = .node a t) : hd m = a := by
  dsimp only [hd]
  split
  next h' =>
  cases h ▸ h' ▸ m.property (Nat.succ_le_succ ℓ.zero_le)
  rfl

@[irreducible]
def tl (m : M β) (b : β m.hd) : M β where
  val ℓ := match h : m.val ℓ.succ with | .node _ t => t (hd_eq h ▸ b)
  property ℓ := by dsimp only; split; split; next h _ _ h' => cases h ▸ h' ▸ m.2 ℓ.succ with | node _ h => apply h

unseal tl

private theorem tl_eq {m : M β} {t} (h : m.val (.succ ℓ) = .node a t) b : (tl m (hd_eq h ▸ b)).val ℓ = t b := by
  cases hd_eq h
  dsimp only [tl]
  split
  next h' =>
  cases h ▸ h'
  rfl

theorem ext {r : (m m' : M β) → Prop} (hd : ∀ {m m'}, (h : r m m') → m.hd = m'.hd) (tl : ∀ {m m'} h b, r (tl m b) (tl m' (hd h ▸ b))) {m m'} (h : r m m') : m = m' := by
  apply Subtype.eq
  funext ℓ
  induction ℓ using Nat.rec generalizing m m' with
  | zero =>
    cases m.val .zero
    cases m'.val .zero
    rfl
  | succ ℓ ih =>
    cases h₁ : m.val ℓ.succ
    cases hd_eq h₁
    cases h₂ : m'.val ℓ.succ
    cases hd_eq h₂ ▸ hd h
    exact congrArg _ <| funext fun b => tl_eq h₁ b ▸ tl_eq h₂ b ▸ ih (tl h b)

variable {C : Sort w} (hd : (c : C) → α) (tl : ∀ c, (b : β (hd c)) → C)

@[irreducible]
def gen (c : C) : M β where
  val      ℓ := ℓ.rec (fun _ => .hole) (fun _ gen c => .node (hd c) fun b => gen (tl c b)) c
  property ℓ := ℓ.rec (fun _ => .hole) (fun _ gen c => .node (hd c) fun b => gen (tl c b)) c

unseal gen

variable {hd tl}

@[simp]
theorem hd_gen : (gen hd tl c).hd = hd c := rfl

@[simp]
theorem tl_gen : (gen hd tl c).tl b = gen hd tl (tl c b) := rfl

end M

namespace IM

variable {ι : Type u} {α : (i : ι) → Type v} {β : ∀ i, (a : α i) → Type w} (s : ∀ i a, (b : β i a) → ι)

private inductive Approx : (i : ι) → (ℓ : Nat) → Type (max u v w)
  | hole : Approx i .zero
  | node a (t : ∀ b, Approx (s i a b) ℓ) : Approx i ℓ.succ

variable {s}

private inductive Approx.Agree : (m : Approx s i ℓ) → (m' : Approx s i ℓ') → Prop
  | hole {m' : Approx s i ℓ'} : Agree hole m'
  | node a {t : ∀ b, Approx s (s i a b) ℓ} {t' : ∀ b, Approx s (s i a b) ℓ'} (h : ∀ b, Agree (t b) (t' b)) : Agree (node a t) (node a t')

private theorem Approx.Agree.refl : {m : Approx s i ℓ} → Agree m m
  | .hole => hole
  | .node a _ => .node a fun _ => refl

private theorem Approx.Agree.trans {m : Approx s i ℓ} {m' : Approx s i ℓ'} {m'' : Approx s i ℓ''} : (h : Agree m m') → (h' : Agree m' m'') → Agree m m''
  | hole, _ => hole
  | node a h, node _ h' => node a fun b => trans (h b) (h' b)

end IM

@[irreducible]
def IM {ι : Type u} {α : (i : ι) → Type v} {β : ∀ i, (a : α i) → Type w} (s : ∀ i a, (b : β i a) → ι) (i : ι) : Type (max u v w) :=
  { f : ∀ ℓ, IM.Approx s i ℓ // ∀ ℓ, (f ℓ).Agree (f ℓ.succ) }

namespace IM

unseal IM

variable {ι : Type u} {α : (i : ι) → Type v} {β : ∀ i, (a : α i) → Type w} {s : ∀ i a, (b : β i a) → ι}

private theorem property (m : IM s i) {ℓ ℓ'} : (h : ℓ ≤ ℓ') → (m.val ℓ).Agree (m.val ℓ')
  | .refl => .refl
  | .step h => (m.property h).trans (m.2 _)

@[irreducible]
def hd (m : IM s i) : α i :=
  let .node a _ := m.val (.succ .zero)
  a

unseal hd

private theorem hd_eq {m : IM s i} (h : m.val (.succ ℓ) = .node a t) : hd m = a := by
  dsimp only [hd]
  split
  next h' =>
  cases h ▸ h' ▸ m.property (Nat.succ_le_succ ℓ.zero_le)
  rfl

@[irreducible]
def tl (m : IM s i) (b : β i m.hd) : IM s (s i m.hd b) where
  val ℓ := match h : m.val ℓ.succ with | .node _ t => by cases hd_eq h; exact t b --cast_tl t (hd_eq h).symm b
  property ℓ := by dsimp only; split; split; next h _ _ h' => cases hd_eq h; cases h ▸ h' ▸ m.2 ℓ.succ with | node _ h => apply h

def tl' (m : IM s i) (h : a = m.hd) : (b : β i a) → IM s (s i a b) := by
  cases h
  exact m.tl

unseal tl

private theorem tl_eq {m : IM s i} {t} (h : m.val (.succ ℓ) = .node m.hd t) b : (tl m b).val ℓ = t b := by
  dsimp only [tl]
  split
  next h' =>
  cases h ▸ h'
  rfl

private theorem tl'_eq {m : IM s i} {t} (h : m.val (.succ ℓ) = .node a t) b : (tl' m (hd_eq h).symm b).val ℓ = t b := by
  cases hd_eq h
  exact tl_eq h b

theorem ext {r : ∀ i, (m m' : IM s i) → Prop} (hd : ∀ {i m m'}, (h : r i m m') → m.hd = m'.hd) (tl : ∀ {i m m'} (h : r i m m') b, r (s i m.hd b) (tl m b) (tl' m' (hd h) b)) {i m m'} (h : r i m m') : m = m' := by
  apply Subtype.eq
  funext ℓ
  induction ℓ using Nat.rec generalizing i with
  | zero =>
    cases m.val .zero
    cases m'.val .zero
    rfl
  | succ ℓ ih =>
    cases h₁ : m.val ℓ.succ
    cases hd_eq h₁
    cases h₂ : m'.val ℓ.succ
    cases hd_eq h₂ ▸ hd h
    exact congrArg _ <| funext fun b => tl_eq h₁ b ▸ tl'_eq h₂ b ▸ ih (tl h b)

variable {C : (i : ι) → Sort x} (hd : ∀ {i}, (c : C i) → α i) (tl : ∀ {i} c, (b : β i (hd c)) → C (s i (hd c) b))

@[irreducible]
def gen (c : C i) : IM s i where
  val      ℓ := ℓ.rec (fun _ _ => .hole) (fun _ gen i c => .node (hd c) fun b => gen (s i (hd c) b) (tl c b)) i c
  property ℓ := ℓ.rec (fun _ _ => .hole) (fun _ gen i c => .node (hd c) fun b => gen (s i (hd c) b) (tl c b)) i c

unseal gen

variable {hd tl}

@[simp]
theorem hd_gen {c : C i} : (gen @hd @tl c).hd = hd c := rfl

@[simp]
theorem tl_gen {c : C i} {b} : (gen @hd @tl c).tl b = gen @hd @tl (tl c b) := rfl

end IM
