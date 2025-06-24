-- F(t) = ν(s. t + s)
def F (t : Type) : Type :=
  { f : Nat → Option t // ∀ n x, f n = some x → f n.succ = x }

def F.unfold (x : F t) : t ⊕ F t :=
  match x.val .zero with
  | some x => .inl x
  | none => .inr ⟨(x.val ·.succ), (x.property ·.succ)⟩

def F.corec (f : α → t ⊕ α) (a : α) : F t where
  val n := Sum.elim some (fun _ => none) <| n.rec (f a) (fun _ => .elim .inl f)
  property n x h := by
    dsimp only at h ⊢
    generalize Nat.rec .. = s at h
    cases s <;> cases h
    rfl

theorem F.unfold_corec : unfold (corec f a) = (f a).map id (corec f) := by
  generalize h : f a = x
  simp only [corec, unfold, h]
  cases x
  . rfl
  . apply congrArg Sum.inr
    apply Subtype.eq
    funext n
    dsimp only [corec]
    congr
    induction n with congr

def F.map (f : t₁ → t₂) (x : F t₁) : F t₂ where
  val n := (x.val n).map f
  property n := by simp; exact fun a h => ⟨a, x.property n a h, rfl⟩

def F.ofNat (n : Nat) (x : t) : F t :=
  ⟨fun a => if n ≤ a then x else none, by simp; omega⟩

def F.infty : F t :=
  ⟨fun _ => none, nofun⟩

theorem F.infty_ne_ofNat : infty ≠ ofNat n x := by
  intro h
  have := congrArg (·.val n) h
  simp [infty, ofNat] at this

theorem F.ofNat_inj (h : ofNat n x = ofNat m y) : n = m ∧ x = y := by
  have := congrArg (·.val n) h
  simp [ofNat] at this
  refine ⟨?_, this.right⟩
  have := congrArg (·.val m) h
  simp [ofNat] at this
  omega

theorem Nat.le_rec' {m : Nat} {motive : ∀ n, n ≤ m → Prop} (refl : motive m .refl) (step : ∀ {n} h, motive n.succ h → motive n (Nat.le_of_succ_le h)) {n} h : motive n h := by
  generalize hk : m - n = k
  cases (by omega : m = n + k)
  clear hk
  cases show h = n.le_add_right k from rfl
  induction k with
  | zero => exact refl
  | succ k ih =>
    apply step (by simp)
    apply @ih (fun n' h' => motive n'.succ (Nat.succ_le_succ h')) refl
    intro n' h ih
    apply step _ ih

theorem F.val_none_mono {x : F t} (h : n₁ ≤ n₂) (h' : x.val n₂ = none) : x.val n₁ = none := by
  induction h with
  | refl => exact h'
  | @step m _ ih =>
    cases h : x.val m with
    | none => exact ih h
    | some => cases h'.symm.trans (x.property _ _ h)

theorem F.val_some_mono {x : F t} (h : n₁ ≤ n₂) (h' : x.val n₁ = some y) : x.val n₂ = some y := by
  induction h using Nat.le_rec' with
  | refl => exact h'
  | step _ ih => exact ih (x.property _ _ h')

def F.eq_ofNat_of_some (h : x.val n = some y) : { m // x = ofNat m y } :=
  let ⟨m, h, h'⟩ := go n h
  ⟨m, Subtype.eq <| funext fun n => by dsimp [ofNat]; split; exact val_some_mono ‹_› h; exact h' n (Nat.lt_of_not_le ‹_›)⟩
where
  go : ∀ n, x.val n = some y → { m // x.val m = some y ∧ ∀ k < m, x.val k = none }
  | .zero, h => ⟨_, h, nofun⟩
  | .succ n, h =>
    match h' : x.val n with
    | none => ⟨_, h, fun k hk => val_none_mono (Nat.le_of_lt_succ hk) h'⟩
    | some z => go n (h'.trans ((x.property n z h').symm.trans h))

theorem F.eq_ofNat_of_some_ofNat (h : n ≤ m) : eq_ofNat_of_some (x := ofNat n y) (y := y) (by simp [ofNat]; exact h) = ⟨n, rfl⟩ := by
  generalize eq_ofNat_of_some _ = h'
  rcases h' with ⟨k, hk⟩
  simp [ofNat_inj hk]

def F.mk : Option (Nat × t) → F t
  | none => infty
  | some (n, x) => ofNat n x

theorem F.cover : ¬∀ x, mk x ≠ y := by
  intro h
  have h₁ := h none
  have h₂ n x := h (some (n, x))
  clear h
  dsimp! at h₁ h₂
  apply h₁
  clear h₁
  apply Subtype.eq
  funext n
  cases h : y.val n with
  | none => rfl
  | some x =>
    have ⟨_, h⟩ := eq_ofNat_of_some h
    cases h₂ _ _ h.symm

structure Iso (α : Sort u) (β : Sort v) where
  f : α → β
  g : β → α
  g_f : ∀ x, g (f x) = x
  f_g : ∀ y, f (g y) = y

theorem Sigma.ext_iff' {x y : @Sigma α β} : x = y ↔ ∃ h : x.fst = y.fst, x.snd = h ▸ y.snd :=
  ⟨by intro h; cases h; exact ⟨rfl, rfl⟩, by intro ⟨h, h'⟩; cases y; cases h; cases h'; rfl⟩

theorem Eq.rec_pi₁ {C : α → γ → Sort u} {refl} : @Eq.rec α x (fun y _ => ∀ z, C y z) refl y h = fun z => @Eq.rec α x (fun y _ => C y z) (refl z) y h :=
  by cases h; rfl

theorem Eq.rec_pi₂ {C : α → Sort u} {refl} : @Eq.rec α x (fun y _ => C y → β) refl y h = fun z => refl (h ▸ z) :=
  by cases h; rfl

def F.poly : Iso (F t) ((x : F Unit) × (∀ n, x = .ofNat n () → t)) where
  f x := ⟨x.map fun _ => (), fun n h => match h' : x.val n with | some x => x | none => by have := congrArg (·.val n) h; simp [map, ofNat, h'] at this⟩
  g := fun ⟨x, y⟩ => Subtype.mk (fun n => match h : x.val n with | none => none | some () => some (let ⟨m, h⟩ := F.eq_ofNat_of_some h; y m h)) <| by
    intro n a
    dsimp
    split <;> simp
    rename_i h
    have ⟨m, h⟩ := eq_ofNat_of_some h
    cases h
    intro h'
    cases h'
    simp [ofNat] at h
    split
    next h' => simp [ofNat] at h'; omega
    simp [eq_ofNat_of_some_ofNat h.step]
  g_f x := Subtype.eq <| by
    funext n
    dsimp
    split
    next h => simp [map] at h; exact h.symm
    next h =>
      generalize eq_ofNat_of_some _ = m
      rcases m with ⟨m, hm⟩
      split
      next h' =>
        rewrite [hm] at h
        simp [ofNat] at h
        exact (val_some_mono h h').symm
      next h' =>
        have := congrArg (·.val m) hm
        simp [map, h', ofNat] at this
  f_g := by
    intro ⟨x, y⟩
    dsimp
    simp only [Sigma.ext_iff']
    refine ⟨?_, ?_⟩
    . apply Subtype.eq
      funext n
      dsimp [map]
      split <;> simp [*]
    . funext n h
      split
      next h' =>
        split at h'
        . nomatch h'
        next h'' =>
          cases h'
          generalize eq_ofNat_of_some _ = m
          rcases m with ⟨m, hm⟩
          cases hm
          simp [ofNat] at h''
          replace h := congrArg (·.val m) h
          dsimp [map, ofNat] at h
          split at h
          next h' => simp at h'
          simp at h
          cases Nat.le_antisymm h h''
          rename_i h'
          clear h'' h h'
          dsimp
          rewrite [Eq.rec_pi₁ (C := fun x n => x = ofNat n () → t)]
          dsimp
          rw [Eq.rec_pi₂ (C := fun x => x = ofNat n ())]
      next h' =>
        exfalso
        split at h'
        next h'' =>
          have := congrArg (·.val n) h
          simp [ofNat, map] at this
          rcases this with ⟨_, this⟩
          split at this
          . contradiction
          cases this
          rename_i h
          cases h.symm.trans h''
        . cases h'

theorem F.poly.map_f : poly.f (map f x) = ⟨(poly.f x).fst, fun n h => f ((poly.f x).snd n h)⟩ := by
  simp [poly, Sigma.ext_iff', map]
  funext n h
  let y := x.val n
  cases h' : y with (dsimp [y] at h'; clear y)
  | none =>
    have := congrArg (·.val n) h
    simp [ofNat, h'] at this
  | some z =>
    split <;> rename_i h'' <;> simp [h'] at h''
    cases h''
    rewrite [Eq.rec_pi₁ (C := fun x n => x = ofNat n () → _)]
    dsimp
    rewrite [Eq.rec_pi₂ (C := fun x => x = ofNat n ())]
    split <;> rename_i h <;> cases h'.symm.trans h
    rfl

-- μ(t. ν(s. t + s))
inductive P
  | node (x : F Unit) (y : ∀ n, x = .ofNat n () → P)

theorem P.node.injIff : node x₁ y₁ = node x₂ y₂ ↔ ∃ h : x₁ = x₂, y₁ = h ▸ y₂ := by
  simp
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, by cases h₁; exact eq_of_heq h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, by cases h₁; exact heq_of_eq h₂⟩⟩

def P.fold (x : F P) : P :=
  let ⟨x, y⟩ := F.poly.f x
  node x y

def P.rec' (f : F α → α) : P → α
  | node x y => f (F.poly.g ⟨x, fun n h => rec' f (y n h)⟩)

theorem P.rec'_fold : rec' f (fold x) = f (F.map (rec' f) x) :=
  by simp [fold, rec', ← F.poly.map_f, F.poly.g_f]

def P.mk : List Nat → P
  | [] => .node .infty fun _ h => (F.infty_ne_ofNat h).elim
  | n :: ns => .node (.ofNat n ()) fun _ _ => mk ns

theorem HEq.eqRec_left : HEq (@Eq.rec α x motive lhs y h) rhs ↔ HEq lhs rhs :=
  by cases h; rfl

theorem P.cover : ¬∀ x, mk x ≠ y := by
  intro h
  induction y with
  | node x y ih =>
    apply h []
    simp [mk]
    refine ⟨?x, ?y⟩
    case y =>
      have := ?x
      have : HEq (?x ▸ y : ∀ n, F.infty = .ofNat n () → P) y := by simp [HEq.eqRec_left]
      refine .trans ?_ this
      simp
      funext x h
      cases F.infty_ne_ofNat h
    apply Subtype.eq
    funext n
    dsimp [F.infty]
    symm
    cases hx : x.val n with
    | none => rfl
    | some u =>
      cases u
      simp
      have ⟨m, h⟩ := F.eq_ofNat_of_some hx
      cases h
      clear hx n
      apply ih m rfl
      intro x h'
      apply h (m :: x)
      simp [mk]
      funext m' hm
      cases (F.ofNat_inj hm).left
      exact h'

-- μ(t. t + s)
inductive G (s : Type) : Type
  | here (x : s)
  | there (x : G s)

def G.fold : G s ⊕ s → G s
  | .inl x => there x
  | .inr x => here x

def G.rec' (f : α ⊕ s → α) : G s → α
  | here x => f (.inr x)
  | there x => f (.inl (rec' f x))

def G.get : G s → s
  | here x => x
  | there x => x.get

def G.len : G s → Nat
  | here _ => .zero
  | there x => x.len.succ

def G.mk (x : s) : Nat → G s
  | .zero => here x
  | .succ n => there (mk x n)

def G.map (f : s₁ → s₂) (x : G s₁) : G s₂ :=
  .mk (f x.get) x.len

def G.def : Iso (G s) (Nat × s) where
  f := fun x => ⟨x.len, x.get⟩
  g := fun (n, s) => mk s n
  g_f x := by induction x with dsimp! only at * <;> congr
  f_g := by intro (n, x); simp; induction n using Nat.rec with simp! <;> assumption

-- ν(s. μ(t. t + s))
def Q : Type :=
  Nat → Nat

def Q.unfold (x : Q) : G Q :=
  .mk (x ·.succ) (x .zero)

def Q.corec (f : α → G α) (a : α) : Q :=
  fun n => (f (n.rec a fun _ a => (f a).get)).len

theorem Q.unfold_corec : unfold (corec f a) = (f a).map (corec f) := by
  dsimp only [unfold, G.map]
  congr
  funext n
  dsimp only [corec]
  congr
  induction n with congr

def Nat.pair (x y : Nat) : Nat :=
  2 ^ x * (2 * y + 1) - 1

def Nat.unpair (z : Nat) : Nat × Nat :=
  let (x, m) := go (z + 1) z.zero_lt_succ
  (x, (m - 1) / 2)
where
  go (n : Nat) (hn : n > 0) : Nat × Nat :=
    if h : 2 ∣ n then
      let (k, m) := go (n / 2) (Nat.lt_div_iff_mul_lt' h _ |>.mpr hn)
      (k + 1, m)
    else
      (0, n)

@[simp]
def Nat.fst (z : Nat) : Nat := (unpair z).fst
@[simp]
def Nat.snd (z : Nat) : Nat := (unpair z).snd

@[simp]
theorem Nat.snd_lt_succ : (unpair n).snd < n.succ := by
  apply lt_succ_of_le
  simp [unpair]
  simp [div_le_iff_le_mul]
  suffices ∀ n hn, (unpair.go n hn).snd ≤ n * 2 by
    specialize this (n + 1) n.zero_lt_succ
    simp [Nat.add_mul] at this
    exact this
  clear n
  intro n hn
  fun_induction unpair.go n hn
  next hkm ih =>
    apply Nat.le_trans (hkm ▸ ih)
    omega
  . omega

@[simp]
theorem Nat.unpair_pair : unpair (pair x y) = (x, y) := by
  simp [pair, unpair]
  induction x with
  | zero =>
    unfold unpair.go
    have : ¬2 ∣ 2 * y + 1 := by omega
    simp [this]
  | succ x hx =>
    unfold unpair.go
    simp [Nat.pow_add_one]
    have : 2 ^ x * 2 * (2 * y + 1) - 1 + 1 = 2 ^ x * 2 * (2 * y + 1) := by
      apply Nat.sub_add_cancel
      simp [mul_add_one]
      refine Nat.le_trans ?_ (le_add_left ..)
      refine Nat.le_trans ?_ (le_add_left ..)
      apply Nat.pow_pos
      simp
    simp [this]
    have : 2 ^ x * (2 * y + 1) - 1 + 1 = 2 ^ x * (2 * y + 1) := by
      apply Nat.sub_add_cancel
      simp [mul_add_one]
      refine Nat.le_trans ?_ (le_add_left ..)
      apply Nat.pow_pos
      simp
    simp [this] at hx
    have : 2 ∣ 2 ^ x * 2 * (2 * y + 1) :=
      ⟨2 ^ x * (2 * y + 1), by rw [Nat.mul_comm _ 2, Nat.mul_assoc]⟩
    simp [this]
    have : 2 ^ x * 2 * (2 * y + 1) / 2 = 2 ^ x * (2 * y + 1) := by
      rewrite [Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc]
      simp
    simp [this]
    exact hx

def encode : List Nat → Nat
  | [] => 0
  | x :: xs => x.pair (encode xs) + 1

def decode : Nat → List Nat
  | 0 => []
  | n + 1 =>
    n.fst :: decode n.snd

theorem decode_encode : decode (encode xs) = xs := by
  induction xs with
  | nil => simp [encode, decode]
  | cons => simp [encode, decode]; assumption

theorem distinct : Iso P Q → False := by
  intro h
  replace ⟨f, h⟩ : ∃ f : List Nat → Q, ∀ y, ¬∀ x, f x ≠ y := ⟨h.f ∘ P.mk, fun y h' => P.cover fun x h'' => h' x (.trans (congrArg h.f h'') (h.f_g y))⟩
  apply h fun n => f (decode n) n + 1
  intro xs h
  exact Nat.succ_ne_self _ ((congrFun h (encode xs)).trans (congrArg (f · _ + 1) decode_encode)).symm

def Q.fold : Q ⊕ Q → Q :=
  Q.corec (G.rec' (G.fold ∘ .map id Q.unfold)) ∘ G.fold ∘ .map Q.unfold id
-- inl (x :: xs) ↦ (x + 1) :: xs
-- inr xs ↦ 0 :: xs

def Q.unfold' : Q → Q ⊕ Q :=
  .map (Q.corec (G.rec' (G.fold ∘ .map id Q.unfold))) id ∘ G.rec' (.map G.fold id) ∘ Q.unfold
-- 0 :: xs ↦ inr xs
-- (x + 1) :: xs ↦ inl (x :: xs)

def P.unfold : P → P ⊕ P :=
  .map id P.fold ∘ F.unfold ∘ P.rec' (F.corec (.map P.fold id ∘ F.unfold))
-- [] ↦ inr []
-- (x + 1) :: xs ↦ inr (x :: xs)
-- 0 :: xs ↦ inl xs

def P.fold' : P ⊕ P → P :=
  P.fold ∘ F.corec (.map id F.unfold) ∘ .map id (P.rec' (F.corec (.map P.fold id ∘ F.unfold)))
-- inl xs ↦ 0 :: xs
-- inr [] ↦ []
-- inr (x :: xs) ↦ (x + 1) :: xs

def canonical : P → Q :=
  Q.corec (P.rec' (G.fold ∘ .map id (P.fold ∘ F.corec (.map (G.rec' P.fold') id ∘ F.unfold)) ∘ F.unfold))

-- F (G P) → G P
-- 1 + ℕ × (ℕ × P) → ℕ × P
-- { ∞ ↦ inr ∞ ; (0, x) ↦ inl x ; (n + 1, x) ↦ inr (n, x) } → { inl x ↦ inl x ; inr ↦ inr (F (G P) → P) } → { inl (n, x) ↦ (n + 1, x) ; inr x ↦ (0, x) }

def canonical' : P → Q :=
  P.rec' (Q.corec (G.fold ∘ .map (G.rec' (G.fold ∘ .map id (F.corec Q.unfold')) ∘ Q.unfold) id ∘ F.unfold))

-- F Q → G (F Q)
-- 1 + ℕ × Q → ℕ × (1 + ℕ × Q)
-- { ∞ ↦ inr ∞ ; (0, x) ↦ inl x ; (n + 1, x) ↦ inr (n, x) } → { inl ↦ inl ({ (x :: xs) → (x, xs) } → { (x, y) ↦ (x, Q → F Q) }) ; inr x ↦ inr x } → { inl (n, x) ↦ (n + 1, x) ; inr x ↦ (0, x) }

-- ∞ ↦ (0, ∞)
-- (n + 1, x) ↦ (0, (n, x))
-- (0, x :: xs) ↦ (x + 1, foo xs)

-- foo (0 :: xs) = now xs
-- foo ((x + 1) :: xs) = later (foo (x :: xs))

def p (x : Q) : String :=
  s!"[{x 0}, {x 1}, {x 2}, {x 3}, {x 4}, {x 5}, …]"

#eval p <| canonical (.mk [1, 2, 0])
#eval p <| canonical' (.mk [1, 2, 0])

/-
infinite stream of Ls and Rs such that
μ(t. ν(s. t + s)) - finitely many Ls
ν(t. μ(s. t + s)) - finitely many Rs in between Ls. can be encoded as n ↦ # of Rs after the nth L
-/

def P' : Type :=
  { f : Nat → Bool // WellFounded fun n m => m < n ∧ f n }

def P'.fold (x : F P') : P' where
  val n :=
    match h : x.val n with
    | none => false
    | some y =>
      let ⟨m, hm⟩ := F.eq_ofNat_of_some h
      n = m || y.val (n - m.succ)
  property := by
    dsimp only
    constructor
    intro n
    constructor
    intro y ⟨hy, h⟩
    split at h
    . cases h
    rename_i x h'
    let ⟨m, hm⟩ := F.eq_ofNat_of_some h'
    cases hm
    simp [F.ofNat] at h'
    rewrite [F.eq_ofNat_of_some_ofNat h'] at h
    rename_i b
    clear b
    dsimp only at h
    suffices Acc (fun n m' => m' < n ∧ m ≤ n ∧ (n = m ∨ x.val (n - m.succ))) y by
      refine cast ?_ this
      congr
      funext n m
      simp
      intro hmn
      dsimp [F.ofNat]
      split
      next h' =>
        simp at h'
        simp [Nat.not_le_of_lt h']
      next h' =>
        split at h' <;> cases h'
        rename_i h''
        rewrite [F.eq_ofNat_of_some_ofNat h'']
        simp [h'']
    suffices Acc (fun n m' => m' < n ∧ (n = .zero ∨ x.val n.pred)) (y - m) by
      clear hy h
      have : y = m + (y - m) := by omega
      clear h'
      generalize y - m = z at this
      cases this
      simp at this
      induction this with
      | _  z _ ih =>
      constructor
      intro y ⟨h₁, h₂, h₃⟩
      have : y = m + (y - m) := by omega
      clear h₂
      generalize y - m = y' at this
      cases this
      simp at h₁ h₃
      simp [Nat.add_comm m y', Nat.sub_add_eq] at h₃
      exact ih y' ⟨h₁, h₃⟩
    replace h' := Nat.lt_or_eq_of_le h'
    cases h' with
    | inl h' =>
      suffices Acc (fun n m' => m' < n ∧ x.val n = true) (y - m.succ) by
        clear hy h n
        have : y = m.succ + (y - m.succ) := by omega
        clear h'
        generalize y - m.succ = z at this
        cases this
        simp at this
        induction this with
        | _  z _ ih =>
        constructor
        intro y ⟨h₁, h₂⟩
        rewrite [Nat.succ_add] at h₁
        simp [Nat.succ_sub] at h₁
        simp [show y ≠ 0 by omega] at h₂
        specialize ih y.pred ⟨Nat.lt_sub_of_add_lt h₁, h₂⟩
        rewrite [Nat.succ_add] at ih
        simp [Nat.succ_sub] at ih
        rewrite [Nat.sub_add_cancel (by omega)] at ih
        exact ih
      exact x.property.apply (y - m.succ)
    | inr h' =>
      cases h'
      simp
      constructor
      intro k ⟨hk', hk⟩
      cases k
      . cases hk'
      cases hk
      . cases ‹_›
      clear hk'
      rename_i k hk
      simp at hk
      suffices Acc (fun n m' => m' < n ∧ x.val n) k by
        clear hy h y n
        induction this with
        | _  z _ ih =>
        constructor
        intro y ⟨h₁, h₂⟩
        cases h₂
        . subst_eqs; cases h₁
        rename_i h₂
        specialize ih _ ⟨by omega, h₂⟩ h₂
        rewrite [(by omega : y - 1 + 1 = y)] at ih
        exact ih
      exact x.property.apply k

def P'.shift (k : Nat) (x : P') : P' where
  val n := x.val (k + n)
  property := by have := InvImage.wf (k + ·) x.property; unfold InvImage at this; simp at this; exact this

theorem P'.shift_shift : (x.shift n).shift m = shift (n + m) x := by
  simp [shift, Nat.add_assoc]

def P'.shape (x : P') : F Unit where
  val n := if ∃ m ≤ n, x.val m then () else none
  property := by simp; intro n m h' h; exact ⟨m, h'.step, h⟩

theorem P'.val_shape (h : shape x = .ofNat n ()) : x.val n := by
  have := congrArg (·.val n) h
  simp [F.ofNat, shape] at this
  rcases this with ⟨m, hm, h'⟩
  replace hm := Nat.eq_or_lt_of_le hm
  cases hm with
  | inl hm =>
    cases hm
    exact h'
  | inr hm =>
    replace h := congrArg (·.val m) h
    simp [F.ofNat, Nat.not_le_of_lt hm, shape] at h
    cases h'.symm.trans (h m .refl)

instance : WellFoundedRelation P' where
  rel x' x := ∃ n, x.val n ∧ x' = x.shift n.succ
  wf := by
    constructor
    intro x
    constructor
    intro _ ⟨n, h, hx⟩
    cases hx
    clear h
    induction x.property.apply n with
    | intro n _ ih =>
      constructor
      intro _ ⟨m, h, hx⟩
      cases hx
      rewrite [P'.shift_shift]
      apply ih
      exact ⟨by simp; omega, h⟩

def P'.rec (f : F α → α) (x : P') : α :=
  f (F.poly.g ⟨x.shape, fun n _ => rec f (x.shift n.succ)⟩)
termination_by x
decreasing_by exact ⟨n, val_shape ‹_›, rfl⟩

def P'.iso_P : Iso P P' where
  f := P.rec' fold
  g := rec .fold
  g_f := by
    have : ∀ x y, (P.rec' fold (.node x y)).shape = x := by
      intro x y
      apply Subtype.eq
      funext n
      dsimp [P.rec', F.poly, fold, shape]
      cases h : x.val n with
      | none =>
        simp
        intro m hm
        split
        . rfl
        next h' =>
        exfalso
        split at h'
        . cases h'
        next h'' =>
        cases h''.symm.trans (F.val_none_mono hm h)
      | some =>
        have ⟨m, hm⟩ := F.eq_ofNat_of_some h
        cases hm
        simp [F.ofNat] at h ⊢
        refine ⟨m, h, ?_⟩
        split
        next h' =>
          split at h'
          next h'' => simp at h''
          . cases h'
        next h' =>
        generalize F.eq_ofNat_of_some _ = hk
        rcases hk with ⟨k, hk⟩
        split at h'
        . cases h'
        have : m ≤ k := by
          replace hk := congrArg (·.val k) hk
          simp [F.ofNat] at hk
          split at hk
          . cases hk
          next hk' =>
          simp at hk'
          exact hk'
        have : k ≤ m := by
          replace hk := congrArg (·.val m) hk
          simp [F.ofNat] at hk
          split at hk
          next hk' => simp at hk'
          split at hk
          . assumption
          . cases hk
        cases Nat.le_antisymm this ‹_›
        clear this
        clear this
        simp
    intro x
    induction x with
    | node x y ih =>
    unfold rec P.fold
    rewrite [F.poly.f_g]
    simp only [P.node.injIff]
    refine ⟨this x y, ?_⟩
    funext n h
    rewrite [Eq.rec_pi₁ (C := fun x n => x = F.ofNat n () → P)]
    dsimp only
    rewrite [Eq.rec_pi₂ (C := fun x => x = F.ofNat n ())]
    dsimp only
    change rec P.fold _ = _
    rewrite [this] at h
    cases h
    cases show h = this .. from rfl
    generalize hy : y n rfl = y'
    replace hy : y = fun _ _ => y' := by
      cases hy
      funext _ h
      cases (F.ofNat_inj h).left
      rfl
    cases hy
    specialize ih n rfl
    dsimp only at ih
    refine .trans ?_ ih
    congr
    apply Subtype.eq
    funext m
    dsimp only [P.rec', F.poly, fold, shift, F.ofNat]
    split
    next h =>
      split at h
      next h' => simp at h'; omega
      . cases h
    next h =>
    generalize F.eq_ofNat_of_some _ = hk
    rcases hk with ⟨k, hk⟩
    split at h
    . cases h
    cases h
    have : n ≤ k := by
      replace hk := congrArg (·.val k) hk
      simp [F.ofNat] at hk
      split at hk
      . cases hk
      next hk' =>
      simp at hk'
      exact hk'
    have : k ≤ n := by
      replace hk := congrArg (·.val n) hk
      simp [F.ofNat] at hk
      split at hk
      next hk' => simp at hk'
      split at hk
      . assumption
      . cases hk
    cases Nat.le_antisymm this ‹_›
    simp
    omega
  f_g x := by
    fun_induction rec P.fold x with
    | _ x ih =>
    unfold P.fold
    rewrite [F.poly.f_g]
    apply Subtype.eq
    funext n
    dsimp only [P.rec', F.poly, fold]
    split
    next h =>
      split at h
      next h' =>
        simp [shape] at h'
        exact (h' n .refl).symm
      . cases h
    next h =>
    generalize F.eq_ofNat_of_some _ = hm
    rcases hm with ⟨m, hm⟩
    split at h
    . cases h
    next h' =>
    generalize F.eq_ofNat_of_some _ = hl at h
    rcases hl with ⟨l, hl⟩
    dsimp only at h
    cases h
    have : l ≤ m := by
      replace hm := congrArg (·.val m) hm
      simp [F.ofNat] at hm
      split at hm
      . cases hm
      next hm' =>
      simp [hl, F.ofNat] at hm'
      exact hm'
    have : m ≤ l := by
      replace hm := congrArg (·.val l) hm
      simp [F.ofNat] at hm
      split at hm
      next hm' => simp [hl, F.ofNat] at hm'
      split at hm
      . assumption
      . cases hm
    cases Nat.le_antisymm this ‹_›
    dsimp only
    clear hm
    clear this
    clear this
    specialize ih m hl
    simp [hl, F.ofNat] at h'
    replace h' := Nat.eq_or_lt_of_le h'
    cases h' with
    | inl h' =>
      cases h'
      simp
      exact val_shape hl
    | inr h' =>
      simp [Nat.ne_of_gt h']
      change (P.rec' fold (rec P.fold _)).val _ = _
      rewrite [ih]
      simp [shift]
      apply congrArg
      omega
