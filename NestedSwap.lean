import Batteries.WF

section Markov

abbrev ExistsAfter (P : Nat → Prop) := Acc fun y x => y = x.succ ∧ ¬P x

inductive Nat.ge (n : Nat) : Nat → Prop
  | refl : ge n n
  | step : ge n m.succ → ge n m

theorem Nat.ge_succ : ge n m → ge n.succ m
  | .refl   => .step .refl
  | .step h => .step <| ge_succ h

theorem Nat.ge_zero : ∀ n, ge n 0
  | zero   => .refl
  | succ n => ge_succ (ge_zero n)

theorem ExistsAfter.mk (hn : P n) (hnm : n.ge m) : ExistsAfter P m :=
  by induction hnm <;> constructor <;> rintro _ ⟨rfl, _⟩ <;> trivial

theorem ExistsAfter.ofExists : (∃ n, P n) → ExistsAfter P 0
  | ⟨n, hn⟩ => mk hn n.ge_zero

variable {P : Nat → Prop} [DecidablePred P]

def markovAfter : ExistsAfter P n → { n // P n } :=
  Acc.rec fun n _ ih => if hn : P n then ⟨n, hn⟩ else ih _ ⟨rfl, hn⟩

def markov (h : ∃ n, P n) : { n // P n } :=
  markovAfter <| .ofExists h

end Markov

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

theorem F.eq_ofNat_of_some (h : x.val n = some y) : ∃ m, x = ofNat m y := by
  have ⟨m, h, h'⟩ : ∃ m, x.val m = some y ∧ (∀ k < m, x.val k = none) := by
    induction n with
    | zero => exact ⟨_, h, nofun⟩
    | succ n ih =>
      cases h' : x.val n with
      | none =>
        refine ⟨_, h, fun k hk => ?_⟩
        clear h ih
        replace hk := Nat.le_of_lt_succ hk
        exact F.val_none_mono hk h'
      | some =>
        cases h.symm.trans (x.property n _ h')
        exact ih h'
  refine ⟨m, ?_⟩
  apply Subtype.eq
  funext n
  dsimp [ofNat]
  split <;> rename_i h''
  . exact F.val_some_mono h'' h
  . exact h' n (Nat.lt_of_not_le h'')

instance [DecidableEq t] : Decidable (x = @F.ofNat t n y) :=
  match h : x.val n with
  | none => isFalse fun h' => by have := congrArg (·.val n) h'; simp [F.ofNat] at this; cases h.symm.trans this
  | some y' =>
    if _ : y = y' then
      match n with
      | .zero => isTrue <| Subtype.eq <| by
        subst_eqs
        funext n
        simp [F.ofNat]
        exact F.val_some_mono n.zero_le h
      | .succ n =>
        match h' : x.val n with
        | none => isTrue <| Subtype.eq <| by
          subst_eqs
          funext m
          dsimp [F.ofNat]
          split
          next h' => exact F.val_some_mono h' h
          next h'' => exact F.val_none_mono (Nat.le_of_not_lt h'') h'
        | some _ => isFalse fun h'' => by
          subst_eqs
          simp [F.ofNat] at h'
          omega
    else isFalse fun h' => by have := congrArg (·.val n) h'; simp [F.ofNat] at this; rewrite [h] at this; cases this; contradiction

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
  g := fun ⟨x, y⟩ => Subtype.mk (fun n => match h : x.val n with | none => none | some () => some (let ⟨m, h⟩ := markov (F.eq_ofNat_of_some h); y m h)) <| by
    intro n a
    dsimp
    split <;> simp
    rename_i h
    intro h'
    cases h'
    split
    next h' => cases h'.symm.trans (x.property _ _ h)
    . rfl
  g_f x := Subtype.eq <| by
    funext n
    dsimp
    split
    next h => simp [map] at h; exact h.symm
    next h =>
      generalize markov (_ : ∃ m, map (fun x => ()) x = ofNat m ()) = m
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
          generalize markov (_ : ∃ m, x = ofNat m ()) = m
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
  apply Nat.unpair.go.induct_unfolding fun n hn x => x.snd ≤ n * 2
  . intro n hn h k m hkm ih
    apply Nat.le_trans ih
    omega
  . intro n hn h
    omega

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
      simp [Nat.mul_assoc, mul_add_one]
      refine Nat.le_trans ?_ (le_add_left ..)
      refine Nat.le_trans ?_ (le_add_left ..)
      apply Nat.pow_pos
      simp
    simp [this]
    have : 2 ^ x * (2 * y + 1) - 1 + 1 = 2 ^ x * (2 * y + 1) := by
      apply Nat.sub_add_cancel
      simp [Nat.mul_assoc, mul_add_one]
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

theorem distinct : P ≠ Q := by
  intro h
  have : ∃ f : List Nat → P, ∀ y, ¬∀ x, f x ≠ y := ⟨P.mk, fun _ => P.cover⟩
  rewrite [h] at this
  clear h
  rcases this with ⟨f, h⟩
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
