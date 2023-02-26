import Mathlib.Data.Fin.Tuple.Basic
import Rec

variable {motive : ∀ n, Fin n → Sort u} (zero : ∀ {n}, motive (.succ n) 0) (succ : ∀ {n} i, motive n i → motive n.succ i.succ) in
def Fin.recL : ∀ {n} i, motive n i
  | .succ _, ⟨.zero, _⟩ => zero
  | .succ _, ⟨.succ i, h⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ (recL _)

variable {motive : ∀ n, Fin n → Sort u} (castSucc : ∀ {n} i, motive n i → motive n.succ (.castSucc i)) (last : ∀ {n}, motive (.succ n) (.last _)) in
def Fin.recR : ∀ {n} i, motive n i
  | .succ _, i =>
    if h : i = _
    then h ▸ last
    else castSucc ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.2) (h <| Fin.eq_of_val_eq ·)⟩ (recR _)

namespace Level

inductive Exp : (n : Nat := .zero) → Type
  | var (l : Fin n) : Exp n
  | lam (e : Exp n.succ) : Exp n
  | app (e₁ e₂ : Exp n) : Exp n

namespace Exp

def lift' : (e : Exp n) → Exp (k + n)
  | var l => var (Fin.natAdd k l)
  | lam e => lam e.lift'
  | app e₁ e₂ => app e₁.lift' e₂.lift'

def lift : (e : Exp) → Exp n :=
  lift'

def subst (e : Exp n.succ) (e' : Exp) : Exp n :=
  match e with
  | var l => l.cases e'.lift var
  | lam e => lam (e.subst e')
  | app e₁ e₂ => app (e₁.subst e') (e₂.subst e')

def substAll {k} (e : Exp (k + n)) (es : Fin k → Exp) : Exp n :=
  match k with
  | 0 => n.zero_add ▸ e
  | k + 1 => substAll (k.add_right_comm 1 n ▸ e) (Fin.init es) |>.subst (es (.last _))

theorem cast_var (l : Fin n) (h : n = n') : h ▸ var l = var (Fin.cast h l) := by cases h; rfl

theorem cast_lam (e : Exp (.succ n)) (h : n = n') : h ▸ lam e = lam (congrArg Nat.succ h ▸ e) := by cases h; rfl

theorem cast_app (e₁ e₂ : Exp n) (h : n = n') : h ▸ app e₁ e₂ = app (h ▸ e₁) (h ▸ e₂) := by cases h; rfl

theorem lift_zero : ∀ e : Exp, e.lift = e := by
  suffices ∀ {n} (e : Exp n), e.lift' = (n.zero_add.symm ▸ e : Exp (0 + n)) from this
  intro n e
  induction e with simp [lift', cast_var, cast_lam, cast_app, *]
  | var => simp [Fin.natAdd]; rfl

theorem subst_lift : ∀ {n} (e e' : Exp), e.lift.subst e' = e.lift (n := n) := by
  suffices ∀ {n k} (e : Exp n) e', (k.succ_add n ▸ e.lift').subst e' = e.lift' (k := k) from λ {n} => this
  intro n k e e'
  induction e with simp [lift', cast_var, cast_lam, cast_app, subst, *]
  | var => simp [Fin.natAdd, Nat.succ_add]

theorem substAll_var' (l : Fin n) {k} es : substAll (var <| Fin.natAdd k l) es = var l := by
  induction k generalizing n with simp [substAll, cast_var]
  | succ _ ih =>
    simp [Fin.cast, Fin.castLe, Fin.castLt, Nat.succ_add]
    specialize ih l.succ (Fin.init es)
    simp [Fin.natAdd, Nat.add_succ] at ih
    rw [ih]
    rfl

theorem substAll_var {k} (l : Fin k) es : substAll (var <| Fin.castAdd n l) es = (es l).lift := by
  induction l using Fin.recR generalizing n with simp [substAll, cast_var]
  | castSucc l ih =>
    specialize @ih n.succ (Fin.init es)
    dsimp [Fin.cast, Fin.castAdd, Fin.castLe, Fin.castLt] at ih ⊢
    rw [ih]
    apply subst_lift (es _)
  | last =>
    dsimp [Fin.cast, Fin.castLe, Fin.castLt]
    have := substAll_var' (0 : Fin n.succ) (Fin.init es)
    dsimp [Fin.natAdd] at this
    rw [this]
    rfl

theorem substAll_lam {k} (e : Exp (.succ (k + n))) es : substAll (lam e) es = lam (substAll e es) := by
  induction k generalizing n with simp [substAll, cast_lam]
  | succ k ih => rw [ih]; simp [subst]

theorem substAll_app {k} (e₁ e₂ : Exp (k + n)) es : substAll (app e₁ e₂) es = app (substAll e₁ es) (substAll e₂ es) := by
  induction k generalizing n with simp [substAll, cast_app]
  | succ k ih => rw [ih]; simp [subst]

def rec' {motive : Exp → Sort u} (lam : ∀ e, (∀ e', motive e' → motive (e.subst e')) → motive (lam e)) (app : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (app e₁ e₂)) : ∀ e, motive e :=
  rec' Fin.elim0 finZeroElim
where
  rec' {n} (es : Fin n → Exp) (hes : ∀ l, motive (es l)) : (e : Exp n) → motive (e.substAll (n := .zero) es)
  | var l => substAll_var .. ▸ lift_zero _ ▸ hes l
  | .lam e => substAll_lam .. ▸ lam _ λ e' he' =>
    have := rec' (Fin.lastCases e' es) (Fin.lastCases (by simp; exact he') (λ i => by simp; exact hes i)) e
    by simp [substAll] at this; (conv at «this» => enter [1, 2]; apply Fin.lastCases_last); dsimp [Fin.init] at this; (conv at «this» => enter [1, 1, 2]; apply funext <| Fin.lastCases_castSucc _ _); exact this
  | .app e₁ e₂ => substAll_app .. ▸ app _ _ (rec' es hes e₁) (rec' es hes e₂)

end Exp

end Level

namespace Index

inductive Exp : (n : Nat := .zero) → Type
  | var (i : Fin n) : Exp n
  | lam (e : Exp n.succ) : Exp n
  | app (e₁ e₂ : Exp n) : Exp n

namespace Exp

def lift' : (e : Exp n) → Exp (k + n)
  | var l => var (Fin.castLe (n.le_add_left k) l)
  | lam e => lam e.lift'
  | app e₁ e₂ => app e₁.lift' e₂.lift'

def lift : (e : Exp) → Exp n :=
  lift'

def subst (e : Exp n.succ) (e' : Exp) : Exp n :=
  match e with
  | var i => i.lastCases e'.lift var
  | lam e => lam (e.subst e')
  | app e₁ e₂ => app (e₁.subst e') (e₂.subst e')

def substAll {k} (e : Exp (k + n)) (es : Fin k → Exp) : Exp n :=
  match k with
  | 0 => n.zero_add ▸ e
  | k + 1 => substAll (k.add_right_comm 1 n ▸ e) (Fin.tail es) |>.subst (es 0)

theorem cast_var (i : Fin n) (h : n = n') : h ▸ var i = var (Fin.cast h i) := by cases h; rfl

theorem cast_lam (e : Exp (.succ n)) (h : n = n') : h ▸ lam e = lam (congrArg Nat.succ h ▸ e) := by cases h; rfl

theorem cast_app (e₁ e₂ : Exp n) (h : n = n') : h ▸ app e₁ e₂ = app (h ▸ e₁) (h ▸ e₂) := by cases h; rfl

theorem lift_zero : ∀ e : Exp, e.lift = e := by
  suffices ∀ {n} (e : Exp n), e.lift' = (n.zero_add.symm ▸ e : Exp (0 + n)) from this
  intro n e
  induction e with simp [lift', cast_var, cast_lam, cast_app, *]
  | var => rfl

theorem subst_lift : ∀ {n} (e e' : Exp), e.lift.subst e' = e.lift (n := n) := by
  suffices ∀ {n k} (e : Exp n) e', (k.succ_add n ▸ e.lift').subst e' = e.lift' (k := k) from λ {n} => this
  intro n k e e'
  induction e with simp [lift', cast_var, cast_lam, cast_app, subst, *]
  | var => apply Fin.lastCases_castSucc (i := ⟨_, _⟩)

theorem substAll_var' (i : Fin n) {k} es : substAll (var <| Fin.castLe (n.le_add_left k) i) es = var i := by
  induction k generalizing n with simp [substAll, cast_var, Fin.cast, Fin.castLe, Fin.castLt]
  | succ _ ih =>
    specialize ih (Fin.castSucc i) (Fin.tail es)
    dsimp [Fin.castLe, Fin.castLt] at ih
    rw [ih]
    simp [subst]

theorem substAll_var {k} (i : Fin k) es : substAll (var <| Fin.addNat n i) es = (es i).lift := by
  induction i using Fin.recL generalizing n with simp [substAll, cast_var, Fin.cast, Fin.castLe, Fin.castLt]
  | zero =>
    have := substAll_var' (@Fin.last n) (Fin.tail es)
    dsimp [Fin.castLe, Fin.castLt] at this
    rw [this]
    simp [subst]
  | succ _ ih =>
    simp [Nat.add_assoc, Nat.one_add]
    specialize @ih n.succ (Fin.tail es)
    dsimp [Fin.addNat] at ih
    rw [ih]
    apply subst_lift

theorem substAll_lam {k} (e : Exp (.succ (k + n))) es : substAll (lam e) es = lam (substAll e es) := by
  induction k generalizing n with simp [substAll, cast_lam]
  | succ k ih =>
    rw [ih]
    simp [subst]

theorem substAll_app {k} (e₁ e₂ : Exp (k + n)) es : substAll (app e₁ e₂) es = app (substAll e₁ es) (substAll e₂ es) := by
  induction k generalizing n with simp [substAll, cast_app]
  | succ k ih =>
    rw [ih]
    simp [subst]

def rec' {motive : Exp → Sort u} (lam : ∀ e, (∀ e', motive e' → motive (e.subst e')) → motive (lam e)) (app : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (app e₁ e₂)) : ∀ e, motive e :=
  rec' Fin.elim0 finZeroElim
where
  rec' {n} (es : Fin n → Exp) (hes : ∀ i, motive (es i)) : (e : Exp n) → motive (e.substAll (n := .zero) es)
  | var i => substAll_var .. ▸ lift_zero _ ▸ hes i
  | .lam e => substAll_lam .. ▸ lam _ λ e' he' => (rec' (Fin.cases e' es) (Fin.cases he' hes) e :)
  | .app e₁ e₂ => substAll_app .. ▸ app _ _ (rec' es hes e₁) (rec' es hes e₂)

end Exp

end Index

def forall₂_sigma {α : Type u} {β : α → Type v} {γ : ∀ x, β x → Type w} {δ : ∀ x y, γ x y → Type x} (f : ∀ x y, (z : γ x y) × δ x y z) : (g : ∀ x y, γ x y) × ∀ x y, δ x y (g x y) :=
  ⟨(f · · |>.fst), (f · · |>.snd)⟩

def forall₂_subtype {α : Sort u} {β : α → Sort v} {γ : ∀ x, β x → Sort w} {δ : ∀ x y, γ x y → Prop} (f : ∀ x y, { z // δ x y z }) : { g : ∀ x y, γ x y // ∀ x y, δ x y (g x y) } :=
  ⟨(f · · |>.val), (f · · |>.property)⟩

namespace HOAS

variable (v : Type) in
inductive Tm
  | var (x : v)
  | lam (e : v → Tm)
  | app (e₁ e₂ : Tm)

def Tm.flatten : Tm (Tm v) → Tm v
  | var x => x
  | lam e => lam λ x => (e (var x)).flatten
  | app e₁ e₂ => app e₁.flatten e₂.flatten

def Tm.liftRel (r : v → v' → Prop) : Tm v → Tm v' → Prop
  | var x, var x' => r x x'
  | lam e, lam e' => ∀ x x', r x x' → liftRel r (e x) (e' x')
  | app e₁ e₂, app e₁' e₂' => liftRel r e₁ e₁' ∧ liftRel r e₂ e₂'
  | _, _ => False

theorem Tm.liftRel_flatten (h : liftRel (liftRel r) e e') : liftRel r e.flatten e'.flatten := by
  induction e generalizing e' <;> cases e' <;> try contradiction
  case var => exact h
  case lam ih _ => exact λ _ _ hx => ih _ <| h _ _ hx
  case app ih₁ ih₂ _ _ => exact ⟨ih₁ h.left, ih₂ h.right⟩

def Exp (n : Nat := .zero) := { e : ∀ v, (Fin n → v) → Tm v // ∀ {v v'} r xs xs', (∀ i, r (xs i) (xs' i)) → Tm.liftRel r (e v xs) (e v' xs') }

namespace Exp

def var (i : Fin n) : Exp n :=
  ⟨λ _ xs => .var <| xs i, λ _ _ _ hxs => hxs i⟩

def lam (e : Exp n.succ) : Exp n :=
  ⟨λ _ xs => .lam λ x => e.val _ <| Fin.cases x xs, λ _ _ _ hxs _ _ hx => e.property _ _ _ <| Fin.cases hx hxs⟩

def app (e₁ e₂ : Exp n) : Exp n :=
  ⟨λ _ xs => .app (e₁.val _ xs) (e₂.val _ xs), λ _ _ _ hxs => ⟨e₁.property _ _ _ hxs, e₂.property _ _ _ hxs⟩⟩

def subst (e : Exp n.succ) (e' : Exp n) : Exp n :=
  ⟨λ _ xs => .flatten <| e.val _ <| Fin.lastCases (e'.val _ xs) (λ i => .var (xs i)), λ _ _ _ hxs => Tm.liftRel_flatten <| e.property _ _ _ <| Fin.lastCases (by simp; exact e'.property _ _ _ hxs) (by simp; exact hxs)⟩

def eq_var {e : Exp n} {v xs x} (h : e.val v xs = .var x) : { i // e = var i } := by
  have := h ▸ e.property (· = xs ·) xs id λ _ => rfl
  generalize h₁ : e.val _ id = e' at this
  cases e' <;> try contradiction
  cases this
  clear v xs h
  rename_i i
  refine ⟨i, Subtype.eq ?_⟩
  funext v xs
  have := h₁ ▸ e.property (· = xs ·) xs id λ _ => rfl
  generalize e.val v xs = e' at this
  cases e' <;> try contradiction
  cases this
  rfl

def eq_lam {e : Exp n} {v xs e'} (h : e.val v xs = .lam e') : { e' // e = lam e' } := by
  have h₁ : ∀ v xs, { e' // e.val v xs = .lam e' } := by
    intro v' xs'
    have := h ▸ e.property (λ _ _ => True) xs xs' λ _ => ⟨⟩
    generalize e.val v' xs' = e' at this
    cases e' <;> try contradiction
    exact ⟨_, rfl⟩
  have ⟨e', h₂⟩:= forall₂_subtype h₁
  have h : e.val = _ := funext (funext <| h₂ ·)
  refine ⟨⟨λ _ xs => e' _ (Fin.tail xs) (xs 0), λ _ _ _ hxs => ?_⟩, Subtype.eq h⟩
  exact (h ▸ e.property _ _ _ (hxs ·.succ)) _ _ (hxs 0)

def eq_app {e : Exp n} {v xs e₁ e₂} (h : e.val v xs = .app e₁ e₂) : (e₁ : _) × { e₂ // e = app e₁ e₂ } := by
  have h₁ : ∀ v xs, (e₁ : _) × { e₂ // e.val v xs = .app e₁ e₂ } := by
    intro v' xs'
    have := h ▸ e.property (λ _ _ => True) xs xs' λ _ => ⟨⟩
    generalize e.val v' xs' = e' at this
    cases e' <;> try contradiction
    exact ⟨_, _, rfl⟩
  have ⟨e₁, h₂⟩ := forall₂_sigma h₁
  have ⟨e₂, h₁⟩ := forall₂_subtype h₂
  have h : e.val = _ := funext (funext <| h₁ ·)
  refine ⟨⟨e₁, λ _ _ _ hxs => ?_⟩, ⟨e₂, λ _ _ _ hxs => ?_⟩, Subtype.eq h⟩
  all_goals
    have ⟨_, _⟩ := h ▸ e.property _ _ _ hxs
    assumption

def liftAll (e : Exp) : Exp n :=
  ⟨λ _ _ => e.val _ Fin.elim0, λ _ _ _ _ => e.property _ _ _ finZeroElim⟩

theorem liftAll_eq e : liftAll e = e := by
  apply Subtype.eq
  funext v xs
  dsimp [liftAll]
  apply congrArg
  funext i
  apply i.elim0

def substAll {k} (e : Exp (k + n)) (es : Fin k → Exp) : Exp n :=
  match k with
  | 0 => n.zero_add ▸ e
  | k + 1 => substAll (k.add_right_comm 1 n ▸ e) (Fin.tail es) |>.subst (es 0).liftAll

theorem subst_var (i : Fin n.succ) (e' : Exp n) : (var i).subst e' = i.lastCases e' var := by
  cases i using Fin.lastCases with simp [subst, var]
  | hcast => rfl
  | hlast => rfl

def lift (e : Exp n) : Exp n.succ :=
  ⟨λ _ xs => e.val _ (Fin.tail xs), λ _ _ _ hxs => e.property _ _ _ (hxs ·.succ)⟩

theorem subst_lam (e : Exp n.succ.succ) (e' : Exp n) : (lam e).subst e' = lam (e.subst (e'.lift)) := by
  apply Subtype.eq
  funext v xs
  apply congrArg Tm.lam
  funext x
  dsimp [subst]
  congr
  apply congrArg
  funext i
  cases i using Fin.lastCases with
  | hcast i =>
    simp
    cases i using Fin.cases with
    | H0 => rfl
    | Hs i =>
      simp [Fin.castSucc, Fin.castAdd, Fin.castLe, Fin.castLt, Fin.lastCases]
      unfold Fin.reverseInduction
      exact dif_neg <| Nat.ne_of_lt i.isLt ∘ Fin.val_eq_of_eq
  | hlast =>
    simp
    rw [Fin.cases]
    simp [Fin.induction]
    show Fin.lastCases (C := _) _ _ (.last _) = _
    simp [lift]
    rfl

theorem subst_app (e₁ e₂ : Exp n.succ) (e' : Exp n) : (app e₁ e₂).subst e' = app (e₁.subst e') (e₂.subst e') := rfl

theorem cast_var (l : Fin n) (h : n = n') : h ▸ var l = var (Fin.cast h l) :=
  by cases h; rfl

theorem substAll_var' (i : Fin n) {k} (es : Fin k → Exp) : substAll (var <| Fin.castLe (n.le_add_left k) i) es = var i := by
  induction k generalizing n with simp [substAll, cast_var, Fin.cast, Fin.castLe, Fin.castLt]
  | succ _ ih =>
    specialize ih (Fin.castSucc i) (Fin.tail es)
    dsimp [Fin.castLe, Fin.castLt] at ih
    rw [ih]
    simp [subst, Tm.flatten, var]

theorem substAll_var {k} (i : Fin k) (es : Fin k → Exp) : substAll (var <| Fin.addNat n i) es = (es i).liftAll := by
  induction i using Fin.recL generalizing n with simp [substAll, cast_var, Fin.cast, Fin.castLe, Fin.castLt]
  | zero =>
    have := substAll_var' (n := n.succ) (.last _) (Fin.tail es)
    dsimp [Fin.castLe, Fin.castLt] at this
    rw [this]
    simp [subst, Tm.flatten]
  | succ i ih =>
    specialize @ih n.succ (Fin.tail es)
    dsimp [Fin.addNat] at ih
    simp [Nat.add_assoc, Nat.one_add]
    rw [ih]
    simp [subst]
    apply Subtype.eq
    funext v xs
    simp [liftAll]
    suffices ∀ {n} (e : Exp n) (es : Fin n → v), (e.val _ (.var <| es ·)).flatten = e.val _ es from
      (congrArg (Tm.flatten <| (Fin.tail es i).val _ ·) <| funext finZeroElim).trans <| this _ _
    clear k i n es ih xs
    rename_i k
    clear k
    intro n e es
    generalize h : e.val _ es = e'
    induction e' generalizing n with
    | var =>
      have ⟨i, h⟩ := eq_var h
      cases h
      cases h
      rfl
    | lam _ ih =>
      have ⟨e, h⟩ := eq_lam h
      cases h
      cases h
      dsimp [Tm.flatten]
      congr
      funext x
      specialize ih x _ _ rfl
      dsimp at ih
      apply Eq.trans _ ih
      congr
      apply congrArg
      funext i
      cases i using Fin.cases <;> rfl
    | app _ _ ih₁ ih₂ =>
      have ⟨e₁, e₂, h⟩ := eq_app h
      cases h
      cases h
      dsimp [Tm.flatten]
      congr
      . exact ih₁ _ _ rfl
      . exact ih₂ _ _ rfl

theorem cast_lam (e : Exp (.succ n)) (h : n = n') : h ▸ lam e = lam (congrArg Nat.succ h ▸ e) := by cases h; rfl

theorem substAll_lam {k} (e : Exp (k + n).succ) (es : Fin k → Exp) : substAll (lam e) es = lam (substAll e es) := by
  induction k generalizing n with simp [substAll, cast_lam]
  | succ k ih =>
    specialize @ih n.succ (congrArg Nat.succ (k.add_right_comm 1 _) ▸ e) (Fin.tail es)
    rw [ih]
    simp [subst_lam]
    rfl

theorem cast_app (e₁ e₂ : Exp n) (h : n = n') : h ▸ app e₁ e₂ = app (h ▸ e₁) (h ▸ e₂) := by cases h; rfl

theorem substAll_app {k} (e₁ e₂ : Exp (k + n)) (es : Fin k → Exp) : substAll (app e₁ e₂) es = app (substAll e₁ es) (substAll e₂ es) := by
  induction k generalizing n with simp [substAll, cast_app]
  | succ k ih =>
    specialize @ih n.succ (k.add_right_comm 1 _ ▸ e₁) (k.add_right_comm 1 _ ▸ e₂) (Fin.tail es)
    rw [ih]
    simp [subst_app]

#compile HOAS.Tm

def rec' {motive : Exp → Sort u} (lam : ∀ e, (∀ e', motive e' → motive (e.subst e')) → motive (lam e)) (app : ∀ e₁ e₂, motive e₁ → motive e₂ → motive (app e₁ e₂)) : ∀ e, motive e := by
  suffices ∀ {n} (es : Fin n → Exp), (∀ i, motive (es i)) → ∀ {e : Exp n} {e'}, (e.val _ (λ _ => ()) = e') → motive (e.substAll (n := .zero) es) from λ _ => this Fin.elim0 finZeroElim rfl
  intro n es hes e e' h
  induction e' generalizing n with
  | var =>
    have ⟨i, h⟩ := eq_var h
    cases h
    cases h
    have := substAll_var (n := .zero) i es
    dsimp [Fin.addNat] at this
    rw [this, liftAll_eq]
    exact hes i
  | lam _ ih =>
    have ⟨e, h⟩ := eq_lam h
    cases h
    cases h
    rw [substAll_lam]
    apply lam
    intro e' he'
    rw [← liftAll_eq e']
    exact ih () (Fin.cases e' es) (Fin.cases he' hes) rfl
  | app _ _ ih₁ ih₂ =>
    have ⟨e₁, e₂, h⟩ := eq_app h
    cases h
    cases h
    rw [substAll_app]
    exact app _ _ (ih₁ _ hes rfl) (ih₂ _ hes rfl)

end Exp

end HOAS
