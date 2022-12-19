import Std
import Common.Rel
import Common.Meta

def Fin.zero : Fin (.succ n) := ⟨0, n.zero_lt_succ⟩
def Fin.last : Fin (.succ n) := ⟨n, n.lt_succ_self⟩
def Fin.castSucc (i : Fin n) : Fin n.succ := ⟨i, .step i.2⟩
def Fin.castLe (h : n ≤ m) (i : Fin n) : Fin m := ⟨i, Nat.le_trans i.2 h⟩

def Nat.le_add_right_of_le {m n k : Nat} (h : m ≤ n) : m ≤ n + k :=
  Nat.le_trans h (Nat.le_add_right n k)

def Nat.le_add_left_of_le {m n k : Nat} (h : m ≤ n) : m ≤ k + n :=
  Nat.le_trans h (Nat.le_add_left n k)

def Var := Nat deriving DecidableEq

protected def Var.toString (x : Var) : String :=
  ⟨toString x []⟩
where
  toString x l :=
    let l := Char.ofNat ('a'.toNat + x % 26) :: l
    match h : x / 26 with
    | 0 => l
    | q + 1 =>
      have := h ▸ Nat.div_le_self ..
      toString q l

instance : ToString Var := ⟨Var.toString⟩

instance : OfNat Var n := ⟨n⟩

def Var.ofString : String → Var
  | ⟨l⟩ =>
    l.foldl (λ x c => (x + 1) * 26 + (c.toNat - 'a'.toNat).min 25) 0 - 26 ^ l.length

instance : Coe String Var := ⟨Var.ofString⟩

/-
def Var.fresh : List Var → Var
  | [] => .zero
  | x :: xs => x.succ.max (fresh xs)

theorem Var.fresh_correct : fresh l ∉ l := by
  suffices ∀ y, (fresh l).le y → y ∉ l from this _ .refl
  intro y h
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro h
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_left _ _) h |> Nat.ne_of_gt <| rfl
    | tail _ h' => exact Nat.le_trans (Nat.le_max_right _ _) h |> ih <| h'
-/

inductive Term : (d : Nat := .zero) → Type
  | fvar : Var → Term d
  | bvar : Fin d → Term d
  | abs : Term d.succ → Term d
  | app : Term d → Term d → Term d

namespace Term

protected def toString : Term d → String
  | fvar x => x.toString ++ "'"
  | bvar n => Var.toString (d.pred - n.1)
  | abs e => s!"(λ{Var.toString d}.{e.toString})"
  | app e₁ e₂ => s!"({e₁.toString} {e₂.toString})"

instance instToString : ToString (Term d) := ⟨Term.toString⟩

instance instCoeVar : Coe Var (Term d) := ⟨fvar⟩

instance instCoeFun : CoeFun Term (λ _ => Term → Term) := ⟨app⟩

def weaken (hd : d₁ ≤ d₂) : Term d₁ → Term d₂
  | fvar x => fvar x
  | bvar n => bvar (n.castLe hd)
  | abs e => abs (e.weaken (Nat.succ_le_succ hd))
  | app e₁ e₂ => app (e₁.weaken hd) (e₂.weaken hd)

theorem weaken_refl : {e : Term d} → weaken .refl e = e
  | fvar _ => rfl
  | bvar _ => rfl
  | abs _ => congrArg abs weaken_refl
  | app .. => congrArg₂ app weaken_refl weaken_refl

variable (x : Var) in
def bind : Term d → Term d.succ
  | fvar y => if y = x then bvar .last else fvar y
  | bvar n => bvar n.castSucc
  | abs e => abs e.bind
  | app e₁ e₂ => app e₁.bind e₂.bind

def abs' (x : Var) (e : Term) : Term :=
  abs (e.bind x)

theorem bind_bind : bind x e = bind y e' → bind x (bind z e) = bind y (bind z e') := sorry

variable (e' : Term) in
def subst : Term d.succ → Term d :=
  subst
where
  subst {d' d} : Term d' → Term d
  | fvar x => fvar x
  | bvar n => if h : n < d then bvar ⟨n, h⟩ else e'.weaken d.zero_le
  | abs e => abs (subst e)
  | app e₁ e₂ => app (subst e₁) (subst e₂)

theorem subst_weaken : {e : Term d} → subst e' (weaken (.step .refl) e) = e
  | fvar _ => rfl
  | bvar n => by simp [weaken, subst, subst.subst, Fin.castLe, n.2]
  | abs _ => congrArg abs subst_weaken
  | app .. => congrArg₂ app subst_weaken subst_weaken

theorem subst_bind : {e : Term d} → subst (fvar x) (bind x e) = e
  | fvar _ => by
    unfold bind
    split
    next h =>
      simp [subst, subst.subst, Fin.last, h]
      rfl
    . rfl
  | bvar n => by simp [bind, subst, subst.subst, Fin.castSucc, n.2]
  | abs _ => congrArg abs subst_bind
  | app .. => congrArg₂ app subst_bind subst_bind

variable (x : Var) in
def free : Term d → Prop
  | fvar y => y ≠ x
  | bvar _ => True
  | abs e => e.free
  | app e₁ e₂ => e₁.free ∧ e₂.free

theorem bind_subst (h : e.free x) : bind x (subst (fvar x) e) = e :=
  match e with
  | fvar _ => if_neg h
  | bvar n => by
    unfold subst subst.subst
    split
    . rfl
    next h =>
      simp [weaken, bind]
      exact Nat.pred_le_pred n.2 |> Nat.eq_or_lt_of_le |>.resolve_right h |>.symm |> Fin.eq_of_val_eq
  | abs _ => congrArg abs (bind_subst h)
  | app .. => congrArg₂ app (bind_subst h.1) (bind_subst h.2)

theorem free_bind : (e : Term d) → e.free x → (e.bind y).free x
  | fvar _, h => by
    unfold bind
    split
    . trivial
    . exact h
  | bvar _, h => h
  | abs e, h => free_bind e h
  | app e₁ e₂, h => ⟨free_bind e₁ h.1, free_bind e₂ h.2⟩

def fresh : Term d → Var
  | fvar x => x.succ
  | bvar _ => .zero
  | abs e => e.fresh
  | app e₁ e₂ => e₁.fresh.max e₂.fresh

variable (x : Var) in
theorem free_fresh (h : e.fresh.le x) : free x e :=
  match e with
  | fvar x => Nat.ne_of_lt h
  | bvar n => trivial
  | abs e => free_fresh (e := e) h
  | app e₁ e₂ => ⟨free_fresh <| Nat.le_trans (Nat.le_max_left ..) h, free_fresh <| Nat.le_trans (Nat.le_max_right ..) h⟩

@[simp]
theorem sizeOf_subst_fvar x : (e : Term d.succ) → sizeOf (subst (fvar x) e : Term d) < sizeOf e
  | fvar _ => .refl
  | bvar n => by
    unfold subst subst.subst
    split
    . apply Nat.add_lt_add_right .refl
    . apply Nat.le_add_right
  | abs e => Nat.add_lt_add .refl (sizeOf_subst_fvar ..)
  | app e₁ e₂ => Nat.add_lt_add (Nat.add_lt_add .refl (sizeOf_subst_fvar ..)) (sizeOf_subst_fvar ..)

section Congruence

variable (r : Term → Term → Prop)

class Congruence : Prop where
  abs {e e'} : r e e' → r (abs' x e) (abs' x e')
  app₁ {e₁ e₁'} : r e₁ e₁' → r (app e₁ e₂) (app e₁' e₂)
  app₂ {e₂ e₂'} : r e₂ e₂' → r (app e₁ e₂) (app e₁ e₂')

theorem Congruence.abs' {r} [Congruence r] (hx : e.free x) (hx' : e'.free x) (h : r ((fvar x).subst e) ((fvar x).subst e')) : r (.abs e) (.abs e') :=
  bind_subst hx ▸ bind_subst hx' ▸ abs h

theorem Congruence.abs'' {r} [Congruence r] (h : let x := fvar (e.fresh.max e'.fresh); r (x.subst e) (x.subst e')) : r (.abs e) (.abs e') :=
  abs' (free_fresh _ <| Nat.le_max_left ..) (free_fresh _ <| Nat.le_max_right ..) h

inductive CongruenceClosure : Term → Term → Prop
  | base : r e e' → CongruenceClosure e e'
  | abs {e e'} : CongruenceClosure e e' → CongruenceClosure (abs' x e) (abs' x e')
  | app₁ {e₁ e₁'} : CongruenceClosure e₁ e₁' → CongruenceClosure (app e₁ e₂) (app e₁' e₂)
  | app₂ {e₂ e₂'} : CongruenceClosure e₂ e₂' → CongruenceClosure (app e₁ e₂) (app e₁ e₂')

instance CongruenceClosure.instCongruence : Congruence (CongruenceClosure r) := ⟨@abs r, @app₁ r, @app₂ r⟩

instance ReflexiveTransitiveClosure.instCongruence [Congruence r] : Congruence (ReflexiveTransitiveClosure r) where
  abs := ReflexiveTransitiveClosure.lift (Congruence.abs ·)
  app₁ := ReflexiveTransitiveClosure.lift (Congruence.app₁ ·)
  app₂ := ReflexiveTransitiveClosure.lift (Congruence.app₂ ·)

instance EquivalenceClosure.instCongruence [Congruence r] : Congruence (EquivalenceClosure r) where
  abs := EquivalenceClosure.lift (Congruence.abs ·)
  app₁ := EquivalenceClosure.lift (Congruence.app₁ ·)
  app₂ := EquivalenceClosure.lift (Congruence.app₂ ·)

end Congruence

inductive BetaReduction : Term → Term → Prop
  | β : BetaReduction (app (abs' x e₁) e₂) (e₂.subst (e₁.bind x))

theorem BetaReduction.β' : BetaReduction (app (abs e₁) e₂) (e₂.subst e₁) :=
  have : BetaReduction (app (abs _) _) _ := β (x := e₁.fresh) (e₁ := (fvar e₁.fresh).subst e₁) (e₂ := e₂)
  (bind_subst (free_fresh _ .refl) ▸ this :)

infix:50 " →β " => CongruenceClosure BetaReduction
infix:50 " ↠β " => ReflexiveTransitiveClosure (CongruenceClosure BetaReduction)
infix:50 " =β " => EquivalenceClosure (CongruenceClosure BetaReduction)

/-
def Θ := reduce%
  let A := abs' "A" <| abs' "f" <| app "f" <| app (app "A" "A") "f"
  A A

#eval Θ

example : Θ f ↠β f (Θ f) :=
  .trans (.base <| .app₁ <| .base .β) <|
  .trans (.base <| .base .β) <|
  Reflexive.ofEq <|
  congrArg₂ app weaken_refl <| congrArg₂ app rfl weaken_refl

def Y := reduce%
  abs' "f" <| (abs' "x" <| app "f" (app "x" "x")) (abs' "x" <| app "f" (app "x" "x"))

#eval Y

example : Y f =β f (Y f) :=
  .trans (.base <| .base .β) <|
  .trans (.base <| .base .β) <|
  flip .trans (.symm <| .base <| .app₂ <| .base .β) <|
  Reflexive.ofEq <|
  congrArg₂ app subst_weaken <| congrArg₂ app weaken_refl weaken_refl
-/

namespace Confluence

inductive BetaParallel : Term → Term → Prop
  | β : BetaParallel e₁ e₁' → BetaParallel e₂ e₂' → BetaParallel (app (abs' x e₁) e₂) (e₂'.subst (e₁'.bind x))
  | var : BetaParallel (fvar x) (fvar x) -- TODO : change this to refl
  | abs : BetaParallel e e' → BetaParallel (abs' x e) (abs' x e')
  | app : BetaParallel e₁ e₁' → BetaParallel e₂ e₂' → BetaParallel (app e₁ e₂) (.app e₁' e₂')

infix:50 " ▷β " => BetaParallel
infix:50 " ▷β* " => ReflexiveTransitiveClosure BetaParallel

namespace BetaParallel

theorem abs' (h : let x := fvar (e.fresh.max e'.fresh); x.subst e ▷β x.subst e') : .abs e ▷β .abs e' :=
  abs h |> (congrArg₂ BetaParallel · · |>.mp)
    (congrArg _ <| bind_subst <| free_fresh _ <| Nat.le_max_left ..)
    (congrArg _ <| bind_subst <| free_fresh _ <| Nat.le_max_right ..)

theorem refl : ∀ {e}, e ▷β e
  | .fvar _ => var
  | .abs e =>
    have := sizeOf_subst_fvar (e.fresh.max e.fresh) e
    have := Nat.le_trans this <| Nat.le_add_left _ 1
    abs' refl
  | .app _ _ => app refl refl
termination_by _ e => e

theorem red : e →β e' → e ▷β e'
  | .base .β => β refl refl
  | .abs h => abs (red h)
  | .app₁ h => app (red h) refl
  | .app₂ h => app refl (red h)

theorem red_t : e ▷β e' → e ↠β e'
  | β h₁ h₂ => .trans (.trans (Congruence.app₁ <| Congruence.abs <| red_t h₁) (Congruence.app₂ <| red_t h₂)) (.base <| .base .β)
  | var => .refl
  | abs h => Congruence.abs <| red_t h
  | app h₁ h₂ => .trans (Congruence.app₁ <| red_t h₁) (Congruence.app₂ <| red_t h₂)

theorem clos₁ : e ↠β e' → e ▷β* e' :=
  .lift (r := CongruenceClosure _) red

theorem clos₂ (h : e ▷β* e') : e ↠β e' :=
  h.rec red_t .refl λ _ _ => .trans

/-
theorem lift {M M' : Term f} {b : Fin2 f.succ} : M ▷β M' → M.lift' b.toNat ▷β M'.lift' b.toNat
  | β h₁ h₂ => Term.lift'_subst _ _ b ▸ .β (Fin2.toNat_castSucc ▸ lift h₁) (lift h₂)
  | var => var
  | abs h => abs (Fin2.toNat_castSucc ▸ lift h)
  | app h₁ h₂ => app (lift h₁) (lift h₂)

theorem subst {M M' : Term (.succ f)} {N N' : Term f} (hN : N ▷β N') : M ▷β M' → ∀ {b}, M.subst' b N ▷β M'.subst' b N'
  | β _ _, .zero => (sorry : .app (.abs (.subst' _ .zero N.lift)) (.subst' _ .zero N) ▷β .subst' (.subst _ _) .zero N')
  | β _ _, .succ b => (sorry : .app (.abs (.subst' _ b.castSucc.succ N.lift)) (.subst' _ b.succ N) ▷β .subst' (.subst _ _) b.succ N')
    | @var _ n, b => by
    simp [Term.subst'.impl, Term.impl.subst']
    cases Term.substVar b n <;> simp
    case zero => exact hN
    case succ => exact var
  | abs h, .zero => abs (subst (by have := @lift _ _ _ (@Fin2.last f) hN; simp at this; exact this : N.lift' f ▷β N'.lift' f) h)
  | abs h, .succ b => abs (subst (by have := @lift _ _ _ (@Fin2.last f) hN; simp at this; exact this : N.lift ▷β N'.lift) h)
  | app h₁ h₂, _ => app (subst hN h₁) (subst hN h₂)
-/

end BetaParallel

inductive MaxBeta : Term → Term → Prop
  | β : MaxBeta e₁ e₁' → MaxBeta e₂ e₂' → MaxBeta (app (abs' x e₁) e₂) (e₂'.subst (e₁'.bind x))
  | var : MaxBeta (fvar x) (fvar x)
  | abs : MaxBeta e e' → MaxBeta (abs' x e) (abs' x e')
  | app : (∀ e₁', e₁ ≠ abs e₁') → MaxBeta e₁ e₁' → MaxBeta e₂ e₂' → MaxBeta (app e₁ e₂) (.app e₁' e₂')

theorem MaxBeta.deterministic : ∀ e, MaxBeta e e₁ → MaxBeta e e₂ → e₁ = e₂
  | .fvar _, .var, .var => rfl
  | .abs e, h, h' => by
    generalize he' : e = e' at h'
    cases h with | abs h =>
    cases h' with | abs h' =>
    apply congrArg Term.abs
    sorry
  | .app e₁ e₂, .app _ h₁ h₂, .app _ h₁' h₂' => by cases deterministic e₁ h₁ h₁'; cases deterministic e₂ h₂ h₂'; rfl
  | .app (.abs' x e₁) e₂, .β h₁ h₂, .β h₁' h₂' => by cases deterministic e₁ h₁ h₁'; cases deterministic e₂ h₂ h₂'; rfl

def maxBeta : Term → Term
  | .fvar x => .fvar x
  | .abs e =>
    have := sizeOf_subst_fvar e.fresh e
    have := Nat.le_trans this <| Nat.le_add_left _ 1
    .abs' e.fresh (maxBeta ((fvar e.fresh).subst e))
  | .app (.abs e₁) e₂ =>
    have := sizeOf_subst_fvar e₁.fresh e₁
    have : _ < 1 + (1 + sizeOf e₁) + sizeOf e₂ := Nat.le_trans this <| Nat.le_add_right_of_le <| Nat.le_add_left_of_le <| Nat.le_add_left _ 1
    (maxBeta e₂).subst ((maxBeta ((fvar e₁.fresh).subst e₁)).bind e₁.fresh)
  | .app e₁ e₂ => .app (maxBeta e₁) (maxBeta e₂)

theorem MaxBeta_maxBeta : ∀ e, MaxBeta e (maxBeta e)
  | .fvar x => .var
  | .abs e => by
    simp [maxBeta]
    have : abs' e.fresh ((fvar e.fresh).subst e) = abs e := congrArg abs <| bind_subst <| free_fresh _ .refl
    rw [← this]
    have := sizeOf_subst_fvar e.fresh e
    have := Nat.le_trans this <| Nat.le_add_left _ 1
    exact .abs (MaxBeta_maxBeta _)
  | .app (.abs e₁) e₂ => by
    simp [maxBeta]
    have : abs' e₁.fresh ((fvar e₁.fresh).subst e₁) = abs e₁ := congrArg abs <| bind_subst <| free_fresh _ .refl
    rw [← this]
    have := sizeOf_subst_fvar e₁.fresh e₁
    have : _ < 1 + (1 + sizeOf e₁) + sizeOf e₂ := Nat.le_trans this <| Nat.le_add_right_of_le <| Nat.le_add_left_of_le <| Nat.le_add_left _ 1
    exact .β (MaxBeta_maxBeta _) (MaxBeta_maxBeta e₂)
  | .app (.fvar x) e₂ => by
    simp [maxBeta]
    exact .app (λ _ h => nomatch h) (MaxBeta_maxBeta _) (MaxBeta_maxBeta e₂)
  | .app (.app e₁ e₁') e₂ => by
    simp [maxBeta]
    exact .app (λ _ h => nomatch h) (MaxBeta_maxBeta _) (MaxBeta_maxBeta e₂)

theorem maxBeta_subst : (e : Term 1) → e.free x → e.free y → (maxBeta ((fvar x).subst e)).bind x = (maxBeta ((fvar y).subst e)).bind y
  | .fvar z, hx, hy => by unfold free at hx hy; simp [bind, hx, hy]
  | .bvar .zero, hx, hy => by simp [bind]
  | .abs e, hx, hy => by
    unfold free at hx hy
    simp [subst, subst.subst, fresh, maxBeta, Term.abs', bind]
    have := maxBeta_subst (x := ((fvar x).subst e).fresh) ((fvar x).subst e) (free_fresh _ .refl) (free_fresh (fresh (subst (fvar y) e)) sorry)
    simp [subst] at this
    rw [this]
    sorry
  | .app (.abs e₁) e₂, hx, hy => sorry
  | .app e₁ e₂, hx, hy => sorry

/-
theorem maxBeta_free : ∀ e : Term, (e.bind x).free y → (maxBeta ((fvar y).subst (e.bind x))).bind y = (maxBeta e).bind x
  | .fvar x, h => by
    dsimp [bind]
    split
    . simp [bind]
    next h' =>
      simp [bind, free, h'] at h
      simp [bind, h]
  | .abs e, h => by
    --have := maxBeta_free (x := sorry) ((fvar sorry).subst e) sorry
    simp [bind, fresh, subst, maxBeta]
    sorry
  | .app (.abs e₁) e₂, h => by
    sorry
  | .app e₁ e₂, h => sorry

theorem maxBeta_abs' : ∀ e, maxBeta (Term.abs' x e) = .abs' x (maxBeta e) := by
  intro e
  simp [Term.abs', maxBeta]
  apply maxBeta_free e <| free_fresh _ .refl
/-
  | .fvar x => by
    simp [Term.abs', maxBeta, bind]
    split
    . simp [bind]
    . simp [bind, fresh]
  | .abs e => by
    simp [Term.abs', maxBeta, bind, subst, fresh, weaken]
    have := maxBeta_abs' (x := x) ((fvar e.fresh).subst e)
    simp [Term.abs', maxBeta, bind, subst, fresh, weaken] at this
    sorry
  | .app (.abs e₁) e₂ => by
    simp [Term.abs', maxBeta]
    sorry
  | .app e₁ e₂ => sorry
  -/
  -/

theorem maxBeta.max : M ▷β M' → M' ▷β maxBeta M
  | .β h₁ h₂ => sorry -- .subst (max h₂) (max h₁)
  | .var => .var
  | .abs (x := x) h => /-show _ ▷β maxBeta (Term.abs _) from by
    unfold maxBeta
    dsimp
    apply Eq.mp (congrArg ..) <| BetaParallel.abs (x := x) (max h)
    apply congrArg Term.abs
    sorry-/
    sorry
  | .app h₁ h₂ =>
    match h₁ with
    | .β h₁ h₁' => .app (max (.β h₁ h₁')) (max h₂)
    | .var => .app (max .var) (max h₂)
    | .app h₁ h₁' => .app (max (.app h₁ h₁')) (max h₂)
    | .abs h₁ => .β (max h₁) (max h₂)

theorem diamond (h₁ : e ▷β e₁) (h₂ : e ▷β e₂) : ∃ e', e₁ ▷β e' ∧ e₂ ▷β e' :=
  ⟨maxBeta e, maxBeta.max h₁, maxBeta.max h₂⟩

theorem diamond' (h₁ : e ▷β* e₁) (h₂ : e ▷β* e₂) : ∃ e', e₁ ▷β* e' ∧ e₂ ▷β* e' := by
  induction h₁ generalizing e₂ with
  | base h₁ =>
    rename_i e₁
    suffices ∃ e', e₁ ▷β* e' ∧ e₂ ▷β e' from
      let ⟨e', he, he'⟩ := this
      ⟨e', he, .base he'⟩
    induction h₂ generalizing e₁ with
    | base h₂ =>
      let ⟨e₁, he₁, he₁'⟩ := diamond h₁ h₂
      exact ⟨_, .base he₁, he₁'⟩
    | refl => exact ⟨_, .refl, h₁⟩
    | trans _ _ diamond'_h₂ diamond'_h₂' =>
      let ⟨e₁, he₁, he₁'⟩ := diamond'_h₂ h₁
      let ⟨e₂, he₂, he₂'⟩ := diamond'_h₂' he₁'
      exact ⟨e₂, .trans he₁ he₂, he₂'⟩
  | refl => exact ⟨e₂, h₂, .refl⟩
  | trans _ _ diamond'_h₁ diamond'_h₁' =>
    let ⟨e₁, he₁, he₁'⟩ := diamond'_h₁ h₂
    let ⟨e₂, he₂, he₂'⟩ := diamond'_h₁' he₁
    exact ⟨e₂, he₂, .trans he₁' he₂'⟩

theorem betaConfluence (h₁ : e ↠β e₁) (h₂ : e ↠β e₂) : ∃ e', e₁ ↠β e' ∧ e₂ ↠β e' :=
  let ⟨e', h₁', h₂'⟩ := BetaParallel.diamond' (BetaParallel.clos₁ h₁) (BetaParallel.clos₁ h₂)
  ⟨e', BetaParallel.clos₂ h₁', BetaParallel.clos₂ h₂'⟩

end Confluence

end Term
