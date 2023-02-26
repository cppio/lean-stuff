import Std
import Common

def Nat.le_add_right_of_le {m n k : Nat} (h : m ≤ n) : m ≤ n + k :=
  Nat.le_trans h (Nat.le_add_right n k)

def Nat.le_add_left_of_le {m n k : Nat} (h : m ≤ n) : m ≤ k + n :=
  Nat.le_trans h (Nat.le_add_left n k)

section cast

variable {α : Sort u} {β : α → Sort v} {γ : α → Sort w}

@[simp]
theorem cast_cast (h : α = α') (h' : α' = α'') (x : α) : h' ▸ h ▸ x = h.trans h' ▸ x :=
  by cases h; rfl

@[simp]
theorem cast_cast' (h : x = x') (h' : x' = x'') (y : β x) : h' ▸ h ▸ y = h.trans h' ▸ y :=
  by cases h; rfl

@[simp]
theorem cast_inj (h : x = x') {y y' : β x} : h ▸ y = h ▸ y' ↔ y = y' :=
  by cases h; exact ⟨id, id⟩

theorem cast_to_cast (h : x = x') (y : β x) : h ▸ y = congrArg β h ▸ y :=
  by cases h; rfl

@[simp]
theorem cast_app (f : ∀ x, β x → γ x) {x} (y : β x) {x'} (h : x = x') : f x' (h ▸ y) = h ▸ f x y :=
  by cases h; rfl

theorem cast_swap (hx : x = x') {y : β x} {y' : β x'} (h : hx ▸ y = y') : y = hx ▸ y' :=
  by cases hx; cases h; rfl

end cast

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
  | bvar (d := .succ d) n => Var.toString (d - n.val)
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

@[simp]
theorem weaken_weaken (hd₁ : d₁ ≤ d₂) (hd₂ : d₂ ≤ d₃) : (e : Term d₁) → weaken hd₂ (weaken hd₁ e) = weaken (Nat.le_trans hd₁ hd₂) e
  | fvar _ => rfl
  | bvar _ => rfl
  | abs e => congrArg abs (weaken_weaken (Nat.succ_le_succ hd₁) (Nat.succ_le_succ hd₂) e)
  | app e₁ e₂ => congrArg₂ app (weaken_weaken hd₁ hd₂ e₁) (weaken_weaken hd₁ hd₂ e₂)

variable (x : Var) in
def bind : Term d → Term d.succ
  | fvar y => if y = x then bvar .last else fvar y
  | bvar n => bvar n.castSucc
  | abs e => abs e.bind
  | app e₁ e₂ => app e₁.bind e₂.bind

def abs' (x : Var) (e : Term) : Term :=
  abs (e.bind x)

/-
theorem bind_bind (h : bind x e = bind y e') (hx : x ≠ z) (hy : y ≠ z) : bind x (bind z e) = bind y (bind z e') := by
  induction e with
  | fvar w =>
    cases e'
      <;> unfold bind at h
      <;> split at h
      <;> (try split at h)
      <;> simp at h
      <;> cases h
      <;> simp! [*]
    split <;> simp! [*]
  | bvar n =>
    cases e'
      <;> unfold bind at h
      <;> (try split at h)
      <;> simp at h
    cases h
    rfl
  | abs e he =>
    cases e'
      <;> unfold bind at h
      <;> (try split at h)
      <;> simp at h
    simp! [he h]
  | app e₁ e₂ he₁ he₂ =>
    cases e'
      <;> unfold bind at h
      <;> (try split at h)
      <;> simp at h
    simp! [he₁ h.1, he₂ h.2]
-/

variable (e' : Term) in
def subst : Term d.succ → Term d :=
  subst
where
  subst {d' d} : Term d' → Term d
  | fvar x => fvar x
  | bvar n => if h : n < d then bvar ⟨n, h⟩ else e'.weaken d.zero_le
  | abs e => abs (subst e)
  | app e₁ e₂ => app (subst e₁) (subst e₂)

theorem subst_weaken (h : d ≤ d') (e : Term d) : subst e' (weaken (.step h) e) = weaken h e :=
  match e with
  | fvar _ => rfl
  | bvar n => by
    dsimp [weaken, Fin.castLe, subst, subst.subst]
    have : (n : Nat) < _ := Nat.le_trans n.2 h
    simp [this]
  | abs e => congrArg abs (subst_weaken (Nat.succ_le_succ h) e)
  | app e₁ e₂ => congrArg₂ app (subst_weaken h e₁) (subst_weaken h e₂)

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

theorem bind_free (h : e.free x) : bind x e = e.weaken (.step .refl) :=
  match e with
  | fvar _ => if_neg h
  | bvar _ => rfl
  | abs _ => congrArg abs <| bind_free h
  | app .. => congrArg₂ app (bind_free h.1) (bind_free h.2)

theorem bind_subst (h : e.free x) : bind x (subst (fvar x) e) = e :=
  match e with
  | fvar _ => if_neg h
  | bvar n => by
    unfold subst subst.subst
    split
    . rfl
    next h =>
      simp [weaken, bind]
      exact Nat.pred_le_pred n.2 |> Nat.eq_or_lt_of_le |>.resolve_right h |>.symm
  | abs _ => congrArg abs (bind_subst h)
  | app .. => congrArg₂ app (bind_subst h.1) (bind_subst h.2)

theorem free_weaken (hd : d ≤ d') : (e : Term d) → e.free x ↔ (e.weaken hd).free x
  | fvar _ => ⟨id, id⟩
  | bvar _ => ⟨id, id⟩
  | abs e => free_weaken (Nat.succ_le_succ hd) e
  | app e₁ e₂ => ⟨λ h => ⟨free_weaken hd e₁ |>.mp h.1, free_weaken hd e₂ |>.mp h.2⟩, λ h => ⟨free_weaken hd e₁ |>.mpr h.1, free_weaken hd e₂ |>.mpr h.2⟩⟩

theorem free_bind : (e : Term d) → e.free x → (e.bind y).free x
  | fvar _, h => by
    unfold bind
    split
    . trivial
    . exact h
  | bvar _, h => h
  | abs e, h => free_bind e h
  | app e₁ e₂, h => ⟨free_bind e₁ h.1, free_bind e₂ h.2⟩

theorem free_bind' : (e : Term d) → (e.bind x).free x
  | fvar _ => by
    unfold bind
    split
    . trivial
    . assumption
  | bvar _ => .intro
  | abs e => free_bind' e
  | app e₁ e₂ => ⟨free_bind' e₁, free_bind' e₂⟩

theorem of_free_bind (e : Term d) (h : (e.bind y).free x) : e.free x ∨ y = x :=
  match e with
  | fvar z => by
    unfold bind at h
    split at h
    next h' =>
      cases h'
      exact Classical.em _ |>.symm
    . exact .inl h
  | bvar n => .inl h
  | abs e => of_free_bind e h
  | app e₁ e₂ =>
    match of_free_bind e₁ h.1 with
    | .inr h₁ => .inr h₁
    | .inl h₁ =>
      match of_free_bind e₂ h.2 with
      | .inr h₂ => .inr h₂
      | .inl h₂ => .inl ⟨h₁, h₂⟩

variable {e' : Term} (h' : free x e') in
theorem free_subst : (e : Term (.succ d)) → e.free x → (e'.subst e).free x
  | fvar _, h => h
  | bvar _, h => by
    unfold subst subst.subst
    split
    . assumption
    . exact free_weaken d.zero_le e' |>.mp h'
  | abs e, h => free_subst e h
  | app e₁ e₂, h => ⟨free_subst e₁ h.1, free_subst e₂ h.2⟩

def fresh : Term d → Var
  | fvar x => x.succ
  | bvar _ => .zero
  | abs e => e.fresh
  | app e₁ e₂ => e₁.fresh.max e₂.fresh

def fresh' (es : Fin k → Term d) : Var :=
  match k with
  | 0 => .zero
  | _ + 1 => es .zero |>.fresh.max <| fresh' (es ·.succ')

variable (x : Var) in
theorem free_fresh (h : e.fresh.le x) : free x e :=
  match e with
  | fvar x => Nat.ne_of_lt h
  | bvar n => trivial
  | abs e => free_fresh (e := e) h
  | app e₁ e₂ => ⟨free_fresh <| Nat.le_trans (Nat.le_max_left ..) h, free_fresh <| Nat.le_trans (Nat.le_max_right ..) h⟩

variable (x : Var) in
theorem free_fresh' {es : Fin k → Term d} (h : fresh' es |>.le x) i : free x (es i) := by
  induction k with
  | zero => exact nomatch i
  | succ k ih =>
    cases i using Fin.cases with
    | zero => exact free_fresh x <| Nat.le_trans (Nat.le_max_left ..) h
    | succ i => exact ih (Nat.le_trans (Nat.le_max_right ..) h) i

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

def bindAll (xs : Fin k → Var) {d} (e : Term d) : Term (d + k) :=
  @Fin.rdfoldl k _ (λ k => Term (d + k)) (λ _ e x => bind x e) e xs

def substAll (es : Fin k → Term) {d} (e : Term (d + k)) : Term d :=
  @Fin.rdfoldr k _ (λ k => Term (d + k)) (λ _ e' => subst e') e es

theorem substAll_bindAll {xs : Fin k → Var} {d} {e : Term d} : substAll (fvar <| xs ·) (bindAll xs e) = e := by
  unfold substAll bindAll
  induction k with
  | zero => rfl
  | succ _ ih => dsimp; rw [subst_bind]; exact ih

theorem bindAll_eq_bind_bindAll {xs : Fin (.succ k) → Var} {e : Term d} : bindAll xs e = bind (xs .last) (bindAll (xs ·.castSucc) e) := rfl

theorem bindAll_eq_bindAll_bind {xs : Fin (.succ k) → Var} {e : Term d} : bindAll xs e = (d.succ_add k ▸ bindAll (xs ·.succ') (bind (xs .zero) e) :) := by
  rw [bindAll, ← Fin.dfoldl_eq_rdfoldl]
  dsimp
  rw [Fin.dfoldl_eq_rdfoldl, cast_to_cast]
  refine Fin.rdfoldl_ext (congrArg @Term <| .symm <| d.succ_add ·) ?_ rfl _
  intro i _ _
  rw [← cast_to_cast]
  rw [← @cast_to_cast Nat (Term ·.succ)]
  exact cast_app _ _ <| d.succ_add i

theorem bind_bindAll {xs : Fin k → Var} {e : Term d} : bind x (bindAll xs e) = bindAll (Fin.rcases xs x) e :=
  by simp [bindAll]

theorem bindAll_bind {xs : Fin k → Var} {e : Term d} : bindAll xs (bind x e) = Nat.succ_add .. ▸ bindAll (Fin.cases x xs) e :=
  cast_swap _ <| .symm bindAll_eq_bindAll_bind

@[simp]
theorem bindAll_bvar {xs : Fin k → Var} {n : Fin d} : bindAll xs (bvar n) = bvar (n.castAdd k) := by
  unfold bindAll
  induction k with
  | zero => rfl
  | succ _ ih => exact congrArg _ ih

@[simp]
theorem bindAll_abs {xs : Fin k → Var} {e : Term (.succ d)} : bindAll xs (abs e) = abs (Nat.succ_add .. ▸ bindAll xs e) := by
  unfold bindAll
  induction k with
  | zero => rfl
  | succ _ ih => apply congrArg _ ih |>.trans; simp [bind]; rw [cast_to_cast, @cast_to_cast _ (Term <| .succ ·)]

@[simp]
theorem bindAll_app {xs : Fin k → Var} {e₁ e₂ : Term d} : bindAll xs (app e₁ e₂) = app (bindAll xs e₁) (bindAll xs e₂) := by
  unfold bindAll
  induction k with
  | zero => rfl
  | succ _ ih => exact congrArg _ ih

@[simp]
theorem bindAll_fvar_ne_abs {xs : Fin k → Var} {e : Term (d + k).succ} : bindAll xs (fvar x) ≠ abs e := by
  unfold bindAll
  induction k with
  | zero => intro h; cases h
  | succ _ ih =>
    rw [Fin.rdfoldl]
    generalize he' : Fin.rdfoldl .. = e'
    cases e'
      <;> (try unfold bind; split)
      <;> intro h
      <;> cases h
    exact ih he'

@[simp]
theorem abs_ne_bindAll_fvar {xs : Fin k → Var} {e : Term (d + k).succ} : abs e ≠ bindAll xs (fvar x) :=
  bindAll_fvar_ne_abs.symm

@[simp]
theorem bindAll_fvar_ne_app {xs : Fin k → Var} {e₁ e₂ : Term (d + k)} : bindAll xs (fvar x) ≠ app e₁ e₂ := by
  unfold bindAll
  induction k with
  | zero => intro h; cases h
  | succ _ ih =>
    rw [Fin.rdfoldl]
    generalize he' : Fin.rdfoldl .. = e'
    cases e'
      <;> (try unfold bind; split)
      <;> intro h
      <;> cases h
    exact ih he'

@[simp]
theorem app_ne_bindAll_fvar {xs : Fin k → Var} {e₁ e₂ : Term (d + k)} : app e₁ e₂ ≠ bindAll xs (fvar x) :=
  bindAll_fvar_ne_app.symm

@[simp]
theorem bindAll_fvar_ne_bvar_castAdd {xs : Fin k → Var} {n : Fin d} : bindAll xs (fvar x) ≠ bvar (n.castAdd k) := by
  unfold bindAll
  induction k generalizing d n with
  | zero => intro h; cases h
  | succ _ ih =>
    rw [Fin.rdfoldl]
    generalize he' : Fin.rdfoldl .. = e'
    cases e'
      <;> (try unfold bind; split)
      <;> intro h
      <;> (try cases h)
      <;> simp [bind] at h
    . cases Nat.ne_of_lt (Nat.le_trans n.2 <| d.le_add_right _) h.symm
    . exact ih <| he'.trans <| congrArg bvar <| Fin.eq_of_val_eq h

@[simp]
theorem bvar_castAdd_ne_bindAll_fvar {xs : Fin k → Var} {n : Fin d} : bvar (n.castAdd k) ≠ bindAll xs (fvar x) :=
  bindAll_fvar_ne_bvar_castAdd.symm

theorem substAll_eq_substAll_subst {es : Fin (.succ k) → Term} {e : Term (d + k).succ} : substAll es e = substAll (es ·.castSucc) (subst (es .last) e) := rfl

theorem substAll_eq_subst_substAll {es : Fin (.succ k) → Term} {e : Term (d + k).succ} : substAll es e = subst (es .zero) (substAll (es ·.succ') (d.succ_add k ▸ e)) := by
  rw [substAll, ← Fin.dfoldr_eq_rdfoldr]
  dsimp
  congr
  rw [Fin.dfoldr_eq_rdfoldr, cast_to_cast]
  rw [substAll]
  refine Fin.rdfoldr_ext (congrArg @Term <| .symm <| d.succ_add ·) ?_ (by simp) _
  intro i _ _
  rw [← @cast_to_cast Nat (Term ·.succ)]
  rw [← cast_to_cast]
  exact cast_app (@Term.subst _) _ <| d.succ_add i

theorem substAll_subst {es : Fin k → Term} {e : Term (d + k).succ} : substAll es (subst e' e) = substAll (Fin.rcases es e') e :=
  by simp [substAll]

theorem subst_substAll {es : Fin k → Term} {e : Term (.succ d + k)} : subst e' (substAll es e) = substAll (Fin.cases e' es) (d.succ_add k ▸ e : Term (d + k).succ) := by
  have := @substAll_eq_subst_substAll _ _ (Fin.cases e' es) (d.succ_add k ▸ e)
  simp at this
  exact this.symm

@[simp]
theorem substAll_fvar {es : Fin k → Term} : substAll es (fvar x : Term (d + k)) = fvar x := by
  unfold substAll
  induction k with
  | zero => rfl
  | succ _ ih => exact ih

@[simp]
theorem substAll_bvar_castAdd {es : Fin k → Term} {n : Fin d} : substAll es (bvar (n.castAdd k)) = bvar n := by
  unfold substAll
  induction k with
  | zero => rfl
  | succ _ ih =>
    simp [subst, subst.subst, show (n : Nat) < _ from Nat.le_trans n.2 <| d.le_add_right _]
    exact ih

@[simp]
theorem substAll_abs {es : Fin k → Term} {e : Term (d + k).succ} : substAll es (abs e) = abs (substAll es (Nat.succ_add .. ▸ e)) := by
  unfold substAll
  induction k with
  | zero => rfl
  | succ _ ih =>
    apply ih.trans ∘ .symm
    simp
    congr
    rw [cast_to_cast]
    rw [← @cast_to_cast Nat (Term ·.succ)]
    apply @cast_app Nat (Term ·.succ)

@[simp]
theorem substAll_app {es : Fin k → Term} {e₁ e₂ : Term (d + k)} : substAll es (app e₁ e₂) = app (substAll es e₁) (substAll es e₂) := by
  unfold substAll
  induction k with
  | zero => rfl
  | succ _ ih => exact ih

theorem free_bindAll {xs : Fin k → Var} {e : Term d} (h : free x e) : free x (bindAll xs e) := by
  induction k with
  | zero => exact h
  | succ _ ih =>
    rw [bindAll_eq_bind_bindAll]
    exact free_bind _ ih

theorem free_substAll {es : Fin k → Term} {e : Term (d + k)} (h' : ∀ i, free x (es i)) (h : free x e) : free x (substAll es e) := by
  induction k generalizing d with
  | zero => exact h
  | succ _ ih =>
    rw [substAll_eq_subst_substAll]
    apply free_subst (h' .zero)
    apply ih (h' ·.succ')
    simp
    exact h

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
  abs := ReflexiveTransitiveClosure.map' (Congruence.abs ·)
  app₁ := ReflexiveTransitiveClosure.map' (Congruence.app₁ ·)
  app₂ := ReflexiveTransitiveClosure.map' (Congruence.app₂ ·)

instance EquivalenceClosure.instCongruence [Congruence r] : Congruence (EquivalenceClosure r) where
  abs := EquivalenceClosure.map' (Congruence.abs ·)
  app₁ := EquivalenceClosure.map' (Congruence.app₁ ·)
  app₂ := EquivalenceClosure.map' (Congruence.app₂ ·)

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
  .trans (.base <| .app₁ <| .base .β') <|
  .trans (.base <| .base .β') <|
  Reflexive.ofEq <|
  congrArg₂ app weaken_refl <| congrArg₂ app rfl weaken_refl

def Y := reduce%
  abs' "f" <| (abs' "x" <| app "f" (app "x" "x")) (abs' "x" <| app "f" (app "x" "x"))

#eval Y

example : Y f =β f (Y f) :=
  .trans (.base <| .base .β') <|
  .trans (.base <| .base .β') <|
  flip .trans (.symm <| .base <| .app₂ <| .base .β') <|
  Reflexive.ofEq <|
  congrArg₂ app subst_weaken <| congrArg₂ app weaken_refl weaken_refl
-/

namespace Confluence

inductive BetaParallel : Term → Term → Prop
  | β : BetaParallel e₁ e₁' → BetaParallel e₂ e₂' → BetaParallel (app (abs' x e₁) e₂) (e₂'.subst (e₁'.bind x))
  | var : BetaParallel (fvar x) (fvar x)
  | abs : BetaParallel e e' → BetaParallel (abs' x e) (abs' x e')
  | app : BetaParallel e₁ e₁' → BetaParallel e₂ e₂' → BetaParallel (app e₁ e₂) (.app e₁' e₂')

infix:50 " ▷β " => BetaParallel
infix:50 " ▷β* " => ReflexiveTransitiveClosure BetaParallel

namespace BetaParallel

theorem abs' (hx : e.free x) (hx' : e'.free x) (h : (fvar x).subst e ▷β (fvar x).subst e') : .abs e ▷β .abs e' :=
  bind_subst hx ▸ bind_subst hx' ▸ abs h

theorem abs'' (h : let x := fvar (e.fresh.max e'.fresh); x.subst e ▷β x.subst e') : .abs e ▷β .abs e' :=
  abs' (free_fresh _ <| Nat.le_max_left ..) (free_fresh _ <| Nat.le_max_right ..) h

theorem refl : ∀ {e}, BetaParallel e e
  | fvar x => var
  | .abs e =>
    have := Nat.le_trans (sizeOf_subst_fvar (e.fresh.max e.fresh) e) <| Nat.le_add_left _ 1
    abs'' refl
  | .app .. => app refl refl

theorem ofBetaReduction : e →β e' → e ▷β e'
  | .base .β => β refl refl
  | .abs h => abs (ofBetaReduction h)
  | .app₁ h => app (ofBetaReduction h) refl
  | .app₂ h => app refl (ofBetaReduction h)

theorem toBetaReduction : e ▷β e' → e ↠β e'
  | β h₁ h₂ => .trans (.trans (Congruence.app₁ <| Congruence.abs <| toBetaReduction h₁) (Congruence.app₂ <| toBetaReduction h₂)) (.base <| .base .β)
  | var => .refl
  | abs h => Congruence.abs <| toBetaReduction h
  | app h₁ h₂ => .trans (Congruence.app₁ <| toBetaReduction h₁) (Congruence.app₂ <| toBetaReduction h₂)

theorem multiOfBetaReduction : e ↠β e' → e ▷β* e' :=
  .map' (r := CongruenceClosure _) ofBetaReduction

theorem multiToBetaReduction : e ▷β* e' → e ↠β e' :=
  .map (r := BetaParallel) toBetaReduction

end BetaParallel

inductive MaxBeta : Term → Term → Prop
  | β : MaxBeta e₁ e₁' → MaxBeta e₂ e₂' → MaxBeta (app (abs' x e₁) e₂) (e₂'.subst (e₁'.bind x))
  | var : MaxBeta (fvar x) (fvar x)
  | abs : MaxBeta e e' → MaxBeta (abs' x e) (abs' x e')
  | app : (∀ e₁', e₁ ≠ abs e₁') → MaxBeta e₁ e₁' → MaxBeta e₂ e₂' → MaxBeta (app e₁ e₂) (.app e₁' e₂')

/-
@[simp]
theorem cast_cast {α : Sort u} {β : α → Sort v} {x₁ x₂ x₃ : α} (h₁ : x₁ = x₂) (h₂ : x₂ = x₃) (y : β x₁) : h₂ ▸ h₁ ▸ y = h₁.trans h₂ ▸ y := by
  subst_eqs
  rfl

theorem cast_cast' {α : Sort u} {α' : Sort v} {β : α → Sort w} {β' : α' → Sort w} {x₁ x₂ : α} {x₂' x₃' : α'} (h₁ : x₁ = x₂) (h : β x₂ = β' x₂') (h₂ : x₂' = x₃') (y : β x₁) : h₂ ▸ h ▸ h₁ ▸ y = (congrArg β h₁ |>.trans h |>.trans (congrArg β' h₂)) ▸ y := by
  subst_eqs
  rfl
-/

theorem _root_.Term.bindAll_weaken_eq {l l' : Fin k → Var} {e e' : Term d} (h : e.bindAll l = e'.bindAll l') (hd : d ≤ d') : bindAll l (weaken hd e) = bindAll l' (weaken hd e') := by
  induction e generalizing d'
    <;> cases e'
    <;> simp at h
    <;> (try cases h)
    <;> simp! [*]
  case fvar =>
    clear d hd
    rename_i d x y
    induction k generalizing d d' with
    | zero => cases h; rfl
    | succ k ih =>
      simp [bindAll_eq_bindAll_bind, bind] at h ⊢
      split
        <;> split
        <;> simp [*] at h
      . simp
      . exact ih h
  case abs ih _ => exact ih h _
  case app ih₁ ih₂ _ _ h₁ h₂ => exact ⟨ih₁ h₁ _, ih₂ h₂ _⟩

theorem _root_.Term.bindAll_eq_of_weaken {l l' : Fin k → Var} {e e' : Term d} (hd : d ≤ d') (h : bindAll l (weaken hd e) = bindAll l' (weaken hd e')) : bindAll l e = bindAll l' e' := by
  induction e generalizing d'
    <;> cases e'
    <;> simp! at h
    <;> (try cases h)
    <;> simp [*]
  case fvar.bvar n => cases bindAll_fvar_ne_bvar_castAdd (n := n.castLe hd) h
  case bvar.fvar n _ => cases bvar_castAdd_ne_bindAll_fvar (n := n.castLe hd) h
  case fvar =>
    clear d hd
    rename_i d x y
    induction k generalizing d d' with
    | zero => cases h; rfl
    | succ k ih =>
      simp [bindAll_eq_bindAll_bind, bind] at h ⊢
      split
        <;> split
        <;> simp [*] at h
      . simp
      . exact ih h
  case abs ih _ => exact ih _ h
  case app ih₁ ih₂ _ _ h₁ h₂ => exact ⟨ih₁ _ h₁, ih₂ _ h₂⟩

theorem _root_.Term.bindAll_subst_bind (l l' : Fin k → Var) {e₁ e₁' : Term d} {e₂ e₂' : Term} {x y : Var} (h₁ : bindAll l (e₁.bind x) = bindAll l' (e₁'.bind y)) (h₂ : bindAll l e₂ = bindAll l' e₂') : bindAll l (e₂.subst (e₁.bind x)) = bindAll l' (e₂'.subst (e₁'.bind y)) := by
  induction e₁ with
  | fvar z =>
    cases e₁' with
    | fvar w =>
      dsimp [bind] at h₁ ⊢
      split
        <;> split
        <;> rename_i heq₁ heq₂
        <;> simp [heq₁, heq₂] at h₁
        <;> simp [subst, subst.subst, Fin.last]
      . exact bindAll_weaken_eq h₂ (Nat.zero_le _)
      . exact bindAll_eq_of_weaken (Nat.le_succ _) h₁
    | bvar n =>
      simp! at h₁
      split at h₁
      . simp [Fin.castLe, Fin.last, Nat.ne_of_lt n.2 |>.symm] at h₁
      . cases bindAll_fvar_ne_bvar_castAdd (n := n.castSucc) h₁
    | abs => simp! at h₁; split at h₁ <;> simp at h₁
    | app => simp! at h₁; split at h₁ <;> simp at h₁
  | bvar n =>
    cases e₁' with
    | fvar x =>
      simp! at h₁
      split at h₁
      . simp [Fin.castLe, Fin.last, Nat.ne_of_lt n.2] at h₁
      . cases bindAll_fvar_ne_bvar_castAdd (n := n.castSucc) h₁.symm
    | bvar n' =>
      simp! at h₁
      dsimp [Fin.castLe] at h₁
      cases Fin.eq_of_val_eq h₁
      simp [subst, subst.subst, Fin.castSucc, n.2]
    | abs => simp! at h₁
    | app => simp! at h₁
  | abs _ h =>
    cases e₁' with
    | fvar => simp! at h₁; split at h₁; simp at h₁; have := h₁.symm; simp at this
    | bvar => simp! at h₁
    | abs => simp [bind, subst, subst.subst] at h₁ ⊢; exact h h₁
    | app => simp! at h₁
  | app _ _ h h' =>
    cases e₁' with
    | fvar => simp! at h₁; split at h₁; simp at h₁; have := h₁.symm; simp at this
    | bvar => simp! at h₁
    | abs => simp! at h₁
    | app => simp [bind, subst, subst.subst] at h₁ ⊢; exact ⟨h h₁.1, h' h₁.2⟩

theorem free_beta (h : e.free x) (h' : e →β e') : e'.free x := by
  induction h' with
  | base h' =>
    cases h'
    exact free_subst h.2 _ h.1
  | abs h' ih =>
    cases of_free_bind _ h with
    | inl h' => exact free_bind _ <| ih h'
    | inr h' => cases h'; exact free_bind' _
  | app₁ _ ih => exact ⟨ih h.1, h.2⟩
  | app₂ _ ih => exact ⟨h.1, ih h.2⟩

theorem subst_bind_weaken (hd : d ≤ d') : subst e' (bind x (weaken hd e)) = weaken hd (subst e' (bind x e)) := by
  induction e generalizing d' with
  | fvar =>
    dsimp [weaken, bind]
    split
    . simp [subst, subst.subst]
    . rfl
  | bvar n =>
    dsimp [bind, subst, subst.subst]
    simp [n.2, show n < d' from Nat.le_trans n.2 hd]
    rfl
  | abs _ ih => exact congrArg abs <| ih <| Nat.succ_le_succ hd
  | app _ _ ih₁ ih₂ => exact congrArg₂ app (ih₁ hd) (ih₂ hd)

theorem subst_bind_subst_bind (h : free x e₂) (hx : x ≠ y) : subst e₂ (bind y (subst e₁ (bind x e))) = subst (subst e₂ (bind y e₁)) (bind x (subst e₂ (bind y e))) := by
  induction e with
  | fvar =>
    dsimp [bind]
    split
    . subst_eqs
      simp [hx, bind, subst, subst.subst]
      apply subst_bind_weaken
    . dsimp [bind]
      split
      . simp [subst, subst.subst]
        rw [bind_free <| free_weaken _ e₂ |>.mp h]
        simp
        rw [← subst]
        rw [subst_weaken]
      . simp [*, bind, subst, subst.subst]
  | bvar n => simp [bind, subst, subst.subst, n.2]
  | abs _ ih => exact congrArg abs ih
  | app _ _ ih₁ ih₂ => exact congrArg₂ app ih₁ ih₂

theorem subst_bind_subst_bind' : subst e₂ (bind x (subst e₁ (bind x e))) = subst (subst e₂ (bind x e₁)) (bind x e) := by
  induction e with
  | fvar =>
    dsimp [bind]
    split
    . simp [subst, subst.subst]
      apply subst_bind_weaken
    . simp [subst, subst.subst, bind, *]
  | bvar n => simp [bind, subst, subst.subst, n.2]
  | abs _ ih => exact congrArg abs ih
  | app _ _ ih₁ ih₂ => exact congrArg₂ app ih₁ ih₂

theorem subst_bind_bind (h : x ≠ y) (h' : free x e') : subst e' (bind y (bind x e)) = bind x (subst e' (bind y e)) := by
  induction e with
  | fvar =>
    dsimp!
    split
    . subst_eqs
      simp [h, bind, subst, subst.subst]
    . split
      . simp [bind, *, subst, subst.subst]
        rw [bind_free <| free_weaken (Nat.zero_le _) _ |>.mp h']
        simp
      . simp [bind, *]
        rfl
  | bvar n => simp [bind, subst, subst.subst, n.2, Nat.lt.step n.2]
  | abs _ ih => exact congrArg abs ih
  | app _ _ ih₁ ih₂ => exact congrArg₂ app ih₁ ih₂

example (h : e →β e') : subst e'' (bind x e) →β subst e'' (bind x e') := by
  induction h with
  | @base e e' h =>
    rename_i A B; clear A B
    cases h with | @β y e₁ e₂ =>
    refine .base ?_
    dsimp [abs', bind, subst, subst.subst]
    by_cases y = x
    next h =>
      cases h
      rw [bind_free (free_bind' e₁)]
      rw [← subst, ← subst, ← subst]
      rw [subst_weaken .refl, weaken_refl]
      rw [subst_bind_subst_bind']
      exact .β
    next h =>
      rw [← subst, ← subst, ← subst]
      let z : Var := e₁.fresh.max e''.fresh |>.max x.succ
      have he₁ : free z e₁ := free_fresh z <| Nat.le_trans (Nat.le_max_left ..) <| Nat.le_max_left ..
      have he'' : free z e'' := free_fresh z <| Nat.le_trans (Nat.le_max_right ..) <| Nat.le_max_left ..
      have hx : z ≠ x := Ne.symm <| Nat.ne_of_lt <| Nat.le_max_right ..
      rw [← @bind_subst z _ (bind y e₁) (free_bind _ he₁)]
      rw [subst_bind_bind hx he'']
      conv => rhs; rw [subst_bind_subst_bind he'' hx]
      exact .β
  | @abs y e e' h ih =>
    dsimp [abs', bind, subst, subst.subst]
    rw [← subst]
    let z : Var := e.fresh.max e''.fresh |>.max x.succ
    have he : free z e := free_fresh z <| Nat.le_trans (Nat.le_max_left ..) <| Nat.le_max_left ..
    have he'' : free z e'' := free_fresh z <| Nat.le_trans (Nat.le_max_right ..) <| Nat.le_max_left ..
    have hx : z ≠ x := Ne.symm <| Nat.ne_of_lt <| Nat.le_max_right ..
    rw [← @bind_subst z _ (bind y e) (free_bind _ he)]
    rw [← @bind_subst z _ (bind y e') (free_bind _ <| free_beta he h)]
    rw [subst_bind_bind hx he'']
    rw [subst_bind_bind hx he'']
    refine .abs ?_
    sorry
  | app₁ _ ih => exact .app₁ ih
  | app₂ _ ih => exact .app₂ ih

theorem substAll_bindAll_weaken {xs : Fin k → Var} (hd : d ≤ d') : substAll es (bindAll xs (weaken hd e)) = weaken hd (substAll es (bindAll xs e)) := by
  induction e generalizing d' with
  | fvar =>
    dsimp [weaken]
    induction k generalizing d' with
    | zero => rfl
    | succ k ih =>
      simp [bindAll_eq_bindAll_bind, substAll_eq_subst_substAll, bind]
      split
      . simp [subst, subst.subst]
      . rw [ih hd.step]
        rw [subst_weaken hd]
        congr
        conv => rhs; rw [ih (.step .refl)]
        rw [subst_weaken .refl]
        rw [weaken_refl]
  | bvar n =>
    simp!
    exact substAll_bvar_castAdd (n := n.castLe hd)
  | abs _ ih => simp!; exact ih <| Nat.succ_le_succ hd
  | app _ _ ih₁ ih₂ => simp!; exact ⟨ih₁ hd, ih₂ hd⟩

/-
theorem substAll_bindAll_bind {e : Term d} (hi : ∀ i, (es i).free x) : ((e.bind x).bindAll xs).substAll es = ((e.bindAll xs).substAll es).bind x := by
  induction e with
  | fvar _ =>
    dsimp!
    split
    . simp; sorry
    . apply Eq.symm
      apply Eq.trans
      . apply bind_free
        apply free_substAll hi
        apply free_bindAll
        assumption
      . sorry
  | bvar _ => simp!; sorry
  | abs _ ih => simp!; exact ih
  | app _ _ ih₁ ih₂ => simp!; exact ⟨ih₁, ih₂⟩
-/

example {xs : Fin k → Var} (h : e →β e') : (e.bindAll xs).substAll es →β (e'.bindAll xs).substAll es := by
  induction h generalizing k with
  | @base e e' h =>
    refine .base ?_
    rename_i A B; clear A B
    cases h with | @β x e₁ e₂ =>
    simp [abs']
    induction k generalizing x e₁ e₂ with
    | zero => exact .β
    | succ k ih =>
      simp [bindAll_eq_bindAll_bind, substAll_eq_subst_substAll]
      by_cases xs .zero = x
      next h =>
        cases h
        rw [bind_free <| free_bind' e₁]
        rw [substAll_bindAll_weaken]
        rw [subst_weaken .refl]
        rw [weaken_refl]
        specialize @ih (es ·.succ') (xs ·.succ') (xs .zero) e₁
        sorry
      next h =>
        sorry
    /-
    have := @BetaReduction.β x (e₁.bindAll xs |>.substAll es) (e₂.bindAll xs |>.substAll es)
    dsimp [abs'] at this
    rw [substAll_bindAll_bind]
    sorry
    sorry
    -/
  | @abs x e e' h ih =>
    simp [abs']
    let y := fresh' (Fin.cases e es)
    refine Congruence.abs' (x := y) (free_substAll (free_fresh' y <| Nat.le_max_right ..) <| free_bindAll <| free_bind e <| free_fresh' y .refl .zero) (free_substAll (free_fresh' y <| Nat.le_max_right ..) <| free_bindAll <| free_bind e' <| free_beta (free_fresh' y .refl .zero) h) ?_
    simp [bindAll_bind, subst_substAll]
    sorry
  | app₁ _ ih => simp; exact .app₁ ih
  | app₂ _ ih => simp; exact .app₂ ih

theorem BetaParallel.ofAbs' (h : .abs e ▷β .abs e') : ∃ x, (fvar x).subst e ▷β (fvar x).subst e' := by
  generalize h₁ : Term.abs e = e₁ at h
  generalize h₂ : Term.abs e' = e₂ at h
  cases h with
  | β => cases h₁
  | var => cases h₁
  | app => cases h₁
  | @abs _ _ x =>
  cases h₁
  cases h₂
  apply Exists.intro x
  rw [subst_bind]
  rw [subst_bind]
  assumption

theorem BetaParallel.indep {xs : Fin k → Var} {l l' : Fin k → Term} (hl : ∀ i, l i ▷β l' i) (h : (e.bindAll xs).substAll l ▷β (e'.bindAll xs).substAll l') : e ▷β e' := by
  match e with
  | fvar x =>
    simp only [bindAll_eq_bindAll'] at h
    induction k with
    | zero => exact h
    | succ k ih =>
      dsimp! at h
      specialize @ih (xs ·.castSucc) (l ·.castSucc) (l' ·.castSucc) (hl ·.castSucc)
      sorry
  | .abs e =>
    sorry
  | .app e₁ e₂ =>
    sorry

theorem BetaParallel.ofAbs (h : .abs' x e ▷β .abs' x e') : e ▷β e' := by
  have := ofAbs' h
  clear h
  rename _ => h
  cases h with | _ x' h =>
  exact indep (k := 1) (xs := λ _ => x) (λ _ => var) h

theorem BetaParallel.subst₁ {es es' : Fin k → Term} (he : ∀ i, es i ▷β es' i) (h : e ▷β e') : (e.bindAll xs).substAll es ▷β (e'.bindAll xs).substAll es' := by
  rw [bindAll_eq_bindAll']
  induction k with
  | zero => exact h
  | succ k ih =>
    dsimp!
    sorry

theorem BetaParallel.subst (h₁ : e₁ ▷β e₁') (h₂ : e₂ ▷β e₂') : e₂.subst (e₁.bind x) ▷β e₂'.subst (e₁'.bind x) := by
  dsimp!
  sorry

theorem MaxBeta.indep {l l' : Fin k → Var} (h : e₁.bindAll l = e₂.bindAll l') (h₁ : MaxBeta e₁ e₁') (h₂ : MaxBeta e₂ e₂') : e₁'.bindAll l = e₂'.bindAll l' :=
  match e₁ with
  | fvar x =>
    match e₂ with
    | fvar y =>
      match h₁, h₂ with
      | .var, .var => h
    | .abs _ => by simp at h
    | .app .. => by simp at h
  | .abs e₁ =>
    match e₂ with
    | fvar x => have := h.symm; by simp at this
    | .abs e₂ =>
      match ph₁ : h₁, h₂ with
      | @abs ne₁ e₁' x h₁, @abs e₂ e₂' y h₂ => by
        simp [abs']
        simp [bindAll_bind] at h ⊢
        have : sizeOf ne₁ < 1 + sizeOf e₁ := by
          rename e₁ = _ => pe₁
          rw [pe₁]
          clear k l l' h₁ e₂ e₂' y h₂ pe₁ ph₁ h
          rename_i A B C D
          clear A B C e₂' e₁ h₁ e₂ h₂ e₁' D
          generalize Nat.zero = d at ne₁
          induction ne₁ with
          | fvar => dsimp!; split <;> decreasing_tactic
          | bvar =>
            dsimp!
            dsimp [Fin.castSucc, sizeOf, Fin._sizeOf_1]
            decreasing_tactic
          | abs _ he =>
            dsimp!
            apply Nat.lt_trans
            apply Nat.add_lt_add_left he
            decreasing_tactic
          | app _ _ he₁ he₂ =>
            dsimp!
            apply Nat.le_trans
            apply Nat.add_le_add_left he₂
            apply Nat.le_trans
            rw [Nat.add_assoc]
            apply Nat.add_le_add_left
            apply Nat.add_le_add_right
            rw [Nat.succ_add] at he₁
            exact Nat.le_of_succ_le_succ he₁
            decreasing_tactic
        exact indep (e₁ := ne₁) h h₁ h₂
    | .app .. => by simp at h
  | .app e₁ e₁' =>
    match e₂ with
    | fvar x => have := h.symm; by simp at this
    | .abs _ => by simp at h
    | .app e₂ e₂' =>
      match ph₁ : h₁ with
      | @β A E₁ _ E₂ x ha hb =>
        match h₂ with
        | @β B E₁' _ E₂' y hc hd => by
          simp [abs', bindAll_bind] at h
          apply bindAll_subst_bind l l'
          . have : sizeOf A < 1 + sizeOf e₁ + sizeOf e₁' := by
              rename e₁ = _ => pe₁
              rw [pe₁]
              apply Nat.lt_add_right
              clear k l l' e₁ e₁' h₁ e₂ e₂' h₂ ha hb pe₁ ph₁ B E₁' E₂' y hc hd h
              rename_i A
              clear e₁ e₁' e₂ e₂' E₁ E₂ A
              dsimp [abs']
              suffices ∀ d (A : Term d), sizeOf A < 1 + (1 + sizeOf (bind x A)) from this _ A
              clear A
              intro d A
              induction A with
              | fvar =>
                dsimp!
                split <;> decreasing_tactic
              | bvar =>
                dsimp!
                dsimp [Fin.castSucc, sizeOf, Fin._sizeOf_1]
                decreasing_tactic
              | abs _ he =>
                dsimp!
                apply Nat.lt_trans
                apply Nat.add_lt_add_left he
                decreasing_tactic
              | app _ _ he₁ he₂ =>
                dsimp!
                apply Nat.le_trans
                apply Nat.add_le_add_left he₂
                apply Nat.le_trans
                rw [Nat.add_assoc]
                apply Nat.add_le_add_left
                apply Nat.add_le_add_right
                rw [Nat.succ_add] at he₁
                exact Nat.le_of_succ_le_succ he₁
                decreasing_tactic
            have := indep (e₁ := A) h.1 ha hc
            simp! at this
            exact this
          . exact indep (e₁ := e₁') h.2 hb hd
        | app happ .. =>
          match e₂ with
          | fvar _ => by simp [abs'] at h
          | .abs _ => by cases happ _ rfl
          | .app .. => by simp [abs'] at h
      | app happ ha hb =>
        match h₂ with
        | β .. =>
          match e₁ with
          | fvar _ => by simp [abs'] at h
          | .abs _ => by cases happ _ rfl
          | .app .. => by simp [abs'] at h
        | app _ hc hd => by
          simp at h ⊢
          exact ⟨indep h.1 ha hc, indep h.2 hb hd⟩

theorem MaxBeta.deterministic : MaxBeta e e₁ → MaxBeta e e₂ → e₁ = e₂ :=
  indep (l := Fin.elim) (l' := Fin.elim) rfl

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

theorem maxBeta_abs' : maxBeta (abs' x e) = .abs' x (maxBeta e) := by
  have he₁ := MaxBeta_maxBeta (abs' x e)
  generalize maxBeta _ = e₁ at he₁
  have he₂ := MaxBeta_maxBeta e
  generalize maxBeta e = e₂ at he₂
  exact MaxBeta.deterministic he₁ <| MaxBeta.abs he₂

theorem maxBeta.max (h : M ▷β M') : M' ▷β maxBeta M := by
  induction h with
  | β _ _ ih₁ ih₂ =>
    rename_i e₁ e₁' e₂ e₂' x h₁ h₂
    have her := MaxBeta_maxBeta (app (abs' x e₁) e₂)
    generalize maxBeta _ = er at her
    have : MaxBeta ((app (abs' x e₁) e₂)) (subst (maxBeta e₂) (bind x (maxBeta e₁))) := .β (MaxBeta_maxBeta _) (MaxBeta_maxBeta _)
    cases her.deterministic this
    exact .subst ih₁ ih₂
  | var => exact .var
  | abs h ih => rw [maxBeta_abs']; exact .abs ih
  | app h₁ _ ih₁ ih₂ =>
    match h₁ with
    | .abs h₁ =>
      rename_i A B e₂ e₂' E h₁ e₁ e₁' x
      clear M M' A B E
      rw [maxBeta_abs'] at ih₁
      have her := MaxBeta_maxBeta (app (abs' x e₁) e₂)
      generalize maxBeta _ = er at her
      have : MaxBeta ((app (abs' x e₁) e₂)) (subst (maxBeta e₂) (bind x (maxBeta e₁))) := .β (MaxBeta_maxBeta _) (MaxBeta_maxBeta _)
      cases her.deterministic this
      exact .β (.ofAbs ih₁) ih₂
    | .β .. | .var | .app .. => unfold maxBeta; exact .app ih₁ ih₂

theorem diamond : Diamond BetaParallel := λ h₁ h₂ =>
  ⟨maxBeta _, maxBeta.max h₁, maxBeta.max h₂⟩

theorem betaConfluence (h₁ : e ↠β e₁) (h₂ : e ↠β e₂) : ∃ e', e₁ ↠β e' ∧ e₂ ↠β e' :=
  let ⟨e', h₁', h₂'⟩ := ReflexiveTransitiveClosure.diamond diamond (BetaParallel.multiOfBetaReduction h₁) (BetaParallel.multiOfBetaReduction h₂)
  ⟨e', BetaParallel.multiToBetaReduction h₁', BetaParallel.multiToBetaReduction h₂'⟩

end Confluence

end Term
