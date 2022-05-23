import algebra.big_operators
import data.fin.tuple.basic
import data.finset.basic

open_locale big_operators

variables (F : ℕ → Type*) (V W U : Type*)

inductive term
| var : V → term
| app {n} : (fin n → term) → F n → term

namespace term

variables {F V W U}

@[simp]
def subst (σ : V → term F W) : term F V → term F W
| (var x) := σ x
| (app t f) := app (λ i, subst (t i)) f

@[simp]
theorem subst_var : ∀ (t : term F V), subst var t = t
| (var x) := rfl
| (app t f) := by { dsimp, congr, exact funext (λ i, subst_var (t i)), }

@[simp]
def mg (t : term F V) (u : term F W) : Prop :=
∃ σ, t.subst σ = u

@[simp]
def subst.mg (σ : V → term F W) (τ : V → term F U) : Prop :=
∀ t, (subst σ t).mg (subst τ t)

@[simp]
theorem var_mg (σ : V → term F W) : subst.mg var σ :=
λ t, ⟨σ, congr_arg (subst σ) $ subst_var t⟩

end term

/-\===============================================================================\-/

section

variables {F V}

open term

@[simp]
def term.vars : term F V → ℕ
| (var x) := 1
| (app t f) := ∑ i, (t i).vars

@[simp]
def term.apps : term F V → ℕ
| (var x) := 0
| (app t f) := ∑ i, (t i).apps + 1

@[simp]
def term.vars' : term F V → set V
| (var x) := {x}
| (app t f) := set_of $ λ x, ∃ i, x ∈ (t i).vars'

theorem term.vars'_subst {σ : V → term F V} {x} {t : term F V} (h : x ∉ t.vars') (hσ : ∀ {y}, y ≠ x → x ∉ (σ y).vars') : x ∉ (t.subst σ).vars' :=
begin
  induction t,
  case var : y {
    exact hσ (ne.symm h),
  },
  case app : n t f ih {
    intro hi,
    cases hi with i hi,
    exact ih i (h ∘ exists.intro i) hi,
  },
end

@[simp]
def vars' : list (term F V × term F V) → set V
| [] := ∅
| ((t₁, t₂)::tl) := t₁.vars' ∪ t₂.vars' ∪ vars' tl

@[simp]
theorem vars'_append : ∀ ts ts' : list (term F V × term F V), vars' (ts ++ ts') = vars' ts ∪ vars' ts'
| [] ts' := by simp
| ((t₁, t₂)::tl) ts' := by simp; rw vars'_append tl ts'; ac_refl

theorem vars'_zip {n} {t₁ t₂ : fin n → term F V} {x} (h : x ∈ vars' ((list.of_fn t₁).zip (list.of_fn t₂))) : ∃ i, x ∈ (t₁ i).vars' ∪ (t₂ i).vars' :=
begin
  induction n with n ih,
    cases h,
  simp at h,
  cases h,
    exact ⟨0, h⟩,
  specialize ih h,
  cases ih with i ih,
  exact ⟨i.succ, ih⟩,
end

@[simp]
def subst' (σ : V → term F V) : list (term F V × term F V) → list (term F V × term F V) :=
list.map (prod.map (term.subst σ) (term.subst σ))

theorem vars'_subst' {σ : V → term F V} {ts x} (h : x ∉ vars' ts) (hσ : ∀ y, y ≠ x → x ∉ (σ y).vars') : x ∉ vars' (subst' σ ts) :=
begin
  induction ts,
  case nil {
    simp,
  },
  case cons : t tl ih {
    cases t with t₁ t₂,
    simp [not_or_distrib] at h,
    specialize ih h.right,
    simp [not_or_distrib],
    split,
      swap,
      assumption,
    split,
      apply term.vars'_subst h.left.left hσ,
      apply term.vars'_subst h.left.right hσ,
  },
end

instance [decidable_eq V] : ∀ {t : term F V}, decidable_pred t.vars' :=
@term.rec F V (λ t, decidable_pred t.vars') (infer_instance : ∀ x y, decidable (y = x))
  (λ n t f ih x, @fintype.decidable_exists_fintype _ _ (λ i, ih i x) _)

variable [decidable_eq V]

instance {t : term F V} {x : V} : decidable (x ∈ t.vars') :=
(infer_instance : decidable_pred t.vars') x

@[simp]
def replace_in (x) (t : term F V) (σ : V → term F V) (y) := if y = x then t.subst σ else σ y

@[simp]
def replace (x) (t : term F V) := replace_in x t var

theorem subst_replace_in {x t σ} (t' : term F V) (h : x ∉ t'.vars') : subst (replace_in x t σ) t' = subst σ t' :=
begin
  induction t',
  case var : y {
    simp at h,
    simp [ne.symm h],
  },
  case app : n t f ih {
    simp,
    ext i,
    exact ih i (h ∘ exists.intro i),
  },
end

@[simp]
theorem subst_subst_replace {x} {t t' : term F V} {σ} : subst σ (subst (replace_in x t' var) t) = subst (replace_in x t' σ) t :=
begin
  induction t,
  case var : y {
    simp [apply_ite (subst σ)],
  },
  case app : n t f ih {
    simp,
    exact funext ih,
  },
end

variable [∀ n, decidable_eq (F n)]

def unify : list (term F V × term F V) → option (V → term F V)
| [] := some var
| ((var x, var y)::tl) := if x = y then unify tl else replace_in y (var x) <$> (unify $ subst' (replace y (var x)) tl)
| ((var x, t)::tl) := if x ∈ t.vars' then none else replace_in x t <$> (unify $ subst' (replace x t) tl)
| ((t, var x)::tl) := if x ∈ t.vars' then none else replace_in x t <$> (unify $ subst' (replace x t) tl)
| ((@app _ _ n₁ t₁ f₁, @app _ _ n₂ t₂ f₂)::tl) := if h : n₁ = n₂ then if cast (congr_arg F h) f₁ = f₂ then unify $ (list.of_fn t₁).zip (list.of_fn t₂) ++ tl else none else none

@[simp]
def unify' : ℕ → ℕ → list (term F V × term F V) → option (V → term F V)
| v a [] := some var
| (v + 1) a ((var x, var y)::tl) := if x = y then unify' (v + 1) a tl else replace_in y (var x) <$> (unify' v a $ subst' (replace y (var x)) tl)
| (v + 1) a ((var x, t)::tl) := if x ∈ t.vars' then none else replace_in x t <$> (unify' v a $ subst' (replace x t) tl)
| (v + 1) a ((t, var x)::tl) := if x ∈ t.vars' then none else replace_in x t <$> (unify' v a $ subst' (replace x t) tl)
| v (a + 1) ((@app _ _ n₁ t₁ f₁, @app _ _ n₂ t₂ f₂)::tl) := if h : n₁ = n₂ then if cast (congr_arg F h) f₁ = f₂ then unify' v a $ (list.of_fn t₁).zip (list.of_fn t₂) ++ tl else none else none
| _ _ _ := none

@[simp]
lemma unify'_nil : ∀ v a, unify' v a [] = some (@var F V)
| 0 0 := by simp
| 0 (a + 1) := by simp
| (v + 1) 0 := by simp
| (v + 1) (a + 1) := by simp

@[simp]
lemma unify'_var_var (v) : ∀ a x y tl,
  unify' (v + 1) a ((@var F V x, var y)::tl) = if x = y then unify' (v + 1) a tl else replace_in y (var x) <$> (unify' v a $ subst' (replace y (var x)) tl)
| 0 x y tl := by simp
| (a + 1) x y tl := by simp

@[simp]
lemma unify'_var_app (v) : ∀ a x {n} t f tl,
  unify' (v + 1) a ((var x, @app F V n t f)::tl) = if x ∈ (app t f).vars' then none else replace_in x (app t f) <$> (unify' v a $ subst' (replace x (app t f)) tl)
| 0 x n t f tl := by simp
| (a + 1) x n t f tl := by simp

@[simp]
lemma unify'_app_var (v) : ∀ a {n} t f x tl,
  unify' (v + 1) a ((@app F V n t f, var x)::tl) = if x ∈ (app t f).vars' then none else replace_in x (app t f) <$> (unify' v a $ subst' (replace x (app t f)) tl)
| 0 n t f x tl := by simp
| (a + 1) n t f x tl := by simp

@[simp]
lemma unify'_app_app : ∀ v a {n₁} t₁ f₁ {n₂} t₂ f₂ tl,
  unify' v (a + 1) ((@app F V n₁ t₁ f₁, @app F V n₂ t₂ f₂)::tl) = if h : n₁ = n₂ then if cast (congr_arg F h) f₁ = f₂ then unify' v a $ (list.of_fn t₁).zip (list.of_fn t₂) ++ tl else none else none
| 0 a n₁ t₁ f₁ n₂ t₂ f₂ tl := by simp
| (v + 1) a n₁ t₁ f₁ n₂ t₂ f₂ tl := by simp

@[simp]
lemma unify'_var₁ : ∀ a x t tl,
  unify' 0 a ((@var F V x, t)::tl) = none
| 0 x t tl := by simp
| (a + 1) x t tl := by simp

@[simp]
lemma unify'_var₂ : ∀ a t x tl,
  unify' 0 a ((t, @var F V x)::tl) = none
| 0 t x tl := by simp
| (a + 1) (var y) x tl := by simp
| (a + 1) (app t f) x tl := by simp

@[simp]
lemma unify'_app_app' : ∀ v {n₁} t₁ f₁ {n₂} t₂ f₂ tl,
  unify' v 0 ((@app F V n₁ t₁ f₁, @app F V n₂ t₂ f₂)::tl) = none
| 0 n₁ t₁ f₁ n₂ t₂ f₂ tl := by simp
| (v + 1) n₁ t₁ f₁ n₂ t₂ f₂ tl := by simp

@[simp]
def list.sum' : list ℕ → ℕ
| [] := 0
| (x::xs) := xs.sum' + x

@[simp]
def unify (ts : list (term F V × term F V)) : option (V → term F V) :=
unify' (ts.map $ λ t : term F V × term F V, t.fst.vars + t.snd.vars).sum' (ts.map $ λ t : term F V × term F V, t.fst.apps).sum' ts

example : unify [] = some (@var F V) := by simp
example (x y tl) : unify ((@var F V x, var y)::tl) = if x = y then unify tl else replace_in y (var x) <$> (unify $ subst' (replace y (var x)) tl) :=
begin
  simp,
  by_cases hxy : x = y; simp [hxy],
end
example (x) {n} (t f tl) : unify ((var x, @app F V n t f)::tl) = if x ∈ (app t f).vars' then none else replace_in x (app t f) <$> (unify $ subst' (replace x (app t f)) tl) :=
begin
  simp [add_comm 1, ← add_assoc],
  by_cases hi : (∃ (i : fin n), x ∈ (t i).vars'); simp [hi, function.comp],
  refl,
end
/-
| (v + 1) a ((var x, t)::tl) := if x ∈ t.vars' then none else replace_in x t <$> (unify' v a $ subst' (replace x t) tl)
| (v + 1) a ((t, var x)::tl) := if x ∈ t.vars' then none else replace_in x t <$> (unify' v a $ subst' (replace x t) tl)
| v (a + 1) ((@app _ _ n₁ t₁ f₁, @app _ _ n₂ t₂ f₂)::tl) := if h : n₁ = n₂ then if cast (congr_arg F h) f₁ = f₂ then unify' v a $ (list.of_fn t₁).zip (list.of_fn t₂) ++ tl else none else none
-/

/-
lemma unify'_not_in_vars : ∀ {v a ts} {σ : V → term F V} (h : unify' v a ts = some σ) {x} (hx : x ∉ vars' ts), σ x = var x
| v a [] σ h x hx := by simp at h; subst h
| (v + 1) a ((var y, var z)::tl) σ h x hx := by {
  simp [not_or_distrib] at hx,
  by_cases hyz : y = z; simp [hyz] at h,
    exact unify'_not_in_vars h hx.right,
  cases h with σ' h,
  cases h with h h',
  subst h',
  have := unify'_not_in_vars h (vars'_subst' hx.right _),
  simp [this, hx.left.left],
  intros w hwx,
  by_cases hwz : w = z; simp [hwz],
    exact hx.left.right,
  exact hwx.symm,
}
| (v + 1) a ((var y, @app _ _ n t f)::tl) σ h x hx := by {
  simp [not_or_distrib] at hx,
  by_cases hy : (∃ (i : fin n), y ∈ (t i).vars'); simp [hy] at h,
    contradiction,
  cases h with σ' h,
  cases h with h h',
  subst h',
  have := unify'_not_in_vars h (vars'_subst' hx.right _),
  simp [this, hx.left.left],
  intros w hwx,
  by_cases hwy : w = y; simp [hwy],
    exact hx.left.right,
  exact hwx.symm,
}
| (v + 1) a ((@app _ _ n t f, var y)::tl) σ h x hx := by {
  simp [not_or_distrib] at hx,
  by_cases hy : (∃ (i : fin n), y ∈ (t i).vars'); simp [hy] at h,
    contradiction,
  cases h with σ' h,
  cases h with h h',
  subst h',
  have := unify'_not_in_vars h (vars'_subst' hx.right _),
  simp [this, hx.left.left],
  intros w hwx,
  by_cases hwy : w = y; simp [hwy],
    exact hx.left.right,
  exact hwx.symm,
}
| v (a + 1) ((@app _ _ n₁ t₁ f₁, @app _ _ n₂ t₂ f₂)::tl) σ h x hx := by {
  simp [not_or_distrib] at hx,
  by_cases hn : n₁ = n₂; simp [hn] at h,
    swap,
    contradiction,
  subst hn,
  simp at h,
  by_cases hf : f₁ = f₂; simp [hf] at h,
    swap,
    contradiction,
  subst hf,
  apply unify'_not_in_vars h,
  simp [not_or_distrib],
  split,
   swap,
   exact hx.right,
  intro h',
  replace h' := vars'_zip h',
  cases h' with i h',
  cases h',
    exact hx.left.left i h',
    exact hx.left.right i h',
}
| 0 a ((var y, t)::tl) σ h x hx := by simp at h; cases h
| 0 a ((t, var y)::tl) σ h x hx := by simp at h; cases h
| v 0 ((app t₁ f₁, app t₂ f₂)::tl) σ h x hx := by simp at h; cases h
-/

@[simp]
theorem list.of_fn_inj {α n} {f g : fin n → α} : list.of_fn f = list.of_fn g ↔ f = g :=
begin
  split,
  intro h,
  induction n with n ih,
    exact funext fin.elim0,
  simp at h,
  funext i,
  apply @fin.cases _ (λ i, f i = g i),
    exact h.left,
  apply congr_fun (ih h.right),
  intro h,
  subst h,
end

lemma unify'_eq : ∀ {v a ts} {σ : V → term F V} (h : unify' v a ts = some σ), ts.map (λ t, t.fst.subst σ) = ts.map (λ t, t.snd.subst σ)
| v a [] σ h := rfl
| (v + 1) a ((var x, var y)::tl) σ h := by {
  by_cases hxy : x = y; simp [hxy] at ⊢ h,
    exact unify'_eq h,
  cases h with σ' h,
  cases h with h h',
  subst h',
  simp,
  have := unify'_eq h,
  simp [function.comp] at this,
  exact this,
}
| (v + 1) a ((var x, app t f)::tl) σ h := by {
  by_cases hi : (∃ i, x ∈ (t i).vars'); simp [hi] at h,
    contradiction,
  cases h with σ' h,
  cases h with h h',
  subst h',
  simp,
  split,
    have := subst_replace_in (app t f) hi,
    simp at this,
    exact this.symm,
  have := unify'_eq h,
  simp [function.comp] at this,
  exact this,
}
| (v + 1) a ((app t f, var x)::tl) σ h := by {
  by_cases hi : (∃ i, x ∈ (t i).vars'); simp [hi] at h,
    contradiction,
  cases h with σ' h,
  cases h with h h',
  subst h',
  simp,
  split,
    have := subst_replace_in (app t f) hi,
    simp at this,
    exact this,
  have := unify'_eq h,
  simp [function.comp] at this,
  exact this,
}
| v (a + 1) ((@app _ _ n₁ t₁ f₁, @app _ _ n₂ t₂ f₂)::tl) σ h := by {
  simp at h,
  by_cases hn : n₁ = n₂; simp [hn] at h,
    swap,
    contradiction,
  subst hn,
  by_cases hf : f₁ = f₂; simp [hf] at h,
    swap,
    contradiction,
  subst hf,
  have := unify'_eq h,
  simp at this,
  replace this := list.append_inj' this _,
    swap,
    simp,
  cases this with this this',
  simp,
  split,
  {
    rw ← list.map_map at this,
    rw list.map_fst_zip at this,
    rw ← list.map_map _ prod.snd at this,
    rw list.map_snd_zip at this,
    simp at this,
    exact this,
    simp,
    simp,
  },
  exact this',
}
| 0 a ((var y, t)::tl) σ h := by simp at h; cases h
| 0 a ((t, var y)::tl) σ h := by simp at h; cases h
| v 0 ((app t₁ f₁, app t₂ f₂)::tl) σ h := by simp at h; cases h

theorem unify_eq {ts} {σ : V → term F V} (h : unify ts = some σ) : ts.map (λ t, t.fst.subst σ) = ts.map (λ t, t.snd.subst σ) :=
unify'_eq h

theorem unify_mg {ts : list (term F V × term F V)} {σ : V → term F V} (h : ts.map (λ t, t.fst.subst σ) = ts.map (λ t, t.snd.subst σ)) : ∃ σ', unify ts = some σ' ∧ subst.mg σ' σ :=
begin
  induction ts,
  case nil {
    simp,
  },
  case cons : t tl ih {
    cases t with t₁ t₂,
    cases t₁,
    case var : x {
      cases t₂,
      case var : y {
        by_cases hxy : x = y; simp [hxy] at h ⊢,
          simp at ih,
          apply ih,
      },
    },
  },
end

end

/-\===============================================================================\-/

private def join' : ∀ {n}, (fin (n + 1) → string) → string
| 0 t := t 0
| (n + 1) t := fin.cons_induction (λ hd tl, hd ++ ", " ++ join' tl) t

private def join : ∀ {n}, (fin n → string) → string
| 0 t := ""
| (n + 1) t := "(" ++ join' t ++ ")"

protected def term.repr [∀ n, has_repr (F n)] [has_repr V] : term F V → string :=
@term.rec F V (λ t, string) repr (λ n t f t', repr f ++ join t')

instance [∀ n, has_repr (F n)] [has_repr V] : has_repr (term F V) :=
⟨@term.repr F V _ _⟩

/-\===============================================================================\-/

def V' := ℕ

protected def V'.repr (x : V') : string := "?" ++ nat.repr x

instance : has_repr V' := ⟨V'.repr⟩

def F' : ℕ → Type
| 0 := unit
| 2 := unit
| _ := empty

instance : ∀ n, decidable_eq (F' n)
| 0 := punit.decidable_eq
| 2 := punit.decidable_eq
| 1 := empty.decidable_eq
| (n + 3) := empty.decidable_eq

protected def F'.repr : ∀ {n}, F' n → string
| 0 () := "o"
| 2 () := "fn"

instance {n} : has_repr (F' n) := ⟨F'.repr⟩

def var' : ℕ → term F' V' := term.var

def o : term F' V' := term.app (λ n, [].nth_le n.val n.property) ()
def fn (a b : term F' V') : term F' V' := term.app (λ n, [a, b].nth_le n.val n.property) ()

#eval fn (fn (var' 0) o) (fn o (var' 1))

def L := fn (var' 0) (var' 1)
def R := fn (var' 1) o

#eval (unify [(L, R)]).map (λ σ, L.subst σ)
#eval (unify [(L, R)]).map (λ σ, R.subst σ)
