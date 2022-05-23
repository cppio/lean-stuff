import tactic.ext
import tactic.suggest

namespace lambda
namespace simply
section

variable B : Type

@[derive decidable_eq]
inductive type
| base (n : B)
| fn (a b : type)

namespace type

@[pattern]
def o := type.base ()

protected def repr : type unit → string
| (base ()) := "o"
| (fn a b) := "(" ++ a.repr ++ " → " ++ b.repr ++ ")"

instance has_repr : has_repr (type unit) := ⟨type.repr⟩

protected def repr' : type ℕ → string
| (base n) := "?" ++ repr n
| (fn a b) := "(" ++ a.repr' ++ " → " ++ b.repr' ++ ")"

instance has_repr' : has_repr (type ℕ) := ⟨type.repr'⟩

variable {B}

def default : type B → type unit
| (base _) := o
| (fn a b) := fn a.default b.default

def contains (n : B) : type B → Prop
| (base n') := n' = n
| (fn a b) := a.contains ∨ b.contains

variable [decidable_eq B]

instance {n : B} : decidable_pred (contains n)
| (base n') := (infer_instance : decidable_eq B) n' n
| (fn a b) := @or.decidable _ _ (contains.decidable_pred a) (contains.decidable_pred b)

def subst (n : B) (a : type B) : type B → type B
| (base n') := if n' = n then a else base n'
| (fn a b) := fn a.subst b.subst

lemma subst_not_contains {n : B} {a} : ∀ {b}, ¬contains n b → subst n a b = b
| (base _) h := if_neg h
| (fn a b) h := let h := not_or_distrib.mp h in congr_arg2 _ (subst_not_contains h.left) (subst_not_contains h.right)

def subst_all : list (B × type B) → type B → type B
| [] := id
| ((n, a)::xs) := subst_all xs ∘ subst n a

def unify : type B → type B → option (list (B × type B))
| (base n₁) (base n₂) :=
  if n₁ = n₂
  then some []
  else some [(n₂, base n₁)]
| (base n) (fn a b) :=
  if (fn a b).contains n
  then none
  else some [(n, fn a b)]
| (fn a b) (base n) :=
  if (fn a b).contains n
  then none
  else some [(n, fn a b)]
| (fn a₁ b₁) (fn a₂ b₂) := do
  l₁ ← unify a₁ a₂,
  l₂ ← unify (b₁.subst_all l₁) (b₂.subst_all l₁),
  some $ l₁ ++ l₂

#eval unify (fn (fn (fn (fn (fn (base 0) $ base 1) $ base 2) $ base 3) $ base 4) $ base 5) (fn (base 0) $ fn (base 1) $ fn (base 2) $ fn (base 3) $ fn (base 4) $ base 5)

lemma unify_subst {a₁ a₂ : type B} {l} (h : unify a₁ a₂ = some l) : a₁.subst_all l = a₂.subst_all l :=
begin
  unfold unify at h,
  induction a₁,
  case type.base : n₁ {
    cases a₂,
    case type.base : n₂ {
      unfold unify' at h,
      by_cases h' : n₁ = n₂; simp [h'] at h; cases h,
      rw h',
      simp [subst_all, subst],
    },
    case type.fn : a₂ b₂ {
      unfold unify' at h,
      by_cases h' : contains n₁ (a₂.fn b₂); simp [h'] at h; cases h,
      simp [subst_all, subst, subst_not_contains h'],
    },
  },
  case type.fn : a₁ b₁ ha₁ hb₁ {
    induction a₂,
    case type.base : n₂ {
      unfold unify' at h,
      by_cases h' : contains n₂ (a₁.fn b₁); simp [h'] at h; cases h,
      simp [subst_all, subst, subst_not_contains h'],
    },
    case type.fn : a₂ b₂ ha₂ hb₂ {
      unfold unify' has_bind.bind at h,
      cases h₁ : unify' (sizeof (a₁.fn b₁) + sizeof (a₂.fn b₂)) a₁ a₂ with l₁; simp [h₁, option.bind] at h,
      contradiction,
      cases h₂ : unify' (sizeof (a₁.fn b₁) + sizeof (a₂.fn b₂)) (b₁.subst_all l₁) (b₂.subst_all l₁) with l₂; simp [h₂, option.bind] at h,
      contradiction,
    },
  }
end


end type

parameter V : Type
variables [decidable_eq B] [decidable_eq V]

def ctx := V → option (type B)

variable {B}

inductive uterm
| var (x : V)
| abs (x : V) (t : uterm)
| app (t₁ t₂ : uterm)

inductive tterm : type B → Type
| var (x : V) (a) : tterm a
| abs (x : V) (a) {b} (t : tterm b) : tterm (type.fn a b)
| app {a b} (t₁ : tterm (type.fn a b)) (t₂ : tterm a) : tterm b

parameter {V}

private lemma map_id {α} : ∀ {o : option α}, o.map id = o
| none := rfl
| (some _) := rfl

private lemma map_comp {α β φ} {f : β → φ} {g : α → β} : ∀ {o : option α}, (o.map g).map f = o.map (f ∘ g)
| none := rfl
| (some _) := rfl

@[reducible]
def ctx.has (x a) (Γ : ctx B) := Γ x = some a
def ctx.add (x a) (Γ : ctx B) : ctx B := λ y, if y = x then some a else Γ y
def ctx.rem (x) (Γ : ctx B) : ctx B := λ y, if y = x then none else Γ y
def ctx.of (x a) : ctx B := λ y, if y = x then some a else none
def ctx.subst (n : B) (a : type B) : ctx B → ctx B := (∘) $ option.map $ type.subst n a
def ctx.subst_all : list (B × type B) → ctx B → ctx B
| [] := id
| ((n, a)::xs) := ctx.subst_all xs ∘ ctx.subst n a
lemma ctx.subst_all' {x} : ∀ {Γ} l : list (B × type B), ctx.subst_all l Γ x = ((∘) $ option.map $ type.subst_all l) Γ x
| _ [] := by simp [ctx.subst_all, type.subst_all, map_id]
| _ ((n, a)::xs) := by simp [ctx.subst_all, type.subst_all, ctx.subst, ctx.subst_all' xs, map_comp]

def ctx.union (Γ₁ Γ₂ : ctx B) : ctx B := λ y, (Γ₁ y).orelse (Γ₂ y)

inductive term : type B → ctx B → Type
| var (x a) {Γ} (h : ctx.has x a Γ) : term a Γ
| abs (x a) {b Γ} (t : term b (ctx.add x a Γ)) : term (type.fn a b) Γ
| app {a b Γ} (t₁ : term (type.fn a b) Γ) (t₂ : term a Γ) : term b Γ

@[simp]
def tterm.to_uterm : ∀ {a : type B}, tterm a → uterm
| _ (tterm.var x a) := uterm.var x
| _ (tterm.abs x a t) := uterm.abs x t.to_uterm
| _ (tterm.app t₁ t₂) := uterm.app t₁.to_uterm t₂.to_uterm

@[simp]
def term.to_tterm : ∀ {a} {Γ : ctx B}, term a Γ → tterm a
| _ _ (term.var x a h) := tterm.var x a
| _ _ (term.abs x a t) := tterm.abs x a t.to_tterm
| _ _ (term.app t₁ t₂) := tterm.app t₁.to_tterm t₂.to_tterm

@[simp]
def term.to_uterm : ∀ {a} {Γ : ctx B}, term a Γ → uterm
| _ _ (term.var x a h) := uterm.var x
| _ _ (term.abs x a t) := uterm.abs x t.to_uterm
| _ _ (term.app t₁ t₂) := uterm.app t₁.to_uterm t₂.to_uterm

@[simp]
lemma term.to_uterm_to_tterm : ∀ {a} {Γ : ctx B} (t : term a Γ), t.to_tterm.to_uterm = t.to_uterm
| _ _ (term.var x a h) := rfl
| _ _ (term.abs x a t) := congr_arg (uterm.abs x) t.to_uterm_to_tterm
| _ _ (term.app t₁ t₂) := congr_arg2 uterm.app t₁.to_uterm_to_tterm t₂.to_uterm_to_tterm

lemma ctx.add_rem {x a} {Γ : ctx B} (h : Γ x = some a) : Γ = (Γ.rem x).add x a :=
begin
  ext y,
  by_cases h' : y = x; simp [ctx.add, ctx.rem, h', h],
end

lemma ctx.subst_add {n a x b} {Γ : ctx B} : (Γ.add x b).subst n a = (Γ.subst n a).add x (type.subst n a b) :=
begin
  ext y,
  by_cases h : y = x; simp [ctx.add, ctx.subst, h],
  refl,
end

lemma ctx.union_add {x a} {Γ Γ' : ctx B} : (Γ.add x a).union Γ' = (Γ.union Γ').add x a :=
begin
  ext y,
  by_cases h : y = x; simp [ctx.add, ctx.union, h],
  refl,
end

def term.add (x a) : ∀ {b} {Γ : ctx B}, Γ x = none → term b Γ → term b (Γ.add x a)
| _ Γ h (term.var y b h') := term.var y b $ by { unfold ctx.has ctx.add at ⊢ h', by_cases h₁ : y = x, cases h₁, rw h at h', contradiction, simp [h₁, h'] }
| _ Γ h (term.abs y b t) := term.abs y b $ by {
  by_cases h₁ : y = x,
  {
    cases h₁,
    apply cast (congr_arg _ _) t,
    ext x',
    unfold ctx.add,
    by_cases h₂ : x' = x; simp [h₂],
  },
  {
    apply cast (congr_arg _ _) (t.add _),
    {
      ext x',
      unfold ctx.add,
      by_cases h₂ : x' = x; by_cases h₃ : x' = y; simp [h₁, ne.symm h₁, h₂, h₃],
    },
    {
      unfold ctx.add,
      simp [ne.symm h₁, h],
    },
  },
}
| _ Γ h (term.app t₁ t₂) := term.app (t₁.add h) (t₂.add h)

def term.union (Γ') : ∀ {a} {Γ : ctx B}, term a Γ → term a (Γ.union Γ')
| _ Γ (term.var x b h) := term.var x b $ by unfold ctx.has ctx.union at h ⊢; rw h; refl
| _ Γ (term.abs x b t) := term.abs x b $ cast (congr_arg _ ctx.union_add) t.union
| _ Γ (term.app t₁ t₂) := term.app t₁.union t₂.union

def term.subst (n a) : ∀ {b} {Γ : ctx B}, term b Γ → term (type.subst n a b) (Γ.subst n a)
| _ _ (term.var x b h) := term.var x (type.subst n a b) $ by unfold ctx.has ctx.subst function.comp at h ⊢; rw h; refl
| _ _ (term.abs x b t) := term.abs x (type.subst n a b) $ cast (congr_arg _ ctx.subst_add) t.subst
| _ _ (term.app t₁ t₂) := term.app t₁.subst t₂.subst

def term.subst_all : ∀ l {b} {Γ : ctx B}, term b Γ → term (b.subst_all l) (Γ.subst_all l)
| [] _ _ t := t
| ((n, a)::xs) _ _ t := (t.subst n a).subst_all xs

@[simp]
def typeck : ∀ {a} Γ : ctx B, tterm a → option (term a Γ)
| _ Γ (tterm.var x a) := if h : Γ.has x a then some $ term.var x a h else none
| _ Γ (tterm.abs x a t) := do t' ← typeck (Γ.add x a) t, some $ term.abs x a t'
| _ Γ (tterm.app t₁ t₂) := do t₁' ← typeck Γ t₁, t₂' ← typeck Γ t₂, some $ term.app t₁' t₂'

private lemma none_bind {α β} (f : α → option β) : none >>= f = none := rfl
private lemma some_bind {α β} (f : α → option β) (x : α) : some x >>= f = f x := rfl
local attribute [simp] none_bind some_bind

theorem typeck.sound : ∀ {a} {Γ : ctx B} {t : tterm a} {t'}, typeck Γ t = some t' → t'.to_tterm = t
| _ Γ (tterm.var x a) t' h := by {
  by_cases h' : Γ.has x a; simp [h'] at h,
  rw ← h,
  refl,
  contradiction,
}
| _ Γ (tterm.abs x a t) t' h := by {
  cases h' : typeck (Γ.add x a) t; simp [h'] at h,
  contradiction,
  rw [← h, ← typeck.sound h'],
  refl,
}
| _ Γ (tterm.app t₁ t₂) t' h := by {
  cases h₁ : typeck Γ t₁; simp [h₁] at h,
  contradiction,
  cases h₂ : typeck Γ t₂; simp [h₂] at h,
  contradiction,
  rw [← h, ← typeck.sound h₁, ← typeck.sound h₂],
  refl,
}

theorem typeck.complete : ∀ {a} {Γ : ctx B} t : term a Γ, typeck Γ t.to_tterm = some t
| _ Γ (term.var x a h) := by simp [h]
| _ Γ (term.abs x a t) := by simp [typeck.complete t]
| _ Γ (term.app t₁ t₂) := by simp [typeck.complete t₁, typeck.complete t₂]

end

variables {V B : Type} [decidable_eq V] [decidable_eq B]

def ctx.default : ctx V B → ctx V unit := (∘) $ option.map type.default

lemma ctx.default_add {a x} {Γ : ctx V B} : (Γ.add x a).default = Γ.default.add x a.default :=
begin
  ext y,
  by_cases h : y = x; simp [ctx.add, ctx.default, h],
  refl,
end

def term.default : ∀ {a} {Γ : ctx V B}, term a Γ → term a.default Γ.default
| _ _ (term.var x b h) := term.var x b.default $ by unfold ctx.has ctx.default function.comp at h ⊢; rw h; refl
| _ _ (term.abs x b t) := term.abs x b.default $ cast (congr_arg _ ctx.default_add) t.default
| _ _ (term.app t₁ t₂) := term.app t₁.default t₂.default

protected def term.repr : ∀ {a} {Γ : ctx string unit}, term a Γ → string
| _ _ (term.var x a _) := "(" ++ x ++ ":" ++ repr a ++ ")"
| _ _ (term.abs x a t) := "(λ" ++ x ++ ":" ++ repr a ++ "." ++ t.repr ++ ")"
| _ _ (term.app t₁ t₂) := "(" ++ t₁.repr ++ " " ++ t₂.repr ++ ")"

instance {a} {Γ : ctx string unit} : has_repr (term a Γ) := ⟨term.repr⟩

private def get' {α} : ∀ {o : option α}, o ≠ none → α
| (some x) h := x
| none h := absurd rfl h

def unify : list V → ctx V B → ctx V B → option (list (B × type B))
| [] _ _ := some []
| (x::xs) Γ₁ Γ₂ :=
  match (Γ₁ x, Γ₂ x) with
  | (none, _) := unify xs Γ₁ Γ₂
  | (_, none) := unify xs Γ₁ Γ₂
  | (some a₁, some a₂) := do
    s ← a₁.unify a₂,
    s' ← unify xs (Γ₁.subst_all s) (Γ₂.subst_all s),
    some $ s ++ s'
  end

lemma unify_comm {Γ₁ Γ₂ : ctx V B} {l s} (h₁ : ∀ x, Γ₁ x = none → x ∉ l) (h₂ : ∀ x, Γ₂ x = none → x ∉ l) (h : unify l Γ₁ Γ₂ = some s) : (Γ₁.union Γ₂).subst_all s = (Γ₂.union Γ₁).subst_all s :=
begin
  ext x,
  simp [ctx.subst_all', ctx.union],
  cases h₁' : Γ₁ x; cases h₂' : Γ₂ x; simp [option.orelse, option.map, option.bind],
  induction s,
  case list.nil {
    unfold type.subst_all id,
  },
  case list.cons {

  },
end

def unify' (l : list V) (Γ₁ Γ₂ : ctx V B) (a₁ a₂ : type B) : option (list (B × type B)) := do
s ← unify l Γ₁ Γ₂,
s' ← (a₁.subst_all s).unify (a₂.subst_all s),
some $ s ++ s'

def typeinf' : ℕ → uterm V → option (ℕ × list V × Σ a (Γ : ctx V ℕ), term a Γ)
| f (uterm.var x) :=
  some ⟨f + 1, [x], _, ctx.of x _, term.var x (type.base f) $ if_pos rfl⟩
| n (uterm.abs x t) :=
  do ⟨f, l, a, Γ, t⟩ ← typeinf' n t,
  some $ if h : Γ x = none
         then ⟨f + 1, l, _, Γ, term.abs x (type.base f) $ term.add x _ h t⟩
         else ⟨f, l, _, Γ.rem x, term.abs x (get' h) $ cast (by { congr, apply ctx.add_rem, cases Γ x, contradiction, unfold get' }) t⟩
| f (uterm.app t₁ t₂) := do
  ⟨f, l₁, a₁, Γ₁, t₁⟩ ← typeinf' f t₁,
  ⟨f, l₂, a₂, Γ₂, t₂⟩ ← typeinf' f t₂,
  s ← unify' (l₁ ++ l₂) Γ₁ Γ₂ a₁ (type.fn a₂ (type.base f)),
  some ⟨f + 1, l₁ ++ l₂, _, (Γ₁.union Γ₂).subst_all s, term.app (t₁.subst_all s) (t₂.subst_all s)⟩

def typeinf (t : uterm V) : option (Σ a (Γ : ctx V unit), term a Γ) :=
(typeinf' 0 t).map $ λ ⟨_, _, a, Γ, t⟩, ⟨a.default, Γ.default, t.default⟩

#eval (option.get (sorry : option.is_some $ typeinf' 0 $ uterm.abs "y" $ uterm.var "x")).snd.fst
#eval (option.get (sorry : option.is_some $ typeinf  $ uterm.abs "z" $ uterm.var "x")).snd.snd

end simply
end lambda
