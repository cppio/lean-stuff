namespace lambda
namespace untyped
section

parameter v : Type*

inductive term
| var : v → term
| abs : v → term → term
| app : term → term → term

namespace term
section

parameter {v}

def vars : term → set v
| (var x) := {x}
| (abs x t) := vars t ∪ {x}
| (app t₁ t₂) := vars t₁ ∪ vars t₂

def fv : term → set v
| (var x) := {x}
| (abs x t) := fv t \ {x}
| (app t₁ t₂) := fv t₁ ∪ fv t₂

def bv : term → set v
| (var x) := ∅
| (abs x t) := bv t ∪ {x}
| (app t₁ t₂) := bv t₁ ∪ bv t₂

inductive rename (x y) : term → term → Prop
| var₁ : rename (var x) (var y)
| var₂ {z} : x ≠ z → rename (var z) (var z)
| abs₁ {t t'} : rename t t' → rename (abs x t) (abs y t')
| abs₂ {z t t'} : x ≠ z → rename t t' → rename (abs z t) (abs z t')
| app {m m' n n'} : rename m m' → rename n n' → rename (app m n) (app m' n')

inductive alpha_eq : term → term → Prop
| var (x) : alpha_eq (var x) (var x)
| abs {t t'} (x) : alpha_eq t t' → alpha_eq (abs x t) (abs x t')
| app {t₁ t₁' t₂ t₂'} : alpha_eq t₁ t₁' → alpha_eq t₂ t₂' → alpha_eq (app t₁ t₂) (app t₁' t₂')
| symm {t₁ t₂} : alpha_eq t₁ t₂ → alpha_eq t₂ t₁
| trans {t₁ t₂ t₃} : alpha_eq t₁ t₂ → alpha_eq t₂ t₃ → alpha_eq t₁ t₃
| alpha {x y t t'} : y ∉ vars t → rename x y t t' → alpha_eq (abs x t) (abs y t')

namespace alpha_eq

lemma refl' : ∀ t, alpha_eq t t
| (term.var x) := var x
| (term.abs x t) := abs x (refl' t)
| (term.app t₁ t₂) := app (refl' t₁) (refl' t₂)

lemma symm' : ∀ {t t'}, alpha_eq t t' → alpha_eq t' t
| _ _ (var x) := var x
| _ _ (abs x h) := abs x (symm' h)
| _ _ (app h₁ h₂) := app (symm' h₁) (symm h₂)
| _ _ (symm h) := h
| _ _ (trans h₁ h₂) := trans (symm' h₂) (symm' h₁)
| _ _ (alpha h₁ h₂) := sorry

end alpha_eq

end
end term

end
end untyped
end lambda

/-
import data.set.basic

namespace term

protected def repr : term string → string
| (var x) := x
| (abs x t) := "(λ" ++ x ++ "." ++ t.repr ++ ")"
| (app t₁ t₂) := "(" ++ t₁.repr ++ " " ++ t₂.repr ++ ")"

instance : has_repr (term string) := ⟨term.repr⟩

variable {v}

instance fv.decidable_pred [decidable_eq v] : ∀ t, decidable_pred (λ x : v, x ∈ fv t)
| (var x) y :=
  if h : y = x
  then is_true h
  else is_false h
| (abs x t) y :=
  if h : y = x
  then is_false $ flip and.right h
  else
    match fv.decidable_pred t y with
    | is_true h' := is_true ⟨h', h⟩
    | is_false h' := is_false $ h' ∘ and.left
    end
| (app t₁ t₂) y :=
  match fv.decidable_pred t₁ y with
  | is_true h := is_true $ or.inl h
  | is_false h :=
    match fv.decidable_pred t₂ y with
    | is_true h' := is_true $ or.inr h'
    | is_false h' := is_false $ not_or h h'
    end
  end

variables (x x' : v)

inductive subst : term v → term v → Prop
| var : subst (var x) (var x')
| var' {x₁} : x ≠ x₁ → subst (var x₁) (var x₁)
| abs {t₁} : subst (abs x t₁) (abs x t₁)
| abs' {x₁ t₁ t₁'} : x ≠ x₁ → x ∉ fv t₁ ∨ x' ≠ x₁ → subst t₁ t₁' → subst (abs x₁ t₁) (abs x₁ t₁')
| app {t₁ t₂ t₁' t₂'} : subst t₁ t₁' → subst t₂ t₂' → subst (app t₁ t₂) (app t₁' t₂')

def subst' [decidable_eq v] : term v → term v
| (var x₁) := if x = x₁ then var x' else var x₁
| (abs x₁ t₁) := if x = x₁ then abs x₁ t₁ else abs x₁ (subst' t₁)
| (app t₁ t₂) := app (subst' t₁) (subst' t₂)

lemma subst_of_subst' [decidable_eq v] : ∀ {t}, x' ∉ bv t → subst x x' t (subst' x x' t)
| (var x₁) _ :=
  by {
    by_cases h : x = x₁; simp [subst', h],
    exact subst.var,
    exact subst.var' h,
  }
| (abs x₁ t₁) h :=
  by {
    by_cases h' : x = x₁; simp [subst', h'],
    exact subst.abs,
    have := not_or_distrib.mp h,
    apply subst.abs' h' (or.inr this.right) (subst_of_subst' this.left),
  }
| (app t₁ t₂) h := let h' := not_or_distrib.mp h in subst.app (subst_of_subst' h'.left) (subst_of_subst' h'.right)

instance [decidable_eq v] : decidable_rel (subst x x')
| (var x₁) (var x₁') :=
  if h₁ : x = x₁
  then
    if h₂ : x' = x₁'
    then is_true $ h₁ ▸ h₂ ▸ subst.var
    else is_false $ λ s, by cases s; tauto
  else
    if h₂ : x₁ = x₁'
    then is_true $ h₂ ▸ subst.var' h₁
    else is_false $ λ s, by cases s; tauto
| (abs x₁ t₁) (abs x₁' t₁') :=
  if h₁ : x₁ = x₁'
  then
    if h₂ : x = x₁
    then
      if h₃ : t₁ = t₁'
      then is_true $ h₁ ▸ h₂ ▸ h₃ ▸ subst.abs
      else is_false $ λ s, by cases s; tauto
    else
      match subst.decidable_rel t₁ t₁' with
      | is_true h₃ :=
        if h₄ : x' = x₁
        then
          if h₅ : x ∈ t₁.fv
          then is_false $ λ s, by clear _match; cases s; tauto
          else is_true $ h₁ ▸ subst.abs' h₂ (or.inl h₅) h₃
        else is_true $ h₁ ▸ subst.abs' h₂ (or.inr h₄) h₃
      | is_false h₃ := is_false $ λ s, by clear _match; cases s; tauto
      end
  else is_false $ λ s, by cases s; tauto
| (app t₁ t₂) (app t₁' t₂') :=
  match subst.decidable_rel t₁ t₁' with
  | is_true h₁ :=
    match subst.decidable_rel t₂ t₂' with
    | is_true h₂ := is_true $ subst.app h₁ h₂
    | is_false h₂ := is_false $ λ s, by cases s; tauto
    end
  | is_false h₁ := is_false $ λ s, by cases s; tauto
  end
| (var _) (abs _ _) := is_false $ λ s, by cases s
| (var _) (app _ _) := is_false $ λ s, by cases s
| (abs _ _) (var _) := is_false $ λ s, by cases s
| (abs _ _) (app _ _) := is_false $ λ s, by cases s
| (app _ _) (var _) := is_false $ λ s, by cases s
| (app _ _) (abs _ _) := is_false $ λ s, by cases s

namespace subst

variables {x x'}

lemma unique : ∀ {t₁ t₂ t₃}, subst x x' t₁ t₂ → subst x x' t₁ t₃ → t₂ = t₃
| _ _ _ var var := rfl
| _ _ _ (var' _) (var' _) := rfl
| _ _ _ abs abs := rfl
| _ _ _ (abs' _ _ h₁) (abs' _ _ h₂) := congr_arg _ (h₁.unique h₂)
| _ _ _ (app h₁ h₂) (app h₁' h₂') := congr_arg2 _ (h₁.unique h₁') (h₂.unique h₂')
| _ _ _ var (var' h) := absurd rfl h
| _ _ _ (var' h) var := absurd rfl h
| _ _ _ abs (abs' h _ _) := absurd rfl h
| _ _ _ (abs' h _ _) abs := absurd rfl h

lemma not_free (h : x ≠ x') : ∀ {t₁ t₁'}, subst x x' t₁ t₁' → x ∉ t₁'.fv
| _ _ var := h
| _ _ (var' h₁) := h₁
| _ _ abs := flip and.right rfl
| _ _ (abs' _ _ h₁) := h₁.not_free ∘ and.left
| _ _ (app h₁ h₂) := not_or h₁.not_free h₂.not_free

lemma eq_of_not_free : ∀ {t₁ t₂}, x ∉ fv t₁ → subst x x' t₁ t₂ → t₁ = t₂
| _ _ h var := absurd rfl h
| _ _ _ (var' _) := rfl
| _ _ _ abs := rfl
| _ _ h (abs' h₁ _ h₂) := congr_arg _ (h₂.eq_of_not_free (h ∘ flip and.intro h₁))
| _ _ h (app h₁ h₂) := let h' := not_or_distrib.mp h in congr_arg2 _ (h₁.eq_of_not_free h'.left) (h₂.eq_of_not_free h'.right)

lemma free : ∀ {t₁ t₂}, x ∈ fv t₁ → subst x x' t₁ t₂ → x' ∈ fv t₂
| _ _ _ var := rfl
| _ _ h (var' h₁) := absurd h h₁
| _ _ h abs := absurd rfl h.right
| _ _ h (abs' h₁ h₂ h₃) := ⟨h₃.free h.left, h₂.resolve_left $ not_not_intro h.left⟩
| _ _ h (app h₁ h₂) := h.elim (or.inl ∘ flip free h₁) (or.inr ∘ flip free h₂)

variable [decidable_eq v]

lemma refl₁ : ∀ t, subst x x t t
| (term.var x₁) := if h : x = x₁ then h ▸ var else var' h
| (term.abs x₁ _) := if h : x = x₁ then h ▸ abs else abs' h (or.inr h) (refl₁ _)
| (term.app _ _) := app (refl₁ _) (refl₁ _)

lemma refl₂ : ∀ {t}, x ∉ fv t → subst x x' t t
| (term.var _) h := var' h
| (term.abs x₁ t) h := if h₁ : x = x₁ then h₁ ▸ abs else let h₂ := not_and'.mp h h₁ in abs' h₁ (or.inl h₂) (refl₂ h₂)
| (term.app _ _) h := app (refl₂ (h ∘ or.inl)) (refl₂ (h ∘ or.inr))

-- FIXME: classical.choice
theorem eq_fv : ∀ {t₁ t₂}, x' ∉ fv t₁ → subst x x' t₁ t₂ → t₁.fv \ {x} = t₂.fv \ {x'}
| _ _ _ var := by simp
| _ _ h (var' h₁) := by { simp, skip, dsimp at h; simp [h, h₁], }
| _ _ h abs := by dsimp at h; simp [h]
| _ _ h (@abs' _ x x' x₁ t₁ t₁' h₁ h₂ h₃) :=
  by {
    cases h₂,
    dsimp at h, simp [← h₃.eq_of_not_free h₂, h, h₂],
    simp [set.diff_diff_comm, h₃.eq_fv (h ∘ flip and.intro h₂)],
  }
| _ _ h (app h₁ h₂) := by dsimp at h; rw not_or_distrib at h; simp [set.union_diff_distrib, h₁.eq_fv h.left, h₂.eq_fv h.right]

lemma symm : ∀ {t₁ t₂}, x' ∉ fv t₁ → subst x x' t₁ t₂ → subst x' x t₂ t₁
| _ _ _ var := var
| _ _ h (var' _) := var' h
| _ _ h abs :=
  if h₁ : x' = x
  then h₁.symm ▸ abs
  else let h₂ := h ∘ flip and.intro h₁ in abs' h₁ (or.inl h₂) (refl₂ h₂)
| _ _ h (abs' h₁ h₂ h₃) :=
  if h₄ : x' = _
  then h₃.unique (refl₂ (h₂.neg_resolve_right h₄)) ▸ h₄ ▸ abs
  else abs' h₄ (or.inr h₁) (h₃.symm $ h ∘ flip and.intro h₄)
| _ _ h (app h₁ h₂) := app (h₁.symm $ h ∘ or.inl) (h₂.symm $ h ∘ or.inr)

lemma trans : ∀ {x' x'' t₁ t₂ t₃}, x' ∉ fv t₁ → subst x x' t₁ t₂ → subst x' x'' t₂ t₃ → subst x x'' t₁ t₃
| _ _ _ _ _ _ var var := var
| _ _ _ _ _ _ (var' h) (var' _) := var' h
| _ _ _ _ _ _ abs abs := abs
| _ _ _ _ _ h abs (abs' h₁ _ h₂) := eq_of_not_free (not_and'.mp h h₁) h₂ ▸ abs
| _ _ _ _ _ h (abs' h₁ h₂ h₃) abs := let h' := h₂.resolve_right (absurd rfl) in abs' h₁ (or.inl h') (h₃.eq_of_not_free h' ▸ refl₂ h')
| _ _ _ _ _ h (abs' h₁ h₂ h₃) (abs' h₁' h₂' h₃') := abs' h₁ (h₂.elim or.inl $ λ h₂, h₂'.symm.elim or.inr $ λ h₂', or.inl $ h₂' ∘ flip free h₃) (h₃.trans (not_and'.mp h h₁') h₃')
| _ _ _ _ _ h (app h₁ h₂) (app h₁' h₂') := let h' := not_or_distrib.mp h in app (h₁.trans h'.left h₁') (h₂.trans h'.right h₂')
| _ _ _ _ _ _ var (var' h) := absurd rfl h
| _ _ _ _ _ h (var' _) var := absurd rfl h

end subst

inductive alpha_eq : term v → term v → Prop
| var (x) : alpha_eq (var x) (var x)
| abs {t t'} (x) : alpha_eq t t' → alpha_eq (abs x t) (abs x t')
| app {t₁ t₂ t₁' t₂'} : alpha_eq t₁ t₁' → alpha_eq t₂ t₂' → alpha_eq (app t₁ t₂) (app t₁' t₂')
| subst {x x' t t'} : x ≠ x' → x' ∉ fv t → subst x x' t t' → alpha_eq (abs x t) (abs x' t')
| trans {t t' t''} : alpha_eq t t' → alpha_eq t' t'' → alpha_eq t t''

namespace alpha_eq

lemma is_var {x : v} {t'} (h : alpha_eq (term.var x) t') : ∃ x', t' = term.var x' :=
@alpha_eq.rec _ (λ t t', ∀ x : v, t = term.var x → ∃ x', t' = term.var x')
  (λ _ _ _, ⟨_, rfl⟩)
  (λ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ h₁ h₂ _ h₁', let ⟨_, h₂'⟩ := h₁ _ h₁' in h₂ _ h₂')
  _ _ h _ rfl

lemma is_abs {x : v} {t₁ t'} (h : alpha_eq (term.abs x t₁) t') : ∃ x' t₁', t' = term.abs x' t₁' :=
@alpha_eq.rec _ (λ t t', ∀ (x : v) t₁, t = term.abs x t₁ → ∃ x' t₁', t' = term.abs x' t₁')
  (λ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ _, ⟨_, _, rfl⟩)
  (λ _ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ _ _ _, ⟨_, _, rfl⟩)
  (λ _ _ _ _ _ h₁ h₂ _ _ h₁', let ⟨_, _, h₂'⟩ := h₁ _ _ h₁' in h₂ _ _ h₂')
  -- (λ _ _ _ _ _ h₁ h₂ _ h₁', let ⟨_, h₂'⟩ := h₁ _ h₁' in h₂ _ h₂')
  _ _ h _ _ rfl

lemma is_app {t₁ t₂ t' : term v} (h : alpha_eq (term.app t₁ t₂) t') : ∃ t₁' t₂', t' = term.app t₁' t₂' :=
@alpha_eq.rec _ (λ t t', ∀ t₁ t₂ : term v, t = term.app t₁ t₂ → ∃ t₁' t₂', t' = term.app t₁' t₂')
  (λ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ _ _ _ _, ⟨_, _, rfl⟩)
  (λ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ h₁ h₂ _ _ h₁', let ⟨_, _, h₂'⟩ := h₁ _ _ h₁' in h₂ _ _ h₂')
  _ _ h _ _ rfl

lemma of_app₁ {t₁ t₂ t₁' t₂' : term v} (h : alpha_eq (term.app t₁ t₂) (term.app t₁' t₂')) : alpha_eq t₁ t₁' :=
@alpha_eq.rec _ (λ t t', ∀ t₁ t₂ t₁' t₂' : term v, t = term.app t₁ t₂ → t' = term.app t₁' t₂' → alpha_eq t₁ t₁')
  (λ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ h₁ _ _ _ _ _ _ _ h₂ h₃, cast (congr_arg2 _ (app.inj h₂).left (app.inj h₃).left) h₁)
  (λ _ _ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ t t' _ h _ h₁ h₂ t₁ t₂ _ _ h₁' h₃', let ⟨_, _, h₂'⟩ := is_app (cast (h₁' ▸ rfl : t.alpha_eq t' = (t₁.app t₂).alpha_eq t') h) in trans (h₁ _ _ _ _ h₁' h₂') (h₂ _ _ _ _ h₂' h₃'))
  _ _ h _ _ _ _ rfl rfl

lemma of_app₂ {t₁ t₂ t₁' t₂' : term v} (h : alpha_eq (term.app t₁ t₂) (term.app t₁' t₂')) : alpha_eq t₂ t₂' :=
@alpha_eq.rec _ (λ t t', ∀ t₁ t₂ t₁' t₂' : term v, t = term.app t₁ t₂ → t' = term.app t₁' t₂' → alpha_eq t₂ t₂')
  (λ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ _ h₁ _ _ _ _ _ _ h₂ h₃, cast (congr_arg2 _ (app.inj h₂).right (app.inj h₃).right) h₁)
  (λ _ _ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ t t' _ h _ h₁ h₂ t₁ t₂ _ _ h₁' h₃', let ⟨_, _, h₂'⟩ := is_app (cast (h₁' ▸ rfl : t.alpha_eq t' = (t₁.app t₂).alpha_eq t') h) in trans (h₁ _ _ _ _ h₁' h₂') (h₂ _ _ _ _ h₂' h₃'))
  _ _ h _ _ _ _ rfl rfl

lemma refl : ∀ {t : term v}, alpha_eq t t
| (term.var _) := var _
| (term.abs _ _) := abs _ refl
| (term.app _ _) := app refl refl

variable [decidable_eq v]

lemma of_abs {x : v} {t₁ t₁'} (h : alpha_eq (term.abs x t₁) (term.abs x t₁')) : alpha_eq t₁ t₁' :=
@alpha_eq.rec _ (λ t t', ∀ (x : v) t₁ t₁', t = term.abs x t₁ → t' = term.abs x t₁' → alpha_eq t₁ t₁')
  (λ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ h₁ _ _ _ _ h₂ h₃, cast (congr_arg2 _ (abs.inj h₂).right (abs.inj h₃).right) h₁)
  (λ _ _ _ _ _ _ _ _ _ _ _ h, term.no_confusion h)
  (λ _ _ _ _ h₁ _ _ _ _ _ h₂ h₃, absurd ((abs.inj h₂).left.trans (abs.inj h₃).left.symm) h₁)
  (λ A B C D E F G H I J K L, let ⟨x', _, M⟩ := is_abs (cast (K ▸ rfl : A.alpha_eq B = (term.abs H I).alpha_eq B) D) in by {
    by_cases this : x' = H,
      rw this at M,
      exact trans (F _ _ _ K M) (G _ _ _ M L),
    rw K at D,
    rw L at E,
    clear _let_match,
    cases D,
    exact absurd (abs.inj M).left.symm this,
    case subst : _ _ _ _ _ h₁' h₁ {
      cases E,
      exact absurd (abs.inj M).left.symm this,
      case subst subst : _ _ _ _ _ _ h₂ {
        rw (subst.refl₁ _).unique (h₁.trans h₁' h₂),
        exact refl,
      },
      sorry,
    },
    sorry,
  })
  _ _ h _ _ _ rfl rfl

/-
lemma symm : ∀ {t t' : term v}, alpha_eq t t' → alpha_eq t' t
| _ _ (var _) := var _
| _ _ (abs _ h) := abs _ h.symm
| _ _ (app h₁ h₂) := app h₁.symm h₂.symm
| _ _ (subst h₁ h₂ h₃) := subst h₁.symm (h₃.not_free h₁) (h₃.symm h₂)
-/

lemma symm {t t' : term v} : alpha_eq t t' → alpha_eq t' t :=
@alpha_eq.rec _ (flip alpha_eq)
  (λ _, refl)
  (λ _ _ _ _, abs _)
  (λ _ _ _ _ _ _, app)
  (λ _ _ _ _ h₁ h₂ h₃, subst h₁.symm (h₃.not_free h₁) (h₃.symm h₂))
  (λ _ _ _ _ _, flip trans)
  _ _

/-
lemma eq_fv : ∀ {t t' : term v}, alpha_eq t t' → t.fv = t'.fv
| _ _ (var _) := rfl
| _ _ (abs x h) := (λ _, congr_arg (λ s : set v, s \ {x}) h.eq_fv) ()
| _ _ (app h₁ h₂) := congr_arg2 _ h₁.eq_fv h₂.eq_fv
| _ _ (subst _ h₁ h₂) := h₂.eq_fv h₁
-/

lemma eq_fv {t t' : term v} : alpha_eq t t' → t.fv = t'.fv :=
@alpha_eq.rec _ (λ t t', t.fv = t'.fv)
  (λ _, rfl)
  (λ _ _ x _, congr_arg (λ s : set v, s \ {x}))
  (λ _ _ _ _ _ _, congr_arg2 _)
  (λ _ _ _ _ _, subst.eq_fv)
  (λ _ _ _ _ _, eq.trans)
  _ _

/-
lemma trans : ∀ {t t' t'' : term v}, alpha_eq t t' → alpha_eq t' t'' → alpha_eq t t''
| _ _ _ (var _) (var _) := var _
| _ _ _ (abs _ h) (abs _ h') := abs _ (h.trans h')
| _ _ _ (app h₁ h₂) (app h₁' h₂') := app (h₁.trans h₁') (h₂.trans h₂')
| _ _ _ (@alpha_eq.abs _ x₁ t₁ t₂ h₁) (@alpha_eq.subst _ x₁' x₂' t₁' t₂' h₁' h₂' h₃') := alpha_eq.subst sorry sorry sorry
| _ _ _ (@alpha_eq.subst _ x₁ x₂ t₁ t₂ h₁ h₂ h₃) (@alpha_eq.subst _ x₂' x₃ t₁' t₂' h₁' h₂' h₃') :=
  let this := h₃.trans h₂ h₃' in
  if h' : x₁ = x₃
  then (h'.subst this).unique (subst.refl₁ _) ▸ h' ▸ alpha_eq.refl
  else alpha_eq.subst h' sorry this
-/

end alpha_eq

variable [decidable_eq v]

instance : decidable_rel (@alpha_eq v)
| (var x) (var x') :=
  if h : x = x'
  then is_true $ h ▸ alpha_eq.refl
  else is_false $ mt alpha_eq.eq_fv $ λ h', h (@eq.subst _ id _ _ (@congr_fun _ _ _ _ h' x) rfl)
| (abs x t) (abs x' t') :=
  if h₁ : x = x'
  then match alpha_eq.decidable_rel t t' with
       | is_true h₂ := is_true $ h₁ ▸ alpha_eq.abs _ h₂
       | is_false h₂ := is_false $ λ h', h₂ (h₁.subst h').of_abs
       end
  else sorry
| (app t₁ t₂) (app t₁' t₂') :=
  match alpha_eq.decidable_rel t₁ t₁' with
  | is_true h₁ := match alpha_eq.decidable_rel t₂ t₂' with
                  | is_true h₂ := is_true $ alpha_eq.app h₁ h₂
                  | is_false h := is_false $ λ h', by { cases h', contradiction, case : _ h₁ h₂ { rcases h₁.is_app with ⟨_, _, ⟨⟩⟩, exact h (h₁.trans h₂).of_app₂ } }
                  end
  | is_false h := is_false $ λ h', by { cases h', contradiction, case : _ h₁ h₂ { rcases h₁.is_app with ⟨_, _, ⟨⟩⟩, exact h (h₁.trans h₂).of_app₁ } }
  end
| (var _) (abs _ _) := is_false $ λ h, by cases h.is_var; contradiction
| (var _) (app _ _) := is_false $ λ h, by cases h.is_var; contradiction
| (abs _ _) (var _) := is_false $ λ h, by rcases h.is_abs with ⟨_, _, _⟩; contradiction
| (abs _ _) (app _ _) := is_false $ λ h, by rcases h.is_abs with ⟨_, _, _⟩; contradiction
| (app _ _) (var _) := is_false $ λ h, by rcases h.is_app with ⟨_, _, _⟩; contradiction
| (app _ _) (abs _ _) := is_false $ λ h, by rcases h.is_app with ⟨_, _, _⟩; contradiction

def αterm (v) [decidable_eq v] := quotient ⟨@alpha_eq v, @alpha_eq.refl _, @alpha_eq.symm _ _, @alpha_eq.trans _⟩

-- #reduce (infer_instance : decidable_eq (αterm v))

end term

end untyped

end lambda

/-
inductive eta : term α → term α → Prop
| mk (x : α) (t : term α) : x ∉ t.fv → eta (abs x (app t (var x))) t

lemma eta.fv {t s : term α} (h : eta t s) : t.fv = s.fv :=
by cases h; simp *
-/
-/
