import data.list.perm

namespace linear

@[derive decidable_eq]
inductive type
| one
| top
| zero

export type

protected def type.repr : type → string
| one := "one"
| top := "top"
| zero := "zero"

instance : has_repr type := ⟨type.repr⟩

inductive uterm
| var (x : string)
| cut (x : string) (e₁ e₂ : uterm)
| one_intro
| one_elim (e₁ e₂ : uterm)
| top_intro
| zero_elim (e : uterm)

export uterm
  (renaming var → u.var)
  (renaming cut → u.cut)
  (renaming one_intro → u.one_intro)
  (renaming one_elim → u.one_elim)
  (renaming top_intro → u.top_intro)
  (renaming zero_elim → u.zero_elim)

protected def uterm.repr : uterm → string
| (u.var x) := "(var " ++ repr x ++ ")"
| (u.cut x e₁ e₂) := "(cut " ++ repr x ++ " " ++ e₁.repr ++ " " ++ e₂.repr ++ ")"
| u.one_intro := "one_intro"
| (u.one_elim e₁ e₂) := "(one_elim " ++ e₁.repr ++ " " ++ e₂.repr ++ ")"
| u.top_intro := "top_intro"
| (u.zero_elim e) := "(zero_elim " ++ e.repr ++ ")"

instance : has_repr uterm := ⟨uterm.repr⟩

inductive tterm : type → Type
| var (a) (x : string) : tterm a
| cut {a b} (x : string) (e₁ : tterm a) (e₂ : tterm b) : tterm b
| one_intro : tterm one
| one_elim {a} (e₁ : tterm one) (e₂ : tterm a) : tterm a
| top_intro : tterm top
| zero_elim (a) (e : tterm zero) : tterm a

export tterm
  (renaming var → t.var)
  (renaming cut → t.cut)
  (renaming one_intro → t.one_intro)
  (renaming one_elim → t.one_elim)
  (renaming top_intro → t.top_intro)
  (renaming zero_elim → t.zero_elim)

protected def tterm.repr : Π {a}, tterm a → string
| _ (t.var a x) := "(var " ++ repr a ++ " " ++ repr x ++ ")"
| _ (t.cut x e₁ e₂) := "(cut " ++ repr x ++ " " ++ e₁.repr ++ " " ++ e₂.repr ++ ")"
| _ t.one_intro := "one_intro"
| _ (t.one_elim e₁ e₂) := "(one_elim " ++ e₁.repr ++ " " ++ e₂.repr ++ ")"
| _ t.top_intro := "top_intro"
| _ (t.zero_elim a e) := "(zero_elim " ++ repr a ++ " " ++ e.repr ++ ")"

instance {a} : has_repr (tterm a) := ⟨tterm.repr⟩

@[simp]
protected def tterm.type {a} (_ : tterm a) := a

@[simp]
def tterm.to_uterm : Π {a}, tterm a → uterm
| _ (t.var _ x) := u.var x
| _ (t.cut x e₁ e₂) := u.cut x e₁.to_uterm e₂.to_uterm
| _ t.one_intro := u.one_intro
| _ (t.one_elim e₁ e₂) := u.one_elim e₁.to_uterm e₂.to_uterm
| _ t.top_intro := u.top_intro
| _ (t.zero_elim _ e) := u.zero_elim e.to_uterm

abbreviation ctx := list (string × type)

inductive cterm : ctx → type → Type
| exchange {Γ₁ Γ₂ a} (h : Γ₁ ~ Γ₂) (e : cterm Γ₁ a) : cterm Γ₂ a
| var (a x) : cterm [(x, a)] a
| cut {Γ₁ Γ₂ a b} (x) (e₁ : cterm Γ₁ a) (e₂ : cterm ((x, a) :: Γ₂) b) : cterm (Γ₁ ++ Γ₂) b
| one_intro : cterm [] one
| one_elim {Γ₁ Γ₂ a} (e₁ : cterm Γ₁ one) (e₂ : cterm Γ₂ a) : cterm (Γ₁ ++ Γ₂) a
| top_intro (Γ) : cterm Γ top
| zero_elim {Γ₁} (Γ₂ a) (e : cterm Γ₁ zero) : cterm (Γ₁ ++ Γ₂) a

export cterm
  (renaming exchange → c.exchange)
  (renaming var → c.var)
  (renaming cut → c.cut)
  (renaming one_intro → c.one_intro)
  (renaming one_elim → c.one_elim)
  (renaming top_intro → c.top_intro)
  (renaming zero_elim → c.zero_elim)

protected def cterm.repr : Π {Γ a}, cterm Γ a → string
| _ _ (c.exchange _ e) := "(exchange _ " ++ e.repr ++ ")"
| _ _ (c.var a x) := "(var " ++ repr a ++ " " ++ repr x ++ ")"
| _ _ (c.cut x e₁ e₂) := "(cut " ++ repr x ++ " " ++ e₁.repr ++ " " ++ e₂.repr ++ ")"
| _ _ c.one_intro := "one_intro"
| _ _ (c.one_elim e₁ e₂) := "(one_elim " ++ e₁.repr ++ " " ++ e₂.repr ++ ")"
| _ _ (c.top_intro Γ) := "(top_intro " ++ repr Γ ++ ")"
| _ _ (c.zero_elim Γ a e) := "(zero_elim " ++ repr Γ ++ " " ++ repr a ++ " " ++ e.repr ++ ")"

instance {Γ a} : has_repr (cterm Γ a) := ⟨cterm.repr⟩

@[simp]
protected def cterm.type {Γ a} (_ : cterm Γ a) := a

@[simp]
protected def cterm.ctx {Γ a} (_ : cterm Γ a) := Γ

@[simp]
def cterm.to_uterm : Π {Γ a}, cterm Γ a → uterm
| _ _ (c.exchange _ e) := e.to_uterm
| _ _ (c.var _ x) := u.var x
| _ _ (c.cut x e₁ e₂) := u.cut x e₁.to_uterm e₂.to_uterm
| _ _ c.one_intro := u.one_intro
| _ _ (c.one_elim e₁ e₂) := u.one_elim e₁.to_uterm e₂.to_uterm
| _ _ (c.top_intro _) := u.top_intro
| _ _ (c.zero_elim _ _ e) := u.zero_elim e.to_uterm

@[simp]
def cterm.to_tterm : Π {Γ a}, cterm Γ a → tterm a
| _ _ (c.exchange _ e) := e.to_tterm
| _ _ (c.var a x) := t.var a x
| _ _ (c.cut x e₁ e₂) := t.cut x e₁.to_tterm e₂.to_tterm
| _ _ c.one_intro := t.one_intro
| _ _ (c.one_elim e₁ e₂) := t.one_elim e₁.to_tterm e₂.to_tterm
| _ _ (c.top_intro _) := t.top_intro
| _ _ (c.zero_elim _ a e) := t.zero_elim a e.to_tterm

@[simp]
lemma cterm.to_uterm_of_to_tterm : Π {Γ a} (e : cterm Γ a), e.to_tterm.to_uterm = e.to_uterm
| _ _ (c.exchange _ e) := e.to_uterm_of_to_tterm
| _ _ (c.var _ x) := rfl
| _ _ (c.cut x e₁ e₂) := congr_arg2 _ e₁.to_uterm_of_to_tterm e₂.to_uterm_of_to_tterm
| _ _ c.one_intro := rfl
| _ _ (c.one_elim e₁ e₂) := congr_arg2 _ e₁.to_uterm_of_to_tterm e₂.to_uterm_of_to_tterm
| _ _ (c.top_intro _) := rfl
| _ _ (c.zero_elim _ _ e) := congr_arg _ e.to_uterm_of_to_tterm

@[simp]
def cterm.flatten : Π {Γ a}, cterm Γ a → cterm Γ a
| _ _ (@c.exchange Γ₁ Γ₂ _ h e) :=
  if h' : Γ₁ = Γ₂
  then cast (congr_fun (congr_arg cterm h') _) e.flatten
  else c.exchange h e.flatten
| _ _ (c.var a x) := c.var a x
| _ _ (c.cut x e₁ e₂) := c.cut x e₁.flatten e₂.flatten
| _ _ c.one_intro := c.one_intro
| _ _ (c.one_elim e₁ e₂) := c.one_elim e₁.flatten e₂.flatten
| _ _ (c.top_intro Γ) := c.top_intro Γ
| _ _ (c.zero_elim Γ a e) := c.zero_elim Γ a e.flatten

end linear
