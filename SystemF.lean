inductive Tp.Ctx
  | nil
  | cons (Δ : Ctx)

inductive Tp.Var : (Δ : Ctx) → Type
  | here : Var (.cons Δ)
  | there (α : Var Δ) : Var Δ.cons

@[elab_as_elim]
def Tp.Var.cases {motive : (α : Var (.cons Δ)) → Sort u} (here : motive here) (there : ∀ α, motive (there α)) : ∀ α, motive α
  | .here => here
  | .there α => there α

@[simp]
theorem Tp.Var.cases_commute {here there} (f : (b : β) → γ) : (α : Var (.cons Δ)) → f (cases here there α) = cases (f here) (fun α => f (there α)) α
  | .here | .there _ => rfl

inductive Tp : (Δ : Tp.Ctx) → Type
  | var (α : Tp.Var Δ) : Tp Δ
  | arr (τ₁ τ₂ : Tp Δ) : Tp Δ
  | all (τ : Tp Δ.cons) : Tp Δ

def Tp.Rename (Δ Δ' : Ctx) : Type :=
  (α : Var Δ) → Var Δ'

@[simp]
def Tp.Rename.weaken (δ : Rename Δ Δ') : Rename Δ.cons Δ'.cons :=
  Var.cases .here fun α => (δ α).there

def Tp.rename (δ : Rename Δ Δ') : (τ : Tp Δ) → Tp Δ'
  | var α => var (δ α)
  | arr τ₁ τ₂ => arr (τ₁.rename δ) (τ₂.rename δ)
  | all τ => all (τ.rename δ.weaken)

def Tp.Subst (Δ Δ' : Ctx) : Type :=
  (α : Var Δ) → Tp Δ'

@[simp]
def Tp.Subst.mk (τ : Tp Δ) : Subst Δ.cons Δ :=
  Var.cases τ var

@[simp]
def Tp.Subst.weaken (δ : Subst Δ Δ') : Subst Δ.cons Δ'.cons :=
  Var.cases (var .here) fun α => (δ α).rename .there

def Tp.subst (δ : Subst Δ Δ') : (τ : Tp Δ) → Tp Δ'
  | var α => δ α
  | arr τ₁ τ₂ => arr (τ₁.subst δ) (τ₂.subst δ)
  | all τ => all (τ.subst δ.weaken)

@[simp]
theorem Tp.rename_rename {δ₁ : Rename Δ Δ'} {δ₂ : Rename Δ' Δ''} {τ} : rename δ₂ (rename δ₁ τ) = rename (fun α => δ₂ (δ₁ α)) τ := by
  generalize h : (fun α => δ₂ (δ₁ α)) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with
  | var α => exact congrArg var (h α)
  | arr τ₁ τ₂ ih₁ ih₂ => exact congr (congrArg arr (ih₁ δ h)) (ih₂ δ h)
  | all τ ih => exact congrArg all (ih _ <| Var.cases rfl fun α => congrArg Var.there (h α))

@[simp]
theorem Tp.subst_rename {δ₁ : Rename Δ Δ'} {δ₂ : Subst Δ' Δ''} {τ} : subst δ₂ (rename δ₁ τ) = subst (fun α => δ₂ (δ₁ α)) τ := by
  generalize h : (fun α => δ₂ (δ₁ α)) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with
  | var α => exact h α
  | arr τ₁ τ₂ ih₁ ih₂ => exact congr (congrArg arr (ih₁ δ h)) (ih₂ δ h)
  | all τ ih => exact congrArg all (ih _ <| Var.cases rfl fun α => congrArg (rename .there) (h α))

@[simp]
theorem Tp.rename_subst {δ₁ : Subst Δ Δ'} {δ₂ : Rename Δ' Δ''} {τ} : rename δ₂ (subst δ₁ τ) = subst (fun α => (δ₁ α).rename δ₂) τ := by
  generalize h : (fun α => (δ₁ α).rename δ₂) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with
  | var α => exact h α
  | arr τ₁ τ₂ ih₁ ih₂ => exact congr (congrArg arr (ih₁ δ h)) (ih₂ δ h)
  | all τ ih => exact congrArg all (ih _ <| Var.cases rfl fun α => .trans (by simp!) (congrArg (rename .there) (h α)))

@[simp]
theorem Tp.subst_subst {δ₁ : Subst Δ Δ'} {δ₂ : Subst Δ' Δ''} {τ} : subst δ₂ (subst δ₁ τ) = subst (fun α => (δ₁ α).subst δ₂) τ := by
  generalize h : (fun α => (δ₁ α).subst δ₂) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with
  | var α => exact h α
  | arr τ₁ τ₂ ih₁ ih₂ => exact congr (congrArg arr (ih₁ δ h)) (ih₂ δ h)
  | all τ ih => exact congrArg all (ih _ <| Var.cases rfl fun α => .trans (by simp!) (congrArg (rename .there) (h α)))

@[simp]
theorem Tp.rename_id : rename (·) τ = τ := by
  generalize h : (·) = δ
  replace h α := congrFun h.symm α
  induction τ with
  | var α => exact congrArg var (h α)
  | arr τ₁ τ₂ ih₁ ih₂ => exact (congr (congrArg arr (ih₁ δ h)) (ih₂ δ h) :)
  | all τ ih => exact congrArg all (ih _ <| Var.cases rfl fun α => congrArg Var.there (h α))

@[simp]
theorem Tp.subst_var : subst var τ = τ := by
  generalize h : var = δ
  replace h α := congrFun h.symm α
  induction τ with
  | var α => exact h α
  | arr τ₁ τ₂ ih₁ ih₂ => exact (congr (congrArg arr (ih₁ δ h)) (ih₂ δ h) :)
  | all τ ih => exact congrArg all (ih _ <| Var.cases rfl fun α => congrArg (rename .there) (h α))

example (τ : Tp Δ) : Tp Δ.cons := τ.rename .there
example (τ : Tp Δ.cons) (τ' : Tp Δ) : Tp Δ := τ.subst (.mk τ')

inductive Tm.Ctx (Δ : Tp.Ctx)
  | nil
  | cons (Γ : Ctx Δ) (τ : Tp Δ)

def Tm.Ctx.rename (δ : Tp.Rename Δ Δ') : (Γ : Ctx Δ) → Ctx Δ'
  | nil => nil
  | cons Γ τ => cons (Γ.rename δ) (τ.rename δ)

def Tm.Ctx.subst (δ : Tp.Subst Δ Δ') : (Γ : Ctx Δ) → Ctx Δ'
  | nil => nil
  | cons Γ τ => cons (Γ.subst δ) (τ.subst δ)

@[simp]
theorem Tm.Ctx.rename_rename {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Rename Δ' Δ''} : ∀ {Γ}, rename δ₂ (rename δ₁ Γ) = rename (fun α => δ₂ (δ₁ α)) Γ
  | nil => rfl
  | cons .. => congr (congrArg cons rename_rename) Tp.rename_rename

@[simp]
theorem Tm.Ctx.subst_rename {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Subst Δ' Δ''} : ∀ {Γ}, subst δ₂ (rename δ₁ Γ) = subst (fun α => δ₂ (δ₁ α)) Γ
  | nil => rfl
  | cons .. => congr (congrArg cons subst_rename) Tp.subst_rename

@[simp]
theorem Tm.Ctx.rename_subst {δ₁ : Tp.Subst Δ Δ'} {δ₂ : Tp.Rename Δ' Δ''} : ∀ {Γ}, rename δ₂ (subst δ₁ Γ) = subst (fun α => (δ₁ α).rename δ₂) Γ
  | nil => rfl
  | cons .. => congr (congrArg cons rename_subst) Tp.rename_subst

@[simp]
theorem Tm.Ctx.subst_var : {Γ : Ctx Δ} → subst .var Γ = Γ
  | nil => rfl
  | cons .. => congr (congrArg cons subst_var) Tp.subst_var

inductive Tm.Var Δ (τ : Tp Δ) : (Γ : Ctx Δ) → Type
  | here : Var Δ τ (.cons Γ τ)
  | there (x : Var Δ τ Γ) : Var Δ τ (Γ.cons τ')

@[elab_as_elim]
def Tm.Var.cases {motive : ∀ τ, (x : Var Δ τ (.cons Γ τ')) → Sort u} (here : motive τ' here) (there : ∀ {τ} x, motive τ (there x)) : ∀ {τ} x, motive τ x
  | _, .here => here
  | _, .there x => there x

theorem Tm.Var.cases_cast {motive : ∀ τ, (x : Var Δ τ (.cons Γ τ')) → Sort u} {here there} (eq : τ = τ') : @cases Δ Γ τ' motive here there τ (eq ▸ .here) = eq.symm.rec (motive := fun τ eq => motive τ (eq.symm.ndrec (motive := (Var Δ τ <| Γ.cons ·)) .here)) here :=
  by cases eq; rfl

def Tm.Var.rename (δ : Tp.Rename Δ Δ') {τ Γ} : (x : Var Δ τ Γ) → Var Δ' (τ.rename δ) (Γ.rename δ)
  | here => here
  | there x => there (x.rename δ)

def Tm.Var.subst (δ : Tp.Subst Δ Δ') {τ Γ} : (x : Var Δ τ Γ) → Var Δ' (τ.subst δ) (Γ.subst δ)
  | here => here
  | there x => there (x.subst δ)

@[elab_as_elim]
def Tm.Var.casesRename {motive : ∀ τ, Var Δ' τ (Γ.rename δ) → Sort u} (k : ∀ {τ} (x : Var Δ τ Γ), motive (τ.rename δ) (x.rename δ)) {τ} x : motive τ x :=
  match Γ with
  | .nil => nomatch x
  | .cons .. => match τ, x with | _, .here => k here | _, .there x => x.casesRename (motive := fun τ x => motive τ x.there) fun x => k x.there

@[simp]
theorem Tm.Var.casesRename_rename : @casesRename Δ' Δ Γ δ motive k (τ.rename δ) (x.rename δ) = @k τ x := by
  induction x with
  | here => rfl
  | there x ih => exact ih

@[elab_as_elim]
def Tm.Var.casesSubst {motive : ∀ τ, Var Δ' τ (Γ.subst δ) → Sort u} (k : ∀ {τ} (x : Var Δ τ Γ), motive (τ.subst δ) (x.subst δ)) {τ} x : motive τ x :=
  match Γ with
  | .nil => nomatch x
  | .cons .. => match τ, x with | _, .here => k here | _, .there x => x.casesSubst (motive := fun τ x => motive τ x.there) fun x => k x.there

@[simp]
theorem Tm.Var.casesSubst_subst : @casesSubst Δ' Δ Γ δ motive k (τ.subst δ) (x.subst δ) = @k τ x := by
  induction x with
  | here => rfl
  | there x ih => exact ih

inductive Tm : ∀ Δ, (Γ : Tm.Ctx Δ) → (τ : Tp Δ) → Type
  | var (x : Tm.Var Δ τ Γ) : Tm Δ Γ τ
  | lam (e : Tm Δ (Γ.cons τ₁) τ₂) : Tm Δ Γ (τ₁.arr τ₂)
  | app (e : Tm Δ Γ (τ₁.arr τ₂)) (e₁ : Tm Δ Γ τ₁) : Tm Δ Γ τ₂
  | gen (e : Tm (.cons Δ) (Γ.rename .there) τ) : Tm Δ Γ (.all τ)
  | inst (e : Tm Δ Γ (.all τ)) τ' : Tm Δ Γ (τ.subst (.mk τ'))

def Tm.Var.cast {τ τ' Γ Γ'} (hτ : τ = τ') (hΓ : Γ = Γ') (x : Var Δ τ Γ) : Var Δ τ' Γ' :=
  match Γ', x with
  | .cons .., here => (Tm.Ctx.cons.inj hΓ).right ▸ hτ ▸ here
  | .cons .., there x => there (x.cast hτ (Tm.Ctx.cons.inj hΓ).left)

@[simp]
theorem Tm.Var.cast_rfl : cast rfl rfl x = x :=
  by induction x <;> simp! only [*]

@[simp]
theorem Tm.Var.cast_trans : cast hτ₂ hΓ₂ (cast hτ₁ hΓ₁ x) = cast (hτ₁.trans hτ₂) (hΓ₁.trans hΓ₂) x :=
  by subst_eqs; simp

def Tm.cast {Γ Γ' τ τ'} (hΓ : Γ = Γ') (hτ : τ = τ') (e : Tm Δ Γ τ) : Tm Δ Γ' τ' :=
  match τ', e with
  | _, var x => var (x.cast hτ hΓ)
  | .arr .., lam e => lam (e.cast (congr (congrArg Ctx.cons hΓ) (Tp.arr.inj hτ).left) (Tp.arr.inj hτ).right)
  | _, app e e₁ => app (e.cast hΓ (congrArg _ hτ)) (e₁.cast hΓ rfl)
  | .all _, gen e => gen (e.cast (congrArg _ hΓ) (Tp.all.inj hτ))
  | _, inst e τ => hτ ▸ inst (e.cast hΓ rfl) τ

@[simp]
theorem Tm.cast_rfl : cast rfl rfl e = e :=
  by induction e <;> simp [cast, *]

@[simp]
theorem Tm.cast_trans : cast hΓ₂ hτ₂ (cast hΓ₁ hτ₁ e) = cast (hΓ₁.trans hΓ₂) (hτ₁.trans hτ₂) e :=
  by subst_eqs; simp

def Tm.renameTp (δ : Tp.Rename Δ Δ') {Γ τ} : (e : Tm Δ Γ τ) → Tm Δ' (Γ.rename δ) (τ.rename δ)
  | var x => var (x.rename δ)
  | lam e => lam (e.renameTp δ)
  | app e e₁ => app (e.renameTp δ) (e₁.renameTp δ)
  | gen e => gen (e.renameTp δ.weaken |>.cast (by simp!) rfl)
  | inst e τ => inst (e.renameTp δ) (τ.rename δ) |>.cast rfl (by simp!)

def Tm.substTp (δ : Tp.Subst Δ Δ') {Γ τ} : (e : Tm Δ Γ τ) → Tm Δ' (Γ.subst δ) (τ.subst δ)
  | var x => var (x.subst δ)
  | lam e => lam (e.substTp δ)
  | app e e₁ => app (e.substTp δ) (e₁.substTp δ)
  | gen e => gen (e.substTp δ.weaken |>.cast (by simp!) rfl)
  | inst e τ => inst (e.substTp δ) (τ.subst δ) |>.cast rfl (by simp!)

def Tm.Rename Δ (Γ Γ' : Ctx Δ) : Type :=
  ∀ {τ}, (x : Var Δ τ Γ) → Var Δ τ Γ'

def Tm.Rename.rename (δ : Tp.Rename Δ Δ') {Γ Γ'} (γ : Rename Δ Γ Γ') : Rename Δ' (Γ.rename δ) (Γ'.rename δ) :=
  Var.casesRename fun x => (γ x).rename δ

@[simp]
def Tm.Rename.weaken (γ : Rename Δ Γ Γ') {τ} : Rename Δ (Γ.cons τ) (Γ'.cons τ) :=
  Var.cases .here fun x => (γ x).there

def Tm.rename (γ : Rename Δ Γ Γ') {τ} : (e : Tm Δ Γ τ) → Tm Δ Γ' τ
  | var x => var (γ x)
  | lam e => lam (e.rename γ.weaken)
  | app e e₁ => app (e.rename @γ) (e₁.rename @γ)
  | gen e => gen (e.rename (γ.rename .there))
  | inst e τ => inst (e.rename @γ) τ

def Tm.Subst Δ (Γ Γ' : Ctx Δ) : Type :=
  ∀ {τ}, (x : Var Δ τ Γ) → Tm Δ Γ' τ

@[simp]
def Tm.Subst.mk (e : Tm Δ Γ τ) : Subst Δ (Γ.cons τ) Γ :=
  Var.cases e .var

def Tm.Subst.rename (δ : Tp.Rename Δ Δ') {Γ Γ'} (γ : Subst Δ Γ Γ') : Subst Δ' (Γ.rename δ) (Γ'.rename δ) :=
  Var.casesRename fun x => (γ x).renameTp δ

@[simp]
def Tm.Subst.weaken (γ : Subst Δ Γ Γ') {τ} : Subst Δ (Γ.cons τ) (Γ'.cons τ) :=
  Var.cases (var .here) fun x => (γ x).rename .there

def Tm.subst (γ : Subst Δ Γ Γ') {τ} : (e : Tm Δ Γ τ) → Tm Δ Γ' τ
  | var x => γ x
  | lam e => lam (e.subst γ.weaken)
  | app e e₁ => app (e.subst @γ) (e₁.subst @γ)
  | gen e => gen (e.subst (γ.rename .there))
  | inst e τ => inst (e.subst @γ) τ

@[simp]
theorem Tm.Var.heq_cast : HEq (cast hτ hΓ x) x' = HEq x x' :=
  by subst_eqs; simp

@[simp]
theorem Tm.Var.heq_cast' : HEq x (cast hτ hΓ x') = HEq x x' :=
  by subst_eqs; simp

@[simp]
theorem Tm.heq_cast : HEq (cast hΓ hτ e) e' = HEq e e' :=
  by subst_eqs; simp

@[simp]
theorem Tm.heq_cast' : HEq e (cast hΓ hτ e') = HEq e e' :=
  by subst_eqs; simp

@[simp]
theorem Tm.Rename.rename_rename : rename δ γ (x.rename δ) = (γ x).rename δ := by
  induction x with
  | here => rfl
  | there x ih => exact ih

@[simp]
theorem Tm.rename_id : rename (·) e = e := by
  generalize h : (fun {τ} x => x) = γ
  replace h {τ} x := congrFun (congrFun h.symm τ) x
  induction e with simp! [*]
  | lam e ih => exact ih _ (Var.cases rfl fun x => congrArg _ (h x))
  | gen e ih => exact ih _ (Var.casesRename fun x => by simp; exact congrArg _ (h x))

@[simp]
theorem Tm.Subst.rename_rename : rename δ γ (x.rename δ) = (γ x).renameTp δ := by
  induction x with
  | here => rfl
  | there x ih => exact ih

@[simp]
theorem Tm.Rename.rename_rename' {γ : Rename Δ Γ Γ'} {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Rename Δ' Δ''} {x : Var _ τ _} : rename δ₂ (rename δ₁ @γ) x = x.casesRename (Var.casesRename fun x => (γ x).rename δ₁ |>.rename δ₂) := by
  refine x.casesRename fun x => ?_
  refine x.casesRename fun x => ?_
  simp

@[simp]
theorem Tm.Rename.there_rename {γ : Rename Δ Γ Γ'} : (rename δ γ x).there = rename δ (fun x => (γ x).there (τ' := τ)) x := by
  refine x.casesRename fun x => ?_
  simp!

@[simp]
theorem Tm.subst_var : subst var e = e := by
  generalize h : (fun {τ} x => var x) = γ
  replace h {τ} x := congrFun (congrFun h.symm τ) x
  induction e with simp! [*]
  | lam e ih => exact ih _ (Var.cases rfl fun _ => by simp! [h])
  | gen e ih => exact ih _ (Var.casesRename fun x => by simp! [h])

@[simp]
theorem Tp.Subst.weaken_var : @weaken Δ _ var = var := by
  funext α
  cases α <;> rfl

theorem Tm.rename_rename' (h : ∀ {τ} (x : Var _ τ _), γ₂ (γ₁ x) = γ x) : Rename.rename δ γ₂ (Rename.rename δ γ₁ x) = Rename.rename δ γ x := by
  refine x.casesRename fun x => ?_
  simp [h]

theorem Tm.Var.cast_flip : (eq : cast hτ.symm hΓ.symm x = x') → x = cast hτ hΓ x' :=
  by cases hΓ; cases hτ; simp

theorem Tm.cast_flip : (eq : cast hΓ.symm hτ.symm e = e') → e = cast hΓ hτ e' :=
  by cases hΓ; cases hτ; simp

theorem Tm.Var.cast_flip' : (eq : cast hτ hΓ x = x') → x = cast hτ.symm hΓ.symm x' :=
  by cases hΓ; cases hτ; simp

theorem Tm.cast_flip' : (eq : cast hΓ hτ e = e') → e = cast hΓ.symm hτ.symm e' :=
  by cases hΓ; cases hτ; simp

@[simp]
theorem Tm.rename_cast {γ : Rename Δ Γ Γ'} : rename γ (cast hΓ rfl e) = rename (fun x => γ (x.cast rfl hΓ)) e :=
  by cases hΓ; simp

@[simp]
theorem Tm.rename_cast' {γ : Rename Δ Γ Γ'} : rename γ (cast rfl hτ e) = cast rfl hτ (rename γ e) :=
  by cases hτ; simp

@[simp]
theorem Tm.cast_rename {γ : Rename Δ Γ Γ'} : cast hΓ rfl (rename γ e) = rename (fun x => (γ x).cast rfl hΓ) e :=
  by cases hΓ; simp

@[simp]
theorem Eq.rec_heq {refl} : HEq (@rec α a motive refl b h) rhs = HEq refl rhs :=
  by cases h; rfl

@[simp]
theorem Eq.rec_heq' {refl} : HEq lhs (@rec α a motive refl b h) = HEq lhs refl :=
  by cases h; rfl

@[simp]
theorem Tm.Var.casesRename_cast : @casesRename Δ' Δ Γ δ motive @k τ' (@cast Δ' (.rename δ τ) τ' (Γ.rename δ) (Γ.rename δ) hτ rfl (.rename δ x)) = hτ.rec (motive := fun τ' hτ => motive τ' (cast hτ rfl (x.rename δ))) (cast_rfl (x := x.rename δ) ▸ k x :) := by
  cases hτ
  induction x with
  | here => rfl
  | there x ih =>
    apply ih.trans
    simp [← heq_eq_eq]
    rfl

@[simp]
theorem Tm.Var.casesSubst_cast : @casesSubst Δ' Δ Γ δ motive @k τ' (@cast Δ' (.subst δ τ) τ' (Γ.subst δ) (Γ.subst δ) hτ rfl (.subst δ x)) = hτ.rec (motive := fun τ' hτ => motive τ' (cast hτ rfl (x.subst δ))) (cast_rfl (x := x.subst δ) ▸ k x :) := by
  cases hτ
  induction x with
  | here => rfl
  | there x ih =>
    apply ih.trans
    simp [← heq_eq_eq]
    rfl

theorem Tm.Var.heq_of_eq_cast (eq : cast hτ hΓ x = x') : HEq x x' :=
  by cases eq; simp

theorem Tm.heq_of_eq_cast (eq : cast hΓ hτ e = e') : HEq e e' :=
  by cases eq; simp

theorem Tm.Var.heq_here {τ τ'} (hτ : τ = τ') : HEq (@here Δ τ Γ) (@here Δ τ' Γ) :=
  by cases hτ; rfl

@[simp]
theorem Tm.Var.rename_rename (h : ∀ α, δ₂ (δ₁ α) = δ₂' (δ₁' α)) : cast rfl (by simp [h]) (rename δ₂ (rename δ₁ x)) = cast (by simp [h]) rfl (rename δ₂' (rename δ₁' x)) := by
  induction x with
  | here =>
    have {Δ} {τ τ' τ'' : Tp Δ} {Γ Γ' Γ'' : Ctx Δ} (hτ : τ = τ'') (hτ' : τ' = τ'') (hΓ : Γ.cons τ = Γ'') (hΓ'' : Γ'.cons τ' = Γ'') : cast hτ hΓ here = cast hτ' hΓ'' here := by
      subst_eqs
      rfl
    exact this ..
  | there x ih => simp! [ih]

theorem Tm.Var.rename_rename' (h : ∀ α, δ₂ (δ₁ α) = δ₂' (δ₁' α)) : HEq (rename δ₂ (rename δ₁ x)) (rename δ₂' (rename δ₁' x)) := by
  have := heq_of_eq (rename_rename h (x := x))
  simp [-heq_eq_eq] at this
  exact this

theorem Tm.Var.rename_rename'' (h : ∀ α, δ₂ (δ₁ α) = δ α) : rename δ₂ (rename δ₁ x) = cast (by simp [h]) (by simp [h]) (rename δ x) := by
  induction x with
  | here =>
    have {Δ} {τ τ' : Tp Δ} {Γ Γ' : Ctx Δ} {hτ : τ = τ'} {hΓ : Γ.cons τ = Γ'.cons τ'} : here = cast hτ hΓ here := by
      subst_eqs
      rfl
    exact this
  | there x ih => simp! [ih]

@[simp]
theorem Tm.Var.subst_rename (h : ∀ α, δ₂ (δ₁ α) = δ α) : subst δ₂ (rename δ₁ x) = cast (by simp [h]) (by simp [h]) (subst δ x) := by
  induction x with
  | here =>
    have {Δ} {τ τ' : Tp Δ} {Γ Γ' : Ctx Δ} {hτ : τ = τ'} {hΓ : Γ.cons τ = Γ'.cons τ'} : here = cast hτ hΓ here := by
      subst_eqs
      rfl
    exact this
  | there x ih => simp! [ih]

@[simp]
theorem Tm.Var.rename_subst {δ₁ : Tp.Subst Δ Δ'} {δ₂ : Tp.Rename Δ' Δ''} (h : ∀ α, (δ₁ α).rename δ₂ = δ α) : rename δ₂ (subst δ₁ x) = cast (by simp [h]) (by simp [h]) (subst δ x) := by
  induction x with
  | here =>
    have {Δ} {τ τ' : Tp Δ} {Γ Γ' : Ctx Δ} {hτ : τ = τ'} {hΓ : Γ.cons τ = Γ'.cons τ'} : here = cast hτ hΓ here := by
      subst_eqs
      rfl
    exact this
  | there x ih => simp! [ih]

@[simp]
theorem Tm.Var.subst_var : subst .var x = x.cast Tp.subst_var.symm Ctx.subst_var.symm := by
  induction x with
  | here =>
    have {Δ} {τ τ' : Tp Δ} {Γ Γ' : Ctx Δ} {hτ : τ = τ'} {hΓ : Γ.cons τ = Γ'.cons τ'} : here = cast hτ hΓ here := by
      subst_eqs
      rfl
    exact this
  | there x ih => simp! [ih]

@[simp]
theorem Tm.renameTp_cast : renameTp δ (cast hΓ hτ e) = cast (congrArg _ hΓ) (congrArg _ hτ) (e.renameTp δ) :=
  by subst_eqs; simp

@[simp]
theorem Tm.substTp_cast : substTp δ (cast hΓ hτ e) = cast (congrArg _ hΓ) (congrArg _ hτ) (e.substTp δ) :=
  by subst_eqs; simp

theorem Tm.renameTp_cong (eq : δ = δ') : renameTp δ e = cast (by simp [eq]) (by simp [eq]) (renameTp δ' e) :=
  by cases eq; simp

theorem Tm.substTp_cong (eq : δ = δ') : substTp δ e = cast (by simp [eq]) (by simp [eq]) (substTp δ' e) :=
  by cases eq; simp

theorem Tm.inst_cong {Γ₁ Γ₂ τ₁ τ₂ e₁ e₂ τ'₁ τ'₂} (hΓ : Γ₁ = Γ₂) (hτ : τ₁ = τ₂) (he : HEq e₁ e₂) (hτ : τ'₁ = τ'₂) : HEq (@inst Δ Γ₁ τ₁ e₁ τ'₁) (@inst Δ Γ₂ τ₂ e₂ τ'₂) := by
  subst_eqs
  rfl

@[simp]
theorem Tm.substTp_var : substTp .var e = e.cast Ctx.subst_var.symm Tp.subst_var.symm := by
  have {Δ} : Tp.Subst.weaken (Δ := Δ) .var = .var := by
    funext α
    cases α <;> rfl
  induction e with
  | var x => simp! [cast]
  | lam e ih => simp! [cast, ih]
  | app e e₁ ih ih₁ => simp only [substTp, cast, ih, ih₁]; simp
  | gen e ih => simp! [cast]; simp! [← heq_eq_eq]; rewrite [this]; simp [ih]
  | inst e τ ih => simp! [cast, ih, ← heq_eq_eq]; apply inst_cong <;> simp [this]

@[simp]
theorem Tm.renameTp_renameTp {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Rename Δ' Δ''} : renameTp δ₂ (renameTp δ₁ e) = (renameTp (fun α => δ₂ (δ₁ α)) e).cast (by simp) (by simp) := by
  induction e generalizing Δ' Δ'' with simp! [*]
  | var x => simp [cast]; apply Var.rename_rename''; simp
  | app e e₁ => simp [cast]
  | gen e ih =>
    have : @Eq (Tp.Rename ..) (fun α => .cases .here (fun α => (δ₂ α).there) (.cases .here (fun α => (δ₁ α).there) α)) (.weaken fun α => δ₂ (δ₁ α)) := by
      funext α
      cases α
      . rfl
      . rfl
    rewrite [renameTp_cong this]
    simp
  | inst e τ ih =>
    simp [← heq_eq_eq]
    apply inst_cong <;> simp
    rfl

@[simp]
theorem Tm.substTp_renameTp {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Subst Δ' Δ''} : substTp δ₂ (renameTp δ₁ e) = (substTp (fun α => δ₂ (δ₁ α)) e).cast (by simp) (by simp) := by
  induction e generalizing Δ' Δ'' with simp! [*]
  | var x => simp [cast]
  | app e e₁ => simp [cast]
  | gen e ih =>
    have : @Eq (Tp.Subst ..) (fun α => Tp.Var.cases (.var .here) (fun α => (δ₂ α).rename .there) (Tp.Var.cases .here (fun α => (δ₁ α).there) α)) (.weaken fun α => δ₂ (δ₁ α)) := by
      funext α
      cases α
      . rfl
      . rfl
    rewrite [substTp_cong this]
    simp
  | inst e τ ih =>
    simp [← heq_eq_eq]
    apply inst_cong <;> simp
    rfl

@[simp]
theorem Tm.renameTp_substTp {δ₁ : Tp.Subst Δ Δ'} {δ₂ : Tp.Rename Δ' Δ''} : renameTp δ₂ (substTp δ₁ e) = (substTp (fun α => (δ₁ α).rename δ₂) e).cast (by simp) (by simp) := by
  induction e generalizing Δ' Δ'' with simp! [*]
  | var x => simp [cast]
  | app e e₁ => simp [cast]
  | gen e ih =>
    have : @Eq (Tp.Subst ..) (fun α => Tp.rename δ₂.weaken (Tp.Var.cases (.var .here) (fun α => (δ₁ α).rename .there) α)) (.weaken fun α => (δ₁ α).rename δ₂) := by
      funext α
      cases α
      . rfl
      . simp!
    rewrite [substTp_cong this]
    simp
  | inst e τ ih =>
    simp [← heq_eq_eq]
    apply inst_cong <;> simp!
    congr
    funext α
    cases α <;> simp!

theorem Tm.rename_rename'' {γ₁ : Subst Δ Γ Γ'} {γ₂ : Rename Δ Γ' Γ''} {γ : Subst Δ Γ Γ''} (h : ∀ {τ} (x : Var _ τ _), (γ₁ x).rename @γ₂ = γ x) : rename (γ₂.rename δ) (γ₁.rename δ x) = γ.rename δ x := by
  refine x.casesRename fun x => ?_
  simp [← h]
  generalize γ₁ x = e
  clear h γ₁
  rename_i Δ' τ x' _ 
  clear Γ τ x' γ x
  induction e generalizing Δ' with simp! [*]
  | lam e ih =>
    simp! [← ih]
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesRename fun x => ?_
    simp! [Rename.rename]
  | gen e ih =>
    simp! [← ih]
    congr
    funext τ x
    refine x.casesRename fun x => ?_
    refine x.casesRename fun x => ?_
    simp! [← heq_eq_eq]
    rfl

theorem Tm.rename_rename''' {γ : Subst Δ Γ Γ'} : rename .there (Subst.rename δ γ x) = Subst.rename δ (Γ' := .cons _ τ) (fun x => rename .there (γ x)) x := by
  refine .trans ?_ (rename_rename'' (γ₁ := @γ) (γ₂ := .there (τ' := τ)) fun _ => by simp)
  congr
  funext τ x
  refine x.casesRename fun x => ?_
  simp!

theorem Tm.subst_rename' (h : ∀ {τ} (x : Var _ τ _), γ₂ (γ₁ x) = γ x) : Subst.rename δ γ₂ (Rename.rename δ γ₁ x) = Subst.rename δ γ x := by
  refine x.casesRename fun x => ?_
  simp [h]

@[simp]
theorem Tm.rename_rename : rename γ₂ (rename γ₁ e) = rename (fun x => γ₂ (γ₁ x)) e := by
  generalize h : (fun {τ} x => γ₂ (γ₁ x)) = γ
  replace h {τ} x := congrFun (congrFun h τ) x
  induction e with
  | var x => exact congrArg var (h x)
  | lam e ih => exact congrArg lam (ih _ <| Var.cases rfl fun x => congrArg Var.there (h x))
  | app e e₁ ih ih₁ => exact congr (congrArg app (ih _ h)) (ih₁ _ h)
  | gen e ih => exact congrArg gen (ih _ fun _ => rename_rename' h)
  | inst e τ ih => exact congrArg (inst · τ) (ih _ h)

@[simp]
theorem Tm.subst_rename : subst γ₂ (rename γ₁ e) = subst (fun x => γ₂ (γ₁ x)) e := by
  generalize h : (fun {τ} x => γ₂ (γ₁ x)) = γ
  replace h {τ} x := congrFun (congrFun h τ) x
  induction e with
  | var x => exact h x
  | lam e ih => exact congrArg lam (ih _ <| Var.cases rfl fun x => congrArg (rename .there) (h x))
  | app e e₁ ih ih₁ => exact congr (congrArg app (ih _ h)) (ih₁ _ h)
  | gen e ih => exact congrArg gen (ih _ fun _ => subst_rename' h)
  | inst e τ ih => exact congrArg (inst · τ) (ih _ h)

@[simp]
theorem Tm.rename_subst : rename @γ₂ (subst @γ₁ e) = subst (fun x => (γ₁ x).rename @γ₂) e := by
  generalize h : (fun {τ} x => (γ₁ x).rename @γ₂) = γ
  replace h {τ} x := congrFun (congrFun h τ) x
  induction e with
  | var x => exact h x
  | lam e ih => exact congrArg lam (ih _ <| Var.cases rfl fun x => by simp [Rename.weaken, Subst.weaken, Var.cases, ← h x])
  | app e e₁ ih ih₁ => exact congr (congrArg app (ih _ h)) (ih₁ _ h)
  | gen e ih => exact congrArg gen (ih _ fun _ => rename_rename'' h)
  | inst e τ ih => exact congrArg (inst · τ) (ih _ h)

@[simp]
theorem Tm.substTp_rename {δ : Tp.Subst Δ Δ'} {γ : Rename Δ Γ Γ'} {e : Tm Δ Γ τ} : substTp δ (rename γ e) = (e.substTp δ).rename (Var.casesSubst fun x => (γ x).subst δ) := by
  induction e generalizing Δ' with simp! [*]
  | lam e ih =>
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesSubst fun x => ?_
    simp!
  | gen e ih =>
    congr
    funext τ x
    refine x.casesSubst fun x => ?_
    refine x.casesRename fun x => ?_
    simp! [Rename.rename]
    have : x.subst (fun α => (δ α).rename .there) = ((x.subst δ).rename .there).cast (by simp) (by simp) := by
      simp
    simp! [this, ← heq_eq_eq]
    have : ((x.subst δ).rename .there).cast (by simp!) (by simp!) = (x.rename .there).subst δ.weaken := by
      simp!
    rewrite [this]
    simp
    simp!

example (e : Tm Δ Γ τ) : Tm Δ.cons (Γ.rename .there) (τ.rename .there) := e.renameTp .there
example (e : Tm Δ Γ τ) : Tm Δ (Γ.cons τ') τ := e.rename .there
example (e : Tm (.cons Δ) Γ τ) (τ' : Tp Δ) : Tm Δ (Γ.subst (.mk τ')) (τ.subst (.mk τ')) := e.substTp (.mk τ')
example (e : Tm Δ (Γ.cons τ') τ) (e' : Tm Δ Γ τ') : Tm Δ Γ τ := e.subst (Tm.Subst.mk e')

def Tm.Subst' Δ Δ' (δ : Tp.Subst Δ Δ') (Γ : Ctx Δ) (Γ' : Ctx Δ') : Type :=
  ∀ {τ}, (x : Var Δ τ Γ) → Tm Δ' Γ' (τ.subst δ)

def Tm.Subst'.weakenTp (γ : Subst' Δ Δ' δ Γ Γ') : Subst' Δ.cons Δ'.cons δ.weaken (Γ.rename .there) (Γ'.rename .there) :=
  Var.casesRename fun x => ((γ x).renameTp .there).cast rfl (by simp!)

@[simp]
def Tm.Subst'.weaken (γ : Subst' Δ Δ' δ Γ Γ') {τ} : Subst' Δ Δ' δ (Γ.cons τ) (Γ'.cons (τ.subst δ)) :=
  Var.cases (var .here) fun x => (γ x).rename .there

@[simp]
def Tm.Subst'.weakenTp' (γ : Subst' Δ Δ' δ Γ Γ') : Subst' Δ.cons Δ' (Tp.Var.cases τ δ) (Γ.rename .there) Γ' :=
  Var.casesRename fun x => (γ x).cast rfl (by simp!)

def Tm.subst' (γ : Subst' Δ Δ' δ Γ Γ') {τ} : (e : Tm Δ Γ τ) → Tm Δ' Γ' (τ.subst δ)
  | var x => γ x
  | lam e => lam (e.subst' γ.weaken)
  | app e e₁ => app (e.subst' @γ) (e₁.subst' @γ)
  | gen e => gen (e.subst' γ.weakenTp)
  | inst e τ => inst (e.subst' @γ) (τ.subst δ) |>.cast rfl (by simp!)

@[simp]
theorem Tm.Subst'.weakenTp_rename {γ : Subst' Δ Δ' δ Γ Γ'} : weakenTp γ (.rename .there x) = ((γ x).renameTp .there).cast rfl (by simp!) := by
  induction x with
  | here => simp! [weakenTp]
  | there x ih => exact ih

theorem Tm.subst_cast {γ : Subst Δ Γ Γ'} : subst γ (cast hΓ hτ e) = cast rfl hτ (subst (fun x => γ (x.cast rfl hΓ)) e) :=
  by subst_vars; simp

theorem Tm.cast_subst {γ : Subst Δ Γ Γ'} : cast hΓ hτ (subst γ e) = subst (fun x => (γ x).cast hΓ rfl) (e.cast rfl hτ) :=
  by subst_eqs; simp

@[simp]
theorem Tm.Subst.rename_cast : rename δ γ (.cast hτ rfl e) = (rename δ γ e).cast rfl hτ :=
  by cases hτ; simp

@[simp]
theorem Tm.rename_renameTp : rename (Rename.rename δ @γ) (renameTp δ e) = renameTp δ (rename @γ e) := by
  rename_i Δ Δ' _ _ _
  induction e generalizing Δ' with simp! [*]
  | lam e ih =>
    refine .trans ?_ (ih (γ := γ.weaken))
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesRename fun x => ?_
    change _ = Rename.rename δ γ.weaken (.rename δ x.there)
    simp
    simp!
  | gen e ih =>
    apply cast_flip
    refine .trans ?_ ih
    simp
    congr
    funext τ x
    refine x.casesRename fun x => ?_
    refine x.casesRename fun x => ?_
    simp! [← heq_eq_eq]
    apply Var.rename_rename'
    simp!

@[simp]
theorem Tm.subst_renameTp : subst (Subst.rename δ @γ) (renameTp δ e) = renameTp δ (subst @γ e) := by
  rename_i Δ Δ' _ _ _
  induction e generalizing Δ' with simp! [*, subst_cast]
  | lam e ih =>
    refine .trans ?_ (ih (γ := γ.weaken))
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesRename fun x => ?_
    change _ = Subst.rename δ γ.weaken (.rename δ x.there)
    simp
    simp!
    generalize γ x = e
    simp! [← rename_renameTp]
    congr
    funext τ x
    refine x.casesRename fun x => ?_
    simp!
  | gen e ih =>
    apply cast_flip
    refine .trans ?_ ih
    simp [cast_subst]
    congr
    funext τ x
    refine x.casesRename fun x => ?_
    refine x.casesRename fun x => ?_
    simp!

theorem Tm.subst_subst' {γ₁ : Subst' Δ Δ' δ Γ Γ'} {γ₂ : Subst Δ' Γ' Γ''} : subst @γ₂ (subst' @γ₁ e) = subst' (fun x => (γ₁ x).subst @γ₂) e := by
  generalize h : (fun {τ} x => (γ₁ x).subst @γ₂) = γ
  replace h {τ} x := congrFun (congrFun h τ) x
  induction e generalizing Δ' Γ' Γ'' γ₂ with
  | var x => exact h x
  | lam e ih => exact congrArg lam (ih _ <| Var.cases rfl fun x => .trans (by simp!) (congrArg (rename .there) (h x)))
  | app e e₁ ih ih₁ => exact congr (congrArg app (ih _ h)) (ih₁ _ h)
  | gen e ih => exact congrArg gen (ih _ (Var.casesRename fun _ => by simp [h, subst_cast]))
  | inst e τ ih =>
    simp!
    simp [← heq_eq_eq, subst_cast]
    apply inst_cong <;> simp [*]

@[simp]
theorem Tm.cast_subst' {γ : Subst' Δ Δ' δ Γ Γ'} {e : Tm Δ Γ τ} : cast rfl (congrArg τ.subst h) (subst' γ e) = subst' (fun x => (γ x).cast rfl (congrArg (Tp.subst · _) h)) e :=
  by cases h; simp

theorem Tm.subst'_cong {δ₁ δ₂ Γ₁ Γ₂ γ₁ γ₂} (hδ : δ₁ = δ₂) (hΓ : Γ₁ = Γ₂) (hγ : ∀ {τ} (x : Var Δ τ Γ), HEq (γ₁ x) (γ₂ x)) : HEq (@subst' Δ Δ' δ₁ Γ Γ₁ γ₁ τ e) (@subst' Δ Δ' δ₂ Γ Γ₂ γ₂ τ e) :=
  by subst_eqs; cases funext fun τ => funext fun x => eq_of_heq (@hγ τ x); rfl

theorem Tm.rename_cong {Γ₁ Γ₂ γ₁ γ₂} (hΓ : Γ₁ = Γ₂) (hγ : ∀ {τ} (x : Var Δ τ Γ), HEq (γ₁ x) (γ₂ x)) : HEq (@rename Δ Γ Γ₁ γ₁ τ e) (@rename Δ Γ Γ₂ γ₂ τ e) :=
  by cases hΓ; cases funext fun τ => funext fun x => eq_of_heq (@hγ τ x); rfl

theorem Tm.substTp_subst' {γ : Subst' Δ Δ' δ₁ Γ Γ'} {δ₂ : Tp.Subst Δ' Δ''} : substTp δ₂ (subst' @γ e) = (subst' (fun x => (γ x).substTp δ₂ |>.cast rfl (by simp; rfl)) e).cast rfl (by simp) := by
  induction e generalizing Δ' Γ' Δ'' δ₂ with simp! [*]
  | lam e ih =>
    simp [← heq_eq_eq]
    apply subst'_cong <;> simp
    intro τ x
    cases x
    . simp!; apply heq_of_eq_cast <;> simp [cast]; simp [← heq_eq_eq]; apply Var.heq_here; simp
    . simp!; apply rename_cong; simp; intro τ x; refine x.casesSubst fun x => ?_; simp!; apply Var.heq_of_eq_cast <;> simp!
  | app e e₁ ih ih₁ => simp [*, cast]
  | gen e ih =>
    simp [← heq_eq_eq]
    apply subst'_cong <;> simp!
    . funext α; cases α <;> simp!
    intro τ x
    refine x.casesRename fun x => ?_
    simp!
  | inst e τ ih =>
    simp [← heq_eq_eq]
    apply inst_cong <;> simp!
    congr
    funext α
    cases α <;> simp!

@[simp]
theorem Tm.subst'_mk {γ : Subst' Δ Δ' δ Γ Γ'} {e : Tm Δ (Γ.cons τ') τ} {e' : Tm Δ' Γ' (τ'.subst δ)} : subst (Subst.mk e') (subst' (Subst'.weaken γ) e) = subst' (Var.cases e' γ) e := by
  simp [subst_subst']
  congr
  funext τ x
  cases x <;> simp!

@[simp]
theorem Tm.subst'_mkTp {γ : Subst' Δ Δ' δ Γ .nil} : substTp (.mk τ) (subst' γ.weakenTp e) = (subst' γ.weakenTp' e).cast rfl (by simp!; rfl) := by
  apply cast_flip
  simp! [substTp_subst']
  congr
  funext τ x
  refine x.casesRename fun x => ?_
  simp! [Subst'.weakenTp']

@[simp]
theorem Tp.subst_nil : @subst .nil .nil δ τ = τ := by
  cases show δ = var from funext nofun
  exact subst_var

@[simp]
theorem Tm.subst'_var {δ : Tp.Subst Δ Δ'} : subst' (fun x => var (x.subst δ)) e = e.substTp δ := by
  generalize h : (fun {τ} x => var (.subst δ x)) = γ
  replace h {τ} x := congrFun (congrFun h.symm τ) x
  induction e generalizing Δ' with simp! [*]
  | lam e ih => exact ih _ (Var.cases rfl fun _ => by simp! [h])
  | gen e ih =>
    specialize @ih Δ'.cons δ.weaken (fun {τ} x => (Subst'.weakenTp γ x).cast (by simp!) rfl) ?_
    . intro τ x
      refine x.casesRename fun x => ?_
      simp! [h x, cast]
    simp [← ih, ← heq_eq_eq]
    apply subst'_cong <;> simp!

@[simp]
theorem Tm.subst'_nil : @subst' .nil .nil δ .nil .nil γ τ e = e.cast rfl (by simp) := by
  cases show @γ = fun {τ} x => var (x.subst δ) from funext fun τ => funext nofun
  simp
  cases show δ = .var from funext nofun
  simp

inductive Tm.Steps : (e e' : Tm .nil .nil τ) → Type
  | app (s : e.Steps e') : (app e e₁).Steps (app e' e₁)
  | app_lam : Steps (app (lam e) e₁) (e.subst (Subst.mk e₁))
  | inst (s : e.Steps e') : (inst e τ).Steps (inst e' τ)
  | inst_gen : Steps (inst (gen e) τ) (e.substTp (.mk τ))

inductive Tm.Val : (e : Tm .nil .nil τ) → Type
  | lam : Val (.lam e)
  | gen : Val (.gen e)

theorem Tm.Val.not_steps : (v : Val e) → (s : Steps e e') → False
  | @lam τ₁ τ₂ e, s =>
    have {τ} {e₁ e' : Tm .nil .nil τ} (h : τ = τ₁.arr τ₂) (h' : h ▸ e₁ = e.lam) (s : Tm.Steps e₁ e') : False := by
      cases s with
      | app => nomatch h
      | app_lam => nomatch h
      | inst => rename_i τ _ _ _ _ ; cases τ; rename_i α _ _ _; cases α; cases h; nomatch h'; nomatch h; cases h; nomatch h'; nomatch h
      | inst_gen => rename_i τ _ _ ; cases τ; rename_i α _; cases α; cases h; nomatch h'; nomatch h; cases h; nomatch h'; nomatch h
    this rfl rfl s
  | @gen τ e, s =>
    have {τ₁} {e₁ e' : Tm .nil .nil τ₁} (h : τ₁ = τ.all) (h' : h ▸ e₁ = e.gen) (s : Tm.Steps e₁ e') : False := by
      cases s with
      | app => nomatch h
      | app_lam => nomatch h
      | inst => rename_i τ _ _ _ _ ; cases τ; rename_i α _ _ _; cases α; cases h; nomatch h'; nomatch h; nomatch h; nomatch h
      | inst_gen => rename_i τ _ _ ; cases τ; rename_i α _; cases α; cases h; nomatch h'; nomatch h; nomatch h; nomatch h
    this rfl rfl s

def Tm.progress : (e : Tm .nil .nil τ) → Val e ⊕ Σ e', Steps e e'
  | lam e => .inl .lam
  | app e e₁ => .inr <|
                match e.progress with
                | .inl .lam => ⟨_, .app_lam⟩
                | .inr ⟨_, s⟩ => ⟨_, .app s⟩
  | gen e => .inl .gen
  | inst e τ => .inr <|
                match e.progress with
                | .inl .gen => ⟨_, .inst_gen⟩
                | .inr ⟨_, s⟩ => ⟨_, .inst s⟩

inductive Tm.Reduces : (e e' : Tm .nil .nil τ) → Type
  | refl : Reduces e e
  | step (s : Steps e e') (r : Reduces e' e'') : Reduces e e''

def Tm.Reduces.trans : (r : Reduces e e') → (r' : Reduces e' e'') → Reduces e e''
  | refl,     r' => r'
  | step s r, r' => step s (r.trans r')

def Tm.Reduces.lift {F : (e : Tm .nil .nil τ) → Tm .nil .nil τ'} (f : ∀ {e e'}, (s : Steps e e') → Steps (F e) (F e')) : (r : Reduces e e') → Reduces (F e) (F e')
  | refl     => refl
  | step s r => step (f s) (r.lift f)

def Tm.Reduces.app : (r : Reduces e e') → Reduces (e.app e₁) (e'.app e₁) :=
  lift .app

def Tm.Reduces.inst : (r : Reduces e e') → Reduces (e.inst τ) (e'.inst τ) :=
  lift .inst

def Tm.Reduces.cast (r : Reduces e e') : Reduces (e.cast hΓ hτ) (e'.cast hΓ hτ) :=
  by subst_eqs; simp; exact r

def Tm.Cand (τ : Tp .nil) :=
  { C : Tm .nil .nil τ → Prop // ∀ e e', (s : Reduces e e') → (c : C e') → C e }

def Tm.HT Δ (δ : Tp.Subst Δ .nil) (η : ∀ α, Cand (δ α)) (τ : Tp Δ) (e : Tm .nil .nil (τ.subst δ)) : Prop :=
  match τ with
  | .var α => (η α).val e
  | .arr τ₁ τ₂ => ∃ e₂, ∃ r : Reduces e (.lam e₂), (∀ e₁, (ht : HT Δ δ η τ₁ e₁) → HT Δ δ η τ₂ (e₂.subst (Subst.mk e₁)))
  | .all τ => ∃ e', ∃ r : Reduces e (.gen e'), ∀ τ' (C : Cand τ'), HT Δ.cons (Tp.Var.cases τ' δ) (Tp.Var.cases C η) τ (e'.substTp (.mk τ') |>.cast rfl (by simp!))

theorem Tm.HT.expand : ∀ {τ} e e', (r : Reduces e e') → (ht : HT Δ δ η τ e') → HT Δ δ η τ e
  | .var α, e, e', r, ht => (η α).property e e' r ht
  | .arr _τ₁ _τ₂, _, _, r, ⟨_, r', ht⟩ => ⟨_, r.trans r', ht⟩
  | .all _τ, _, _, r, ⟨_, r', ht⟩ => ⟨_, r.trans r', ht⟩

theorem funext' {α : Sort u} {β γ : α → Sort v} {f : ∀ x, β x} {g : ∀ x, γ x} (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  cases funext fun x => type_eq_of_heq (h x)
  simp at h ⊢
  exact funext h

theorem Tm.HT.rename {δ₁ : Tp.Rename Δ Δ'} {e} : HT Δ (fun α => δ' (δ₁ α)) (fun α => η' (δ₁ α)) τ e ↔ HT Δ' δ' η' (τ.rename δ₁) (e.cast rfl (by simp)) := by
  induction τ generalizing Δ' with
  | var => simp!
  | arr τ₁ τ₂ ih₁ ih₂ =>
    specialize @ih₁ Δ' δ' η' δ₁
    specialize @ih₂ Δ' δ' η' δ₁
    constructor
    . intro ⟨e, r, ht⟩
      exists _, r.cast
      intro e₁ ht₁
      specialize @ih₁ (e₁.cast rfl (by simp!))
      simp at ih₁
      refine Eq.mp ?_ (ih₂.mp (ht _ (ih₁.mpr ht₁)))
      congr
      simp [subst_cast]
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp! [Var.cases_cast, ← heq_eq_eq]
      rfl
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl (by simp!) := by simp [← h]
      cases h
      intro ⟨e, r, ht⟩
      exists _, r.cast
      intro e₁ ht₁
      specialize @ih₂ (e.subst (Subst.mk (e₁.cast rfl (by simp!))) |>.cast rfl (by simp!))
      simp at ih₂
      refine Eq.mp ?_ (ih₂.mpr (ht _ (ih₁.mp ht₁)))
      congr
      simp [subst_cast]
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp! [Var.cases_cast, ← heq_eq_eq]
      rfl
  | all τ ih =>
    constructor
    . intro ⟨e, r, ht⟩
      exists _, r.cast
      intro τ₁ C₁
      specialize @ih Δ'.cons (Tp.Var.cases τ₁ δ') (Tp.Var.cases C₁ η') δ₁.weaken (e.substTp (.mk τ₁) |>.cast rfl (by simp!))
      refine Eq.mp ?_ (ih.mp (Eq.mp ?_ (ht τ₁ C₁)))
      . simp
      . congr <;> simp!
        apply funext'
        intro α
        cases α <;> rfl
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl _ := cast_flip' h
      cases h
      intro ⟨e, r, ht⟩
      exists _, r.cast
      intro τ₁ C₁
      specialize @ih Δ'.cons (Tp.Var.cases τ₁ δ') (Tp.Var.cases C₁ η') δ₁.weaken (e.substTp (.mk τ₁) |>.cast rfl (by simp!))
      simp at ih
      refine Eq.mp ?_ (ih.mpr (ht τ₁ C₁))
      congr 1 <;> simp!
      apply funext'
      intro α
      cases α <;> rfl

theorem Tm.HT.subst {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Subst Δ' Δ} (hδ : ∀ α, (δ₂ α).subst (fun α => δ' (δ₁ α)) = δ' α) (h : ∀ α e, HT Δ (fun α => δ' (δ₁ α)) (fun α => η' (δ₁ α)) (δ₂ α) (e.cast rfl (by simp [hδ])) ↔ (η' α).val e) {e} : HT Δ (fun α => δ' (δ₁ α)) (fun α => η' (δ₁ α)) (τ.subst δ₂) e ↔ HT Δ' δ' η' τ (e.cast rfl (by simp [hδ])) := by
  induction τ generalizing Δ with
  | var α =>
    specialize h α (e.cast rfl (by simp! [hδ]))
    simp! at h ⊢
    exact h
  | arr τ₁ τ₂ ih₁ ih₂ =>
    specialize @ih₁ Δ δ' η' δ₁ δ₂ hδ h
    specialize @ih₂ Δ δ' η' δ₁ δ₂ hδ h
    constructor
    . intro ⟨e, r, ht⟩
      exists _, r.cast
      intro e₁ ht₁
      specialize @ih₁ (e₁.cast rfl (by simp [hδ]))
      simp at ih₁
      refine Eq.mp ?_ (ih₂.mp (ht _ (ih₁.mpr ht₁)))
      congr
      simp [subst_cast]
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp! [Var.cases_cast, ← heq_eq_eq]
      rfl
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl _ := cast_flip' h
      cases h
      intro ⟨e, r, ht⟩
      exists _, r.cast
      intro e₁ ht₁
      specialize @ih₂ (e.subst (Subst.mk (e₁.cast rfl (by simp [hδ]))) |>.cast rfl (by simp [hδ]))
      simp at ih₂
      refine Eq.mp ?_ (ih₂.mpr (ht _ (ih₁.mp ht₁)))
      congr
      simp [subst_cast]
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp! [Var.cases_cast, ← heq_eq_eq]
      rfl
  | all τ ih =>
    constructor
    . intro ⟨e, r, ht⟩
      exists _, r.cast
      intro τ' C
      specialize @ih Δ.cons (Tp.Var.cases τ' δ') (Tp.Var.cases C η') δ₁.weaken δ₂.weaken (Tp.Var.cases rfl (by simp! [hδ])) (Tp.Var.cases (by simp!) fun α e => .trans (.symm (.trans (@rename Δ Δ.cons (Tp.Var.cases τ' fun α => δ' (δ₁ α)) (Tp.Var.cases C fun α => η' (δ₁ α)) (δ₂ α) .there (e.cast rfl _)) ?_)) (h α e)) (e.substTp (.mk τ') |>.cast rfl (by simp!))
      . simp! [← eq_iff_iff]
        congr 1
        . simp!
        . apply funext'
          intro α
          cases α <;> rfl
        . simp
      refine Eq.mp ?_ (ih.mp (Eq.mp ?_ (ht τ' C)))
      . simp
      . congr <;> simp!
        apply funext'
        intro α
        cases α <;> rfl
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl _ := cast_flip' h
      cases h
      intro ⟨e, r, ht⟩
      exists _, r.cast
      intro τ' C
      specialize @ih Δ.cons (Tp.Var.cases τ' δ') (Tp.Var.cases C η') δ₁.weaken δ₂.weaken (Tp.Var.cases rfl (by simp! [hδ])) (Tp.Var.cases (by simp!) fun α e => .trans (.symm (.trans (@rename Δ Δ.cons (Tp.Var.cases τ' fun α => δ' (δ₁ α)) (Tp.Var.cases C fun α => η' (δ₁ α)) (δ₂ α) .there (e.cast rfl _)) ?_)) (h α e)) (e.substTp (.mk τ') |>.cast rfl (by simp! [hδ]))
      . simp! [← eq_iff_iff]
        congr 1
        . simp!
        . apply funext'
          intro α
          cases α <;> rfl
        . simp
      simp at ih
      refine Eq.mp ?_ (ih.mpr (ht τ' C))
      congr 1 <;> simp!
      apply funext'
      intro α
      cases α <;> rfl

theorem Tm.HT.compose {e} : HT Δ δ η (τ.subst (.mk τ')) e ↔ HT Δ.cons (Tp.Var.cases (.subst δ τ') δ) (Tp.Var.cases ⟨HT Δ δ η τ', HT.expand⟩ η) τ (e.cast rfl (by simp!)) := by
  exact @subst Δ Δ.cons (Tp.Var.cases (τ'.subst δ) δ) (Tp.Var.cases ⟨HT Δ δ η τ', HT.expand⟩ η) τ .there (.mk τ') (Tp.Var.cases (by simp!) (by simp!)) (Tp.Var.cases (by simp!) (by simp!)) (by exact e)

def Tm.HTSubst Δ (δ : Tp.Subst Δ .nil) (η : ∀ α, Cand (δ α)) (Γ : Ctx Δ) (γ : Subst' Δ .nil δ Γ .nil) : Prop :=
  ∀ {τ} x, HT Δ δ η τ (γ x)

def Tm.HT' Δ Γ τ (e : Tm Δ Γ τ) : Prop :=
  ∀ δ η γ, (ht_γ : HTSubst Δ δ η Γ @γ) → HT Δ δ η τ (e.subst' @γ)

theorem Tm.ftlr : ∀ e, HT' Δ Γ τ e
  | var x, δ, η, γ, ht_γ => ht_γ x
  | lam e, δ, η, γ, ht_γ => ⟨_, .refl, fun e₁ ht => by simp; exact ftlr e δ η (Var.cases e₁ γ) (Var.cases ht ht_γ)⟩
  | app e e₁, δ, η, γ, ht_γ => let ⟨_, r, ht⟩ := ftlr e δ η γ ht_γ; .expand _ _ (r.app.trans (.step .app_lam .refl)) (ht (e₁.subst' γ) (ftlr e₁ δ η γ ht_γ))
  | gen e, δ, η, γ, ht_γ => ⟨_, .refl, fun τ' C => by simp; exact ftlr e (Tp.Var.cases τ' δ) (Tp.Var.cases C η) γ.weakenTp' (Var.casesRename fun x => by simp; exact HT.rename.mp (ht_γ x))⟩
  | inst e τ, δ, η, γ, ht_γ => let ⟨e', r, ht⟩ := ftlr e δ η γ ht_γ; .expand _ (e'.substTp (.mk (τ.subst δ)) |>.cast rfl (by simp!)) (.cast (r.inst.trans (.step .inst_gen .refl))) <| have := ht (τ.subst δ) ⟨HT Δ δ η τ, HT.expand⟩; by rename_i τ'; simp! at this ⊢; have comp := @HT.compose Δ δ η τ' τ (e'.substTp (.mk (τ.subst δ)) |>.cast rfl (by simp!)); simp at comp; have := comp.mpr this; exact this

theorem Tm.termination (e : Tm .nil .nil τ) : Nonempty (Σ e', Val e' × Reduces e e') :=
  match τ, e, ftlr e .var nofun nofun nofun with
  | .arr τ₁ τ₂, e, ⟨e', r, _⟩ => ⟨.lam (e'.cast (by simp) (by simp)), .lam, by simp at r; have := r.cast (hΓ := rfl) (hτ := show (τ₁.arr τ₂).subst .var = τ₁.arr τ₂ by simp); simp at this; exact this⟩
  | .all τ, _, ⟨e, r, _⟩ => ⟨.gen (e.cast rfl (by simp)), .gen, by simp! at r; have := r.cast (hΓ := rfl) (hτ := show τ.all.subst .var = τ.all by simp); simp at this; exact this⟩
