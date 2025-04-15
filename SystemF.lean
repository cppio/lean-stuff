inductive Tp.Ctx
  | nil
  | cons (Δ : Ctx)

inductive Tp.Var : (Δ : Ctx) → Type
  | here : Var (.cons Δ)
  | there (α : Var Δ) : Var Δ.cons
  deriving DecidableEq

@[elab_as_elim]
def Tp.Var.cases {motive : (α : Var (.cons Δ)) → Sort u} (here : motive here) (there : ∀ α, motive (there α)) : ∀ α, motive α
  | .here => here
  | .there α => there α

@[simp] theorem Tp.Var.cases_here {here there} : @cases Δ motive here there .here = here := rfl
@[simp] theorem Tp.Var.cases_there {here there α} : @cases Δ motive here there (.there α) = there α := rfl

@[simp]
theorem Tp.Var.cases_commute {here there} (f : (b : β) → γ) : (α : Var (.cons Δ)) → f (cases here there α) = cases (f here) (fun α => f (there α)) α
  | .here | .there _ => rfl

inductive Tp : (Δ : Tp.Ctx) → Type
  | var (α : Tp.Var Δ) : Tp Δ
  | arr (τ₁ τ₂ : Tp Δ) : Tp Δ
  | all (τ : Tp Δ.cons) : Tp Δ
  deriving DecidableEq

def Tp.Rename (Δ Δ' : Ctx) : Type :=
  (α : Var Δ) → Var Δ'

@[simp]
def Tp.Rename.weaken (δ : Rename Δ Δ') : Rename Δ.cons Δ'.cons :=
  Var.cases .here fun α => (δ α).there

@[simp]
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

@[simp]
def Tp.subst (δ : Subst Δ Δ') : (τ : Tp Δ) → Tp Δ'
  | var α => δ α
  | arr τ₁ τ₂ => arr (τ₁.subst δ) (τ₂.subst δ)
  | all τ => all (τ.subst δ.weaken)

@[simp]
theorem Tp.rename_id : rename (Δ := Δ) (·) = (·) := by
  funext τ
  generalize h : (·) = δ
  replace h α := congrFun h.symm α
  induction τ with simp [*]
  | all _ ih => apply ih; apply Var.cases <;> simp [h]

@[simp]
theorem Tp.subst_var : subst (Δ := Δ) var = (·) := by
  funext τ
  generalize h : var = δ
  replace h α := congrFun h.symm α
  induction τ with simp [*]
  | all _ ih => apply ih; apply Var.cases <;> simp [h]

@[simp]
theorem Tp.rename_rename {δ₁ : Rename Δ Δ'} {δ₂ : Rename Δ' Δ''} {τ} : rename δ₂ (rename δ₁ τ) = rename (fun α => δ₂ (δ₁ α)) τ := by
  generalize h : (fun α => δ₂ (δ₁ α)) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with simp [*]
  | all _ ih => apply ih; apply Var.cases <;> simp [h]

@[simp]
theorem Tp.subst_rename {δ₁ : Rename Δ Δ'} {δ₂ : Subst Δ' Δ''} {τ} : subst δ₂ (rename δ₁ τ) = subst (fun α => δ₂ (δ₁ α)) τ := by
  generalize h : (fun α => δ₂ (δ₁ α)) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with simp [*]
  | all _ ih => apply ih; apply Var.cases <;> simp [h]

@[simp]
theorem Tp.rename_subst {δ₁ : Subst Δ Δ'} {δ₂ : Rename Δ' Δ''} {τ} : rename δ₂ (subst δ₁ τ) = subst (fun α => (δ₁ α).rename δ₂) τ := by
  generalize h : (fun α => (δ₁ α).rename δ₂) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with simp [*]
  | all _ ih => apply ih; apply Var.cases <;> simp [← h]

@[simp]
theorem Tp.subst_subst {δ₁ : Subst Δ Δ'} {δ₂ : Subst Δ' Δ''} {τ} : subst δ₂ (subst δ₁ τ) = subst (fun α => (δ₁ α).subst δ₂) τ := by
  generalize h : (fun α => (δ₁ α).subst δ₂) = δ
  replace h := congrFun h
  induction τ generalizing Δ' Δ'' with simp [*]
  | all _ ih => apply ih; apply Var.cases <;> simp [← h]

example (τ : Tp Δ) : Tp Δ.cons := τ.rename .there
example (τ : Tp Δ.cons) (τ' : Tp Δ) : Tp Δ := τ.subst (.mk τ')

inductive Tm.Ctx (Δ : Tp.Ctx)
  | nil
  | cons (Γ : Ctx Δ) (τ : Tp Δ)

@[simp]
def Tm.Ctx.map (δ : (τ : Tp Δ) → Tp Δ') : (Γ : Ctx Δ) → Ctx Δ'
  | nil => nil
  | cons Γ τ => cons (Γ.map δ) (δ τ)

@[simp]
theorem Tm.Ctx.map_id (h : ∀ τ, δ τ = τ) : map δ Γ = Γ :=
  by induction Γ with simp [*]

@[simp]
theorem Tm.Ctx.map_map :  map δ₂ (map δ₁ Γ) = map (fun τ => δ₂ (δ₁ τ)) Γ :=
  by induction Γ with simp [*]

inductive Tm.Var Δ (τ : Tp Δ) : (Γ : Ctx Δ) → Type
  | here : Var Δ τ (.cons Γ τ)
  | there (x : Var Δ τ Γ) : Var Δ τ (Γ.cons τ')
  deriving DecidableEq

@[elab_as_elim]
def Tm.Var.cases {motive : ∀ τ, (x : Var Δ τ (.cons Γ τ')) → Sort u} (here : motive τ' here) (there : ∀ {τ} x, motive τ (there x)) : ∀ {τ} x, motive τ x
  | _, .here => here
  | _, .there x => there x

@[simp] theorem Tm.Var.cases_here {here there} : @cases Δ Γ τ' motive here there τ' .here = here := rfl
@[simp] theorem Tm.Var.cases_there {here there x} : @cases Δ Γ τ' motive here there τ (.there x) = there x := rfl

@[simp]
def Tm.Var.map (δ : (τ : Tp Δ) → Tp Δ') {τ Γ} : (x : Var Δ τ Γ) → Var Δ' (δ τ) (Γ.map δ)
  | here => here
  | there x => there (x.map δ)

@[elab_as_elim, simp]
def Tm.Var.casesMap {motive : ∀ τ, Var Δ' τ (Γ.map δ) → Sort u} (k : ∀ {τ} (x : Var Δ τ Γ), motive (δ τ) (x.map δ)) {τ} x : motive τ x :=
  match Γ, τ, x with
  | .cons .., _, .here => k here
  | .cons .., _, .there x => x.casesMap (motive := fun τ x => motive τ x.there) fun x => k x.there

@[simp]
theorem Tm.Var.casesMap_map : @casesMap Δ' Δ Γ δ motive k (δ τ) (x.map δ) = k x :=
  by induction x with simp [*]

inductive Tm : ∀ Δ, (Γ : Tm.Ctx Δ) → (τ : Tp Δ) → Type
  | var (x : Tm.Var Δ τ Γ) : Tm Δ Γ τ
  | lam (e : Tm Δ (Γ.cons τ₁) τ₂) : Tm Δ Γ (τ₁.arr τ₂)
  | app (e : Tm Δ Γ (τ₁.arr τ₂)) (e₁ : Tm Δ Γ τ₁) : Tm Δ Γ τ₂
  | gen (e : Tm (.cons Δ) (Γ.map (.rename .there)) τ) : Tm Δ Γ (.all τ)
  | inst (e : Tm Δ Γ (.all τ)) τ' : Tm Δ Γ (τ.subst (.mk τ'))

theorem hcongrArg₂ {α : Sort u} {β : α → Sort v} {γ : ∀ a, β a → Sort w} (f : ∀ a b, γ a b) {a₁ a₂ : α} (ha : a₁ = a₂) {b₁ : β a₁} {b₂ : β a₂} (hb : HEq b₁ b₂) : HEq (f a₁ b₁) (f a₂ b₂) :=
  by cases ha; cases hb; rfl

theorem Tm.rec_cast {τ τ' : Tp Δ} (h : τ = τ') {var lam app gen inst} {t : Tm Δ Γ τ} : @rec motive @var @lam @app @gen @inst Δ Γ τ' (h ▸ t) = (h.rec (motive := fun τ' _ => _ = motive Δ Γ τ' _) rfl).mp (@rec motive @var @lam @app @gen @inst Δ Γ τ t) :=
  eq_of_heq (.trans (hcongrArg₂ _ h.symm (h.rec (.refl _))) (have := h.rec (motive := fun τ' _ => _ = motive Δ Γ τ' _) rfl; (this.rec (.refl _) : HEq _ (this.mp _))))

def Tm.decEq {τ τ'} : ∀ (h : τ = τ') (e : Tm Δ Γ τ) (e' : Tm Δ Γ τ'), Decidable (h ▸ e = e')
  | h, var x, var x' => by cases h; exact if h : x = x'
                                          then isTrue (h ▸ rfl)
                                          else isFalse (by simp [h])
  | h, lam e, lam e' => by cases h; exact match decEq rfl e e' with
                                          | isTrue h => isTrue (h ▸ rfl)
                                          | isFalse h => isFalse (by simp [h])
  | h, app (τ₁ := τ₁) e e₁, app (τ₁ := τ₁') e' e₁' => have ih := @e.decEq
                                                      by cases h; exact if h : τ₁ = τ₁'
                                                                        then by cases h; exact
                                                                             match ih _ rfl e', decEq rfl e₁ e₁' with
                                                                             | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
                                                                             | isFalse h, _ => isFalse (by simp [h])
                                                                             | _, isFalse h => isFalse (by simp [h])
                                                                        else isFalse (by simp [h])
  | h, gen e, gen e' => by cases h; exact match decEq rfl e e' with
                                          | isTrue h => isTrue (h ▸ rfl)
                                          | isFalse h => isFalse (by simp [h])
  | _, inst (τ := τ₁) e τ, inst (τ := τ₁') e' τ' => if h : τ = τ'
                                                    then if h₁ : τ₁ = τ₁'
                                                         then by cases h; cases h₁; exact match decEq rfl e e' with
                                                                                          | isTrue h => isTrue (h ▸ rfl)
                                                                                          | isFalse h => isFalse (by simp [h])
                                                         else isFalse fun h' => (rec_cast _).mp (Tm.noConfusion h') fun | _, _, .refl _, _, _ => h₁ rfl
                                                    else isFalse fun h' => (rec_cast _).mp (Tm.noConfusion h') fun | _, _, _, _, .refl _ => h rfl
  | h, var _, lam _
  | h, var _, app ..
  | h, var _, gen _
  | h, var _, inst ..
  | h, lam _, var _
  | h, lam _, app ..
  | h, app .., var _
  | h, app .., lam _
  | h, app .., gen _
  | h, app .., inst ..
  | h, gen _, var _
  | h, gen _, app ..
  | h, inst .., var _
  | h, inst .., app .. => isFalse (by cases h; simp)
  | h, lam _, inst ..
  | h, gen _, inst ..
  | h, inst .., lam _
  | h, inst .., gen _ => isFalse fun h' => (rec_cast h).mp (Tm.noConfusion h')

instance : DecidableEq (Tm Δ Γ τ)
  | e, e' => e.decEq rfl e'

def Tm.Var.cast {τ τ' Γ Γ'} (hτ : τ = τ') (hΓ : Γ = Γ') (x : Var Δ τ Γ) : Var Δ τ' Γ' :=
  hτ ▸ hΓ ▸ x

@[simp]
theorem Tm.Var.cast_there : @cast Δ τ τ' (.cons Γ τ'') (.cons Γ' τ''') hτ hΓ (.there x) = there (x.cast hτ (Ctx.cons.inj hΓ).left) :=
  by cases hτ; cases hΓ; rfl

@[simp]
theorem Tm.Var.cast_rfl : cast rfl rfl x = x :=
  rfl

@[simp]
theorem Tm.Var.cast_cast : cast hτ₂ hΓ₂ (cast hτ₁ hΓ₁ x) = cast (hτ₁.trans hτ₂) (hΓ₁.trans hΓ₂) x :=
  by cases hτ₁; cases hΓ₁; rfl

theorem Tm.Var.cases_cast {motive : ∀ τ, (x : Var Δ τ (.cons Γ τ')) → Sort u} {here there} (hτ : τ = τ'') (hΓ : .cons Γ' τ = Γ.cons τ') : HEq (@cases Δ Γ τ' motive here there τ'' (cast hτ hΓ .here)) here :=
  by cases hτ; cases hΓ; rfl

def Tm.cast {Γ Γ' τ τ'} (hΓ : Γ = Γ') (hτ : τ = τ') (e : Tm Δ Γ τ) : Tm Δ Γ' τ' :=
  hΓ ▸ hτ ▸ e

@[simp]
theorem Tm.cast_var : @cast Δ Γ Γ' τ τ' hΓ hτ (var x) = var (x.cast hτ hΓ) :=
  by cases hΓ; cases hτ; rfl

@[simp]
theorem Tm.cast_lam : @cast Δ Γ Γ' (.arr τ₁ τ₂) (.arr τ₁' τ₂') hΓ hτ (lam e) = lam (e.cast (congr (congrArg Ctx.cons hΓ) (Tp.arr.inj hτ).left) (Tp.arr.inj hτ).right) :=
  by cases hΓ; cases hτ; rfl

@[simp]
theorem Tm.cast_app : @cast Δ Γ Γ' τ τ' hΓ hτ (app e e₁) = app (e.cast hΓ (congrArg _ hτ)) (e₁.cast hΓ rfl) :=
  by cases hΓ; cases hτ; rfl

@[simp]
theorem Tm.cast_gen : @cast Δ Γ Γ' (.all τ) (.all τ') hΓ hτ (gen e) = gen (e.cast (congrArg _ hΓ) (Tp.all.inj hτ)) :=
  by cases hΓ; cases hτ; rfl

@[simp]
theorem Tm.cast_rfl : cast rfl rfl e = e :=
  rfl

@[simp]
theorem Tm.cast_cast : cast hΓ₂ hτ₂ (cast hΓ₁ hτ₁ e) = cast (hΓ₁.trans hΓ₂) (hτ₁.trans hτ₂) e :=
  by cases hΓ₁; cases hτ₁; rfl

@[simp]
def Tm.renameTp (δ : Tp.Rename Δ Δ') {Γ τ} : (e : Tm Δ Γ τ) → Tm Δ' (Γ.map (.rename δ)) (τ.rename δ)
  | var x => var (x.map (.rename δ))
  | lam e => lam (e.renameTp δ)
  | app e e₁ => app (e.renameTp δ) (e₁.renameTp δ)
  | gen e => gen (e.renameTp δ.weaken |>.cast (by simp) rfl)
  | inst e τ => inst (e.renameTp δ) (τ.rename δ) |>.cast rfl (by simp)

@[simp]
def Tm.substTp (δ : Tp.Subst Δ Δ') {Γ τ} : (e : Tm Δ Γ τ) → Tm Δ' (Γ.map (.subst δ)) (τ.subst δ)
  | var x => var (x.map (.subst δ))
  | lam e => lam (e.substTp δ)
  | app e e₁ => app (e.substTp δ) (e₁.substTp δ)
  | gen e => gen (e.substTp δ.weaken |>.cast (by simp) rfl)
  | inst e τ => inst (e.substTp δ) (τ.subst δ) |>.cast rfl (by simp)

def Tm.Rename Δ (Γ Γ' : Ctx Δ) : Type :=
  ∀ {τ}, (x : Var Δ τ Γ) → Var Δ τ Γ'

def Tm.Rename.map (δ : (τ : Tp Δ) → Tp Δ') {Γ Γ'} (γ : Rename Δ Γ Γ') : Rename Δ' (Γ.map δ) (Γ'.map δ) :=
  Var.casesMap fun x => (γ x).map δ

@[simp]
def Tm.Rename.weaken (γ : Rename Δ Γ Γ') {τ} : Rename Δ (Γ.cons τ) (Γ'.cons τ) :=
  Var.cases .here fun x => (γ x).there

@[simp]
def Tm.rename (γ : Rename Δ Γ Γ') {τ} : (e : Tm Δ Γ τ) → Tm Δ Γ' τ
  | var x => var (γ x)
  | lam e => lam (e.rename γ.weaken)
  | app e e₁ => app (e.rename @γ) (e₁.rename @γ)
  | gen e => gen (e.rename (γ.map (.rename .there)))
  | inst e τ => inst (e.rename @γ) τ

def Tm.Subst Δ (Γ Γ' : Ctx Δ) : Type :=
  ∀ {τ}, (x : Var Δ τ Γ) → Tm Δ Γ' τ

@[simp]
def Tm.Subst.mk (e : Tm Δ Γ τ) : Subst Δ (Γ.cons τ) Γ :=
  Var.cases e .var

def Tm.Subst.rename (δ : Tp.Rename Δ Δ') {Γ Γ'} (γ : Subst Δ Γ Γ') : Subst Δ' (Γ.map (.rename δ)) (Γ'.map (.rename δ)) :=
  Var.casesMap fun x => (γ x).renameTp δ

@[simp]
def Tm.Subst.weaken (γ : Subst Δ Γ Γ') {τ} : Subst Δ (Γ.cons τ) (Γ'.cons τ) :=
  Var.cases (var .here) fun x => (γ x).rename .there

@[simp]
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
theorem Tm.Rename.map_map : map δ γ (x.map δ) = (γ x).map δ := by
  induction x with
  | here => rfl
  | there x ih => exact ih

@[simp]
theorem Tm.rename_id : rename (·) e = e := by
  generalize h : (fun {τ} x => x) = γ
  replace h {τ} x := congrFun (congrFun h.symm τ) x
  induction e with simp [*]
  | lam e ih => exact ih _ (Var.cases rfl fun x => congrArg _ (h x))
  | gen e ih => exact ih _ (Var.casesMap fun x => by simp; exact congrArg _ (h x))

@[simp]
theorem Tm.Subst.rename_rename' : rename δ γ (x.map (.rename δ)) = (γ x).renameTp δ := by
  induction x with
  | here => rfl
  | there x ih => exact ih

@[simp]
theorem Tm.Var.heq_here {τ τ' Γ Γ'} (hτ : τ = τ') (hΓ : Γ = Γ') : HEq (@here Δ τ Γ) (@here Δ τ' Γ') :=
  by cases hτ; cases hΓ; rfl

@[simp]
theorem Tm.Var.map_id (h : ∀ τ, δ τ = τ) : map δ x = x.cast (by simp [h]) (by simp [h]) := by
  induction x with
  | here => simp [← heq_eq_eq, h]
  | there x ih => simp [ih]

@[simp]
theorem Tm.Var.map_map (h : ∀ α, δ₂ (δ₁ α) = δ₂' (δ₁' α)) : cast rfl (by simp [h]) (map δ₂ (map δ₁ x)) = cast (by simp [h]) rfl (map δ₂' (map δ₁' x)) := by
  induction x with
  | here =>
    have {Δ} {τ τ' τ'' : Tp Δ} {Γ Γ' Γ'' : Ctx Δ} (hτ : τ = τ'') (hτ' : τ' = τ'') (hΓ : Γ.cons τ = Γ'') (hΓ'' : Γ'.cons τ' = Γ'') : cast hτ hΓ here = cast hτ' hΓ'' here := by
      subst_eqs
      rfl
    exact this ..
  | there x ih => simp [ih]

theorem Tm.Var.map_map' (h : ∀ α, δ₂ (δ₁ α) = δ₂' (δ₁' α)) : HEq (map δ₂ (map δ₁ x)) (map δ₂' (map δ₁' x)) := by
  have := heq_of_eq (map_map h (x := x))
  simp [-heq_eq_eq] at this
  exact this

@[simp]
theorem Tm.Var.map_map'' (h : ∀ α, δ₂ (δ₁ α) = δ α) : map δ₂ (map δ₁ x) = cast (by simp [h]) (by simp [h]) (map δ x) := by
  induction x with
  | here =>
    have {Δ} {τ τ' : Tp Δ} {Γ Γ' : Ctx Δ} {hτ : τ = τ'} {hΓ : Γ.cons τ = Γ'.cons τ'} : here = cast hτ hΓ here := by
      subst_eqs
      rfl
    exact this
  | there x ih => simp [ih]

@[simp]
theorem Tm.renameTp_cast : renameTp δ (cast hΓ hτ e) = cast (congrArg _ hΓ) (congrArg _ hτ) (e.renameTp δ) :=
  by subst_eqs; simp

@[simp]
theorem Tm.substTp_cast : substTp δ (cast hΓ hτ e) = cast (congrArg _ hΓ) (congrArg _ hτ) (e.substTp δ) :=
  by subst_eqs; simp

theorem Tm.substTp_cong (eq : δ = δ') : substTp δ e = cast (by simp [eq]) (by simp [eq]) (substTp δ' e) :=
  by cases eq; simp

theorem Tm.inst_cong {Γ₁ Γ₂ τ₁ τ₂ e₁ e₂ τ'₁ τ'₂} (hΓ : Γ₁ = Γ₂) (hτ : τ₁ = τ₂) (he : HEq e₁ e₂) (hτ : τ'₁ = τ'₂) : HEq (@inst Δ Γ₁ τ₁ e₁ τ'₁) (@inst Δ Γ₂ τ₂ e₂ τ'₂) := by
  subst_eqs
  rfl

@[simp]
theorem Eq.rec_heq {refl} : HEq (@rec α a motive refl b h) rhs = HEq refl rhs :=
  by cases h; rfl

@[simp]
theorem Eq.rec_heq' {refl} : HEq lhs (@rec α a motive refl b h) = HEq lhs refl :=
  by cases h; rfl

@[simp]
theorem Tm.renameTp_renameTp {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Rename Δ' Δ''} : renameTp δ₂ (renameTp δ₁ e) = (renameTp (fun α => δ₂ (δ₁ α)) e).cast (by simp) (by simp) := by
  induction e generalizing Δ' Δ'' with simp [*]
  | gen =>
    simp [← heq_eq_eq]
    congr
    funext α
    cases α <;> rfl
  | inst =>
    simp [← heq_eq_eq]
    apply inst_cong <;> simp
    rfl

@[simp]
theorem Tm.substTp_substTp {δ₁ : Tp.Subst Δ Δ'} {δ₂ : Tp.Subst Δ' Δ''} {e : Tm Δ Γ τ} : substTp δ₂ (substTp δ₁ e) = (substTp (fun α => (δ₁ α).subst δ₂) e).cast (by simp) (by simp) := by
  induction e generalizing Δ' Δ'' with simp [*]
  | gen =>
    simp [← heq_eq_eq]
    congr
    funext α
    cases α <;> simp
  | inst =>
    simp [← heq_eq_eq]
    apply inst_cong <;> simp
    congr
    funext α
    cases α <;> simp

@[simp]
theorem Tm.Subst.rename_cast : rename δ γ (.cast hτ rfl x) = (rename δ γ x).cast rfl hτ :=
  by cases hτ; simp

theorem Tm.Subst.rename_rename : rename δ₂ (rename δ₁ γ) x = cast (by simp) rfl (rename (fun α => δ₂ (δ₁ α)) γ (x.cast rfl (by simp))) := by
  refine x.casesMap fun x => ?_
  refine x.casesMap fun x => ?_
  simp [-Var.map_map'']
  simp

@[simp]
theorem Tm.Rename.map_map' {γ : Rename Δ Γ Γ'} {δ₁ : (τ : Tp Δ) → Tp Δ'} {δ₂ : (τ : Tp Δ') → Tp Δ''} {x : Var _ τ _} : map δ₂ (map δ₁ @γ) x = x.casesMap (Var.casesMap fun x => (γ x).map δ₁ |>.map δ₂) := by
  refine x.casesMap fun x => ?_
  refine x.casesMap fun x => ?_
  simp [-Var.map_map'']

@[simp]
theorem Tm.Rename.there_rename {γ : Rename Δ Γ Γ'} : (map δ γ x).there = map δ (fun x => (γ x).there (τ' := τ)) x := by
  refine x.casesMap fun x => ?_
  simp

@[simp]
theorem Tm.subst_var : subst var e = e := by
  generalize h : (fun {τ} x => var x) = γ
  replace h {τ} x := congrFun (congrFun h.symm τ) x
  induction e with simp [*]
  | lam e ih => exact ih _ (Var.cases rfl (by simp [h]))
  | gen e ih => exact ih _ (Var.casesMap (by simp [h]))

@[simp]
theorem Tp.Subst.weaken_var : @weaken Δ _ var = var := by
  funext α
  cases α <;> rfl

theorem Tm.rename_rename' (h : ∀ {τ} (x : Var _ τ _), γ₂ (γ₁ x) = γ x) : Rename.map δ γ₂ (Rename.map δ γ₁ x) = Rename.map δ γ x := by
  refine x.casesMap fun x => ?_
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
theorem Tm.Var.casesMap_rename_cast : @casesMap Δ' Δ Γ (.rename δ) motive @k τ' (@cast Δ' (.rename δ τ) τ' (Γ.map (.rename δ)) (Γ.map (.rename δ)) hτ rfl (.map (.rename δ) x)) = hτ.rec (motive := fun τ' hτ => motive τ' (cast hτ rfl (x.map (.rename δ)))) (cast_rfl (x := x.map (.rename δ)) ▸ k x :) := by
  cases hτ
  induction x with
  | here => rfl
  | there x ih =>
    apply ih.trans
    rfl

@[simp]
theorem Tm.Var.casesMap_subst_cast : @casesMap Δ' Δ Γ (.subst δ) motive @k τ' (@cast Δ' (.subst δ τ) τ' (Γ.map (.subst δ)) (Γ.map (.subst δ)) hτ rfl (.map (.subst δ) x)) = hτ.rec (motive := fun τ' hτ => motive τ' (cast hτ rfl (x.map (.subst δ)))) (cast_rfl (x := x.map (.subst δ)) ▸ k x :) := by
  cases hτ
  induction x with
  | here => rfl
  | there x ih =>
    apply ih.trans
    rfl

theorem Tm.Var.heq_of_eq_cast (eq : cast hτ hΓ x = x') : HEq x x' :=
  by cases eq; simp

theorem Tm.heq_of_eq_cast (eq : cast hΓ hτ e = e') : HEq e e' :=
  by cases eq; simp

@[simp]
theorem Tm.substTp_var {e : Tm Δ Γ τ} : substTp .var e = e.cast (by simp) (by simp) := by
  have {Δ} : Tp.Subst.weaken (Δ := Δ) .var = .var := by
    funext α
    cases α <;> rfl
  induction e with simp [*]
  | gen e ih => simp [← heq_eq_eq]; rewrite [this]; simp [ih]
  | inst e τ ih => simp [← heq_eq_eq]; apply inst_cong <;> simp [this]

@[simp]
theorem Tm.substTp_renameTp {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Subst Δ' Δ''} : substTp δ₂ (renameTp δ₁ e) = (substTp (fun α => δ₂ (δ₁ α)) e).cast (by simp) (by simp) := by
  induction e generalizing Δ' Δ'' with simp [*]
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
  induction e generalizing Δ' Δ'' with simp [*]
  | gen e ih =>
    have : @Eq (Tp.Subst ..) (fun α => Tp.rename δ₂.weaken (Tp.Var.cases (.var .here) (fun α => (δ₁ α).rename .there) α)) (.weaken fun α => (δ₁ α).rename δ₂) := by
      funext α
      cases α <;> simp
    rewrite [substTp_cong this]
    simp
  | inst e τ ih =>
    simp [← heq_eq_eq]
    apply inst_cong <;> simp
    congr
    funext α
    cases α <;> simp

theorem Tm.rename_rename'' {γ₁ : Subst Δ Γ Γ'} {γ₂ : Rename Δ Γ' Γ''} {γ : Subst Δ Γ Γ''} (h : ∀ {τ} (x : Var _ τ _), (γ₁ x).rename @γ₂ = γ x) : rename (γ₂.map (.rename δ)) (γ₁.rename δ x) = γ.rename δ x := by
  refine x.casesMap fun x => ?_
  simp [← h]
  generalize γ₁ x = e
  clear h γ₁
  rename_i Δ' τ x' _
  clear Γ τ x' γ x
  induction e generalizing Δ' with simp [*]
  | lam e ih =>
    simp [← ih]
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesMap fun x => ?_
    simp [Rename.map]
  | gen e ih =>
    simp [← ih]
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    refine x.casesMap fun x => ?_
    simp [← heq_eq_eq]
    rfl

@[simp]
theorem Tm.rename_renameTp : rename (Rename.map (.rename δ) @γ) (renameTp δ e) = renameTp δ (rename @γ e) := by
  rename_i Δ Δ' _ _ _
  induction e generalizing Δ' with simp [*]
  | lam e ih =>
    refine .trans ?_ (ih (γ := γ.weaken))
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesMap fun x => ?_
    simp [Rename.map]
  | gen e ih =>
    apply cast_flip
    refine .trans ?_ ih
    simp
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    refine x.casesMap fun x => ?_
    simp [← heq_eq_eq]
    simp

theorem Tm.cast_subst {γ : Subst Δ Γ Γ'} : cast hΓ hτ (subst γ e) = subst (fun x => (γ x).cast hΓ rfl) (e.cast rfl hτ) :=
  by subst_eqs; simp

@[simp]
theorem Tm.subst_cast {γ : Subst Δ Γ Γ'} : subst γ (cast hΓ hτ e) = cast rfl hτ (subst (fun x => γ (x.cast rfl hΓ)) e) :=
  by subst_vars; simp

theorem Tm.subst_rename'' {γ₁ : Subst Δ Γ Γ'} {γ₂ : Subst Δ Γ' Γ''} {γ : Subst Δ Γ Γ''} (h : ∀ {τ} (x : Var _ τ _), (γ₁ x).subst @γ₂ = γ x) : subst (γ₂.rename δ) (γ₁.rename δ x) = γ.rename δ x := by
  refine x.casesMap fun x => ?_
  simp [← h]
  generalize γ₁ x = e
  clear h γ₁
  rename_i Δ' τ x' _
  clear Γ τ x' γ x
  induction e generalizing Δ' with simp [*]
  | lam e ih =>
    simp [← ih]
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesMap fun x => ?_
    simp [Subst.rename]
    simp [← rename_renameTp]
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    simp
  | gen e ih =>
    simp [← ih]
    simp [cast_subst]
    congr
    funext τ x
    simp [Subst.rename_rename]

theorem Tm.subst_rename' (h : ∀ {τ} (x : Var _ τ _), γ₂ (γ₁ x) = γ x) : Subst.rename δ γ₂ (Rename.map (.rename δ) γ₁ x) = Subst.rename δ γ x := by
  refine x.casesMap fun x => ?_
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
theorem Tm.subst_subst : subst @γ₂ (subst @γ₁ e) = subst (fun x => (γ₁ x).subst @γ₂) e := by
  generalize h : (fun {τ} x => (γ₁ x).subst @γ₂) = γ
  replace h {τ} x := congrFun (congrFun h τ) x
  induction e with
  | var x => exact h x
  | lam e ih => exact congrArg lam (ih _ <| Var.cases rfl fun x => by simp [Rename.weaken, Subst.weaken, Var.cases, ← h x])
  | app e e₁ ih ih₁ => exact congr (congrArg app (ih _ h)) (ih₁ _ h)
  | gen e ih => exact congrArg gen (ih _ fun _ => subst_rename'' h)
  | inst e τ ih => exact congrArg (inst · τ) (ih _ h)

@[simp]
theorem Tm.substTp_rename {δ : Tp.Subst Δ Δ'} {γ : Rename Δ Γ Γ'} {e : Tm Δ Γ τ} : substTp δ (rename γ e) = (e.substTp δ).rename (Var.casesMap fun x => (γ x).map (.subst δ)) := by
  induction e generalizing Δ' with simp [*]
  | lam e ih =>
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesMap fun x => ?_
    simp
  | gen e ih =>
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    refine x.casesMap fun x => ?_
    simp [Rename.map]
    have : x.map (.subst (fun α => (δ α).rename .there)) = ((x.map (.subst δ)).map (.rename .there)).cast (by simp) (by simp) := by
      simp
    simp [this, ← heq_eq_eq]
    have : ((x.map (.subst δ)).map (.rename .there)).cast (by simp) (by simp) = (x.map (.rename .there)).map (.subst δ.weaken) := by
      simp
    rewrite [this]
    simp only [Var.casesMap_map]
    simp

@[simp]
theorem Tm.substTp_subst {γ : Subst Δ Γ Γ'} {δ : Tp.Subst Δ Δ'} : substTp δ (subst γ e) = subst (Var.casesMap fun x => (γ x).substTp δ) (substTp δ e) := by
  induction e generalizing Δ' with simp [*]
  | lam e ih =>
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesMap fun x => ?_
    simp
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    simp
  | gen e ih =>
    simp [cast_subst]
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    refine x.casesMap fun x => ?_
    simp [Rename.map]
    have : x.map (.subst (fun α => (δ α).rename .there)) = ((x.map (.subst δ)).map (.rename .there)).cast (by simp) (by simp) := by
      simp
    simp [this, ← heq_eq_eq]
    have : ((x.map (.subst δ)).map (.rename .there)).cast (by simp) (by simp) = (x.map (.rename .there)).map (.subst δ.weaken) := by
      simp
    rewrite [this]
    simp only [Var.casesMap_map]
    simp

example (e : Tm Δ Γ τ) : Tm Δ.cons (Γ.map (.rename .there)) (τ.rename .there) := e.renameTp .there
example (e : Tm Δ Γ τ) : Tm Δ (Γ.cons τ') τ := e.rename .there
example (e : Tm (.cons Δ) Γ τ) (τ' : Tp Δ) : Tm Δ (Γ.map (.subst (.mk τ'))) (τ.subst (.mk τ')) := e.substTp (.mk τ')
example (e : Tm Δ (Γ.cons τ') τ) (e' : Tm Δ Γ τ') : Tm Δ Γ τ := e.subst (Tm.Subst.mk e')

@[simp]
theorem Tm.subst_renameTp : subst (Subst.rename δ @γ) (renameTp δ e) = renameTp δ (subst @γ e) := by
  rename_i Δ Δ' _ _ _
  induction e generalizing Δ' with simp [*]
  | lam e ih =>
    refine .trans ?_ (ih (γ := γ.weaken))
    congr
    funext τ x
    cases x
    . rfl
    next x =>
    refine x.casesMap fun x => ?_
    change _ = Subst.rename δ γ.weaken (.map (.rename δ) x.there)
    simp only [Subst.rename_rename']
    simp
    generalize γ x = e
    simp [← rename_renameTp]
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    simp
  | gen e ih =>
    apply cast_flip
    refine .trans ?_ ih
    simp [cast_subst]
    congr
    funext τ x
    refine x.casesMap fun x => ?_
    refine x.casesMap fun x => ?_
    simp only [Subst.rename_rename']
    simp only [Var.map_map (δ₁ := .rename .there) (δ₂ := .rename δ.weaken) (δ₁' := .rename δ) (δ₂' := .rename .there) (by simp) (x := x)]
    simp only [Subst.rename_cast, cast_cast, Subst.rename_rename']
    simp

theorem Tm.rename_cong {Γ₁ Γ₂ γ₁ γ₂} (hΓ : Γ₁ = Γ₂) (hγ : ∀ {τ} (x : Var Δ τ Γ), HEq (γ₁ x) (γ₂ x)) : HEq (@rename Δ Γ Γ₁ γ₁ τ e) (@rename Δ Γ Γ₂ γ₂ τ e) :=
  by cases hΓ; cases funext fun τ => funext fun x => eq_of_heq (@hγ τ x); rfl

@[simp]
theorem Tp.subst_nil : @subst .nil .nil δ = (·) := by
  cases show δ = var from funext nofun
  exact subst_var

@[simp]
theorem Tm.subst_nil : @subst .nil .nil .nil γ τ e = e := by
  cases show @γ = fun {τ} x => var x from funext fun τ => funext nofun
  simp

theorem Tm.Var.cases_casesMap {here there} : @casesMap Δ' Δ (.cons Γ τ') δ motive (cases here there) τ x = cases here (casesMap there) x :=
  x.casesMap (cases rfl fun _ => rfl)

theorem Tm.inst_inj_cast {τ₂' : Tp Δ} (hτ : Tp.subst (.mk τ₁') τ₁ = Tp.subst (.mk τ₂') τ₂) (he : hτ ▸ @inst Δ Γ τ₁ e₁ τ₁' = @inst Δ Γ τ₂ e₂ τ₂') : τ₁ = τ₂ ∧ τ₁' = τ₂' :=
  (rec_cast hτ).mp (Tm.noConfusion he) fun _ _ hτ _ hτ' => ⟨eq_of_heq hτ, eq_of_heq hτ'⟩

@[simp]
def Tm.Subst.weakenTp (γ : Subst Δ (.map (.subst δ) Γ) Γ') : Subst Δ ((Γ.map (.rename .there)).map (.subst (Tp.Var.cases τ δ))) Γ'
  | τ, x => γ (x.cast rfl (by simp))

@[simp]
theorem Tm.Subst.apply_cast {γ : Subst Δ Γ Γ'} : γ (x.cast hτ rfl) = (γ x).cast rfl hτ :=
  by cases hτ; simp

@[simp]
theorem Tm.subst_cases {γ : Subst Δ Γ Γ'} {x : Var Δ τ (.cons Γ τ')} : (subst γ' (x.cases e γ) : Tm Δ Γ'' τ) = x.cases (e.subst γ') fun x => (γ x).subst γ' :=
  by cases x <;> rfl

@[simp]
theorem Tm.substTp_subst_cases {δ : Tp.Subst Δ Δ'} : substTp (fun α => Tp.subst (.mk τ) (α.cases τ' (fun α => (δ α).rename .there))) e = (substTp (fun α => α.cases (τ'.subst (.mk τ)) δ) e).cast (by simp) (by simp) :=
  by simp [← heq_eq_eq]; congr; funext α; cases α <;> simp

@[simp]
theorem Tm.casesMap_cast
  {Γ : Ctx Δ}
  {δ : Tp.Subst Δ .nil}
  {γ : Subst .nil (Γ.map (.subst δ)) .nil}
  {x : Var .nil τ ((Γ.map (.rename .there)).map (.subst (Tp.Var.cases τ₂ δ)))}
: Var.casesMap (Γ := (Γ.map (.rename .there)).map (.subst δ.weaken)) (motive := fun τ _ => Tm _ _ τ) (fun x => substTp (.mk τ₂) (Subst.rename .there γ (x.cast rfl (by simp)))) (x.cast rfl (by simp)) = γ.weakenTp x := by
  refine x.casesMap fun x => ?_
  refine x.casesMap fun {τ} x => ?_
  simp
  have : (x.map (.subst δ)).cast (by simp : _ = (τ.rename .there).subst (Tp.Var.cases τ₂ δ)) (by simp) = (x.map (.rename .there) |>.map (.subst δ.weaken) |>.map (.subst (.mk τ₂))).cast (by simp) rfl := by
    rewrite [Var.map_map'' fun _ => rfl]
    simp
  simp [this]
  have : (x.map (.subst (fun α => (δ α).rename .there))).cast (by simp : _ = (τ.rename .there).subst δ.weaken) (by simp) = (x.map (.subst δ) |>.map (.rename .there)).cast (by simp) rfl := by
    simp
  simp [← heq_eq_eq]
  rewrite [this, Subst.rename, Var.casesMap_rename_cast]
  refine .trans (b := (γ (x.map (.subst δ))).renameTp .there |>.substTp (.mk τ₂)) ?_ ?_
  . congr
    . simp
    simp [← heq_eq_eq]
    rfl
  . simp

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
    have {τ} {e₁ e' : Tm .nil .nil τ} (h : τ = τ₁.arr τ₂) (h' : h ▸ e₁ = e.lam) (s : Steps e₁ e') : False := by
      cases s with
      | app => nomatch h
      | app_lam => nomatch h
      | inst => rename_i τ _ _ _ _ ; cases τ; rename_i α _ _ _; cases α; cases h; nomatch h'; nomatch h; cases h; nomatch h'; nomatch h
      | inst_gen => rename_i τ _ _ ; cases τ; rename_i α _; cases α; cases h; nomatch h'; nomatch h; cases h; nomatch h'; nomatch h
    this rfl rfl s
  | @gen τ e, s =>
    have {τ₁} {e₁ e' : Tm .nil .nil τ₁} (h : τ₁ = τ.all) (h' : h ▸ e₁ = e.gen) (s : Steps e₁ e') : False := by
      cases s with
      | app => nomatch h
      | app_lam => nomatch h
      | inst => rename_i τ _ _ _ _ ; cases τ; rename_i α _ _ _; cases α; cases h; nomatch h'; nomatch h; nomatch h; nomatch h
      | inst_gen => rename_i τ _ _ ; cases τ; rename_i α _; cases α; cases h; nomatch h'; nomatch h; nomatch h; nomatch h
    this rfl rfl s

theorem Tm.Steps.deterministic : (s₁ : Steps e e₁) → (s₂ : Steps e e₂) → e₁ = e₂
  | app s₁, app s₂ => s₁.deterministic s₂ ▸ rfl
  | app s₁, app_lam => nomatch Val.lam.not_steps s₁
  | app_lam, app s₂ => nomatch Val.lam.not_steps s₂
  | app_lam, app_lam => rfl
  | @inst τ e' τ' e₁' s₁, s₂ =>
    have {τ₂} (h : τ₂ = τ.subst (.mk τ')) {e e₂} (h' : h ▸ e = e'.inst τ') (s₂ : Steps e e₂) : e₁'.inst τ' = h ▸ e₂ := by
      cases s₂ with
      | app => nomatch h
      | app_lam => nomatch h
      | inst s₂ =>
        let ⟨_, _⟩ := inst_inj_cast h h'
        subst_eqs
        cases s₁.deterministic s₂
        rfl
      | inst_gen =>
        let ⟨_, _⟩ := inst_inj_cast h h'
        subst_eqs
        nomatch Val.gen.not_steps s₁
    this rfl rfl s₂
  | @inst_gen τ e' τ', s₂ =>
    have {τ₂} (h : τ₂ = τ.subst (.mk τ')) {e e₂} (h' : h ▸ e = e'.gen.inst τ') (s₂ : Steps e e₂) : e'.substTp (.mk τ') = h ▸ e₂ := by
      cases s₂ with
      | app => nomatch h
      | app_lam => nomatch h
      | inst s₂ =>
        let ⟨_, _⟩ := inst_inj_cast h h'
        subst_eqs
        nomatch Val.gen.not_steps s₂
      | inst_gen =>
        let ⟨_, _⟩ := inst_inj_cast h h'
        subst_eqs
        rfl
    this rfl rfl s₂

def Tm.progress : (e : Tm .nil .nil τ) → Val e ⊕ Σ e', Steps e e'
  | lam e => .inl .lam
  | app e e₁ => .inr <|
                have := e.progress
                match this with
                | .inl .lam => ⟨_, .app_lam⟩
                | .inr ⟨_, s⟩ => ⟨_, .app s⟩
  | gen e => .inl .gen
  | inst e τ => .inr <|
                have := e.progress
                match this with
                | .inl .gen => ⟨_, .inst_gen⟩
                | .inr ⟨_, s⟩ => ⟨_, .inst s⟩

def Tm.Steps.irrelevant' (h : Nonempty (Σ e', Steps e e')) : Σ e', Steps e e' :=
  match progress e with
  | .inl v => (h.elim fun ⟨_, s⟩ => v.not_steps s).elim
  | .inr s => s

def Tm.Steps.irrelevant (h : Nonempty (Steps e e')) : Steps e e' :=
  let ⟨_, s⟩ := irrelevant' (h.elim (⟨e', ·⟩))
  h.elim (deterministic s) ▸ s

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

theorem Tm.Reduces.deterministic (r₁ : Reduces e e₁) (r₂ : Reduces e e₂) (v₁ : Val e₁) (v₂ : Val e₂) : e₁ = e₂ := by
  induction r₁ with
  | refl =>
    cases r₂ with
    | refl => rfl
    | step s₂ r₂ => nomatch v₁.not_steps s₂
  | step s₁ _ ih =>
    cases r₂ with
    | refl => nomatch v₂.not_steps s₁
    | step s₂ r₂ =>
      cases s₁.deterministic s₂
      exact ih r₂ v₁

instance : WellFoundedRelation { x // Acc r x } where
  rel := InvImage r (·.1)
  wf  := ⟨fun ac => InvImage.accessible _ ac.2⟩

def Tm.Reduces.irrelevant'.go (h : Acc (fun e e' => Nonempty (Steps e' e)) e) : Σ e', Val e' × Reduces e e' :=
  match progress e with
  | .inl v => ⟨_, v, refl⟩
  | .inr ⟨e', s⟩ => have := ⟨s⟩; let ⟨_, v, r⟩ := go (h.inv this); ⟨_, v, step s r⟩
  termination_by Subtype.mk e h

def Tm.Reduces.irrelevant' (h : Nonempty (Σ e', Val e' × Reduces e e')) : Σ e', Val e' × Reduces e e' :=
  irrelevant'.go <| by
    revert h
    intro ⟨e', v, r⟩
    induction r with
    | refl => exact ⟨_, fun _ h => nomatch h.elim v.not_steps⟩
    | step s r ih => exact ⟨_, fun _ h => h.elim s.deterministic ▸ ih v⟩

def Tm.Reduces.irrelevant.go (h : Nonempty (Reduces e e')) (ha : Acc (fun e e'' => e'' ≠ e' ∧ Nonempty (Steps e'' e)) e) : Reduces e e' :=
  if h' : e = e' then
    h' ▸ refl
  else
    match progress e with
    | .inl v => False.elim <| match h with | ⟨refl⟩ => h' rfl | ⟨step s _⟩ => v.not_steps s
    | .inr ⟨e'', s⟩ => have := ⟨h', ⟨s⟩⟩; step s (go (e := e'') (e' := e') (by match h with | ⟨refl⟩ => exact (h' rfl).elim | ⟨step s' r⟩ => exact s.deterministic s' ▸ ⟨r⟩) (ha.inv this))
  termination_by Subtype.mk e ha

def Tm.Reduces.irrelevant (h : Nonempty (Reduces e e')) : Reduces e e' :=
  irrelevant.go h <| by
    revert h
    intro ⟨r⟩
    induction r with
    | refl => exact ⟨_, nofun⟩
    | step s r ih => exact ⟨_, fun _ ⟨_, h⟩ => h.elim s.deterministic ▸ ih⟩

def Tm.Cand (τ : Tp .nil) :=
  { C : (e : Tm .nil .nil τ) → Prop // ∀ e e', (r : Reduces e e') → (c : C e') → C e }

@[simp]
def Tm.HT Δ (δ : Tp.Subst Δ .nil) (η : ∀ α, Cand (δ α)) (τ : Tp Δ) (e : Tm .nil .nil (τ.subst δ)) : Prop :=
  match τ with
  | .var α => (η α).val e
  | .arr τ₁ τ₂ => ∃ e₂, ∃ _ : Reduces e (.lam e₂), ∀ e₁, (ht : HT Δ δ η τ₁ e₁) → HT Δ δ η τ₂ (e₂.subst (Subst.mk e₁))
  | .all τ => ∃ e', ∃ _ : Reduces e (.gen e'), ∀ τ' C, HT Δ.cons (Tp.Var.cases τ' δ) (Tp.Var.cases C η) τ (e'.substTp (.mk τ') |>.cast rfl (by simp))

def Tm.HT.arr (ht : HT Δ δ η (.arr τ₁ τ₂) e) : Σ e₂, Reduces e (.lam e₂) ×' ∀ e₁, (ht : HT Δ δ η τ₁ e₁) → HT Δ δ η τ₂ (e₂.subst (Subst.mk e₁)) :=
  let ⟨_, .lam, r⟩ := Reduces.irrelevant' (let ⟨_, r, _⟩ := ht; ⟨_, .lam, r⟩)
  ⟨_, r, let ⟨_, r', ht⟩ := ht; by cases r.deterministic r' .lam .lam; exact ht⟩

def Tm.HT.all (ht : HT Δ δ η (.all τ) e) : Σ e', Reduces e (.gen e') ×' ∀ τ' C, HT Δ.cons (Tp.Var.cases τ' δ) (Tp.Var.cases C η) τ (e'.substTp (.mk τ') |>.cast rfl (by simp)) :=
  let ⟨_, .gen, r⟩ := Reduces.irrelevant' (let ⟨_, r, _⟩ := ht; ⟨_, .gen, r⟩)
  ⟨_, r, let ⟨_, r', ht⟩ := ht; by cases r.deterministic r' .gen .gen; exact ht⟩

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
  | var => simp
  | arr τ₁ τ₂ ih₁ ih₂ =>
    specialize @ih₁ Δ' δ' η' δ₁
    specialize @ih₂ Δ' δ' η' δ₁
    constructor
    . intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_lam] at this
      exists _, this
      intro e₁ ht₁
      specialize @ih₁ (e₁.cast rfl (by simp))
      simp at ih₁
      refine Eq.mp ?_ (ih₂.mp (ht _ (ih₁.mpr ht₁)))
      congr
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl _ := cast_flip' h
      cases h
      intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_lam] at this
      exists _, this
      intro e₁ ht₁
      specialize @ih₂ (e.subst (Subst.mk (e₁.cast rfl (by simp))) |>.cast rfl (by simp))
      simp at ih₂
      refine Eq.mp ?_ (ih₂.mpr (ht _ (ih₁.mp ht₁)))
      congr
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
  | all τ ih =>
    constructor
    . intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_gen] at this
      exists _, this
      intro τ₁ C₁
      specialize @ih Δ'.cons (Tp.Var.cases τ₁ δ') (Tp.Var.cases C₁ η') δ₁.weaken (e.substTp (.mk τ₁) |>.cast rfl (by simp))
      refine Eq.mp ?_ (ih.mp (Eq.mp ?_ (ht τ₁ C₁)))
      . simp
      . congr <;> simp
        apply funext'
        intro α
        cases α <;> rfl
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl _ := cast_flip' h
      cases h
      intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_gen] at this
      exists _, this
      intro τ₁ C₁
      specialize @ih Δ'.cons (Tp.Var.cases τ₁ δ') (Tp.Var.cases C₁ η') δ₁.weaken (e.substTp (.mk τ₁) |>.cast rfl (by simp))
      simp at ih
      refine Eq.mp ?_ (ih.mpr (ht τ₁ C₁))
      congr 1 <;> simp
      apply funext'
      intro α
      cases α <;> rfl

theorem Tm.HT.subst {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Subst Δ' Δ} (hδ : ∀ α, (δ₂ α).subst (fun α => δ' (δ₁ α)) = δ' α) (h : ∀ α e, HT Δ (fun α => δ' (δ₁ α)) (fun α => η' (δ₁ α)) (δ₂ α) (e.cast rfl (by simp [hδ])) ↔ (η' α).val e) {e} : HT Δ (fun α => δ' (δ₁ α)) (fun α => η' (δ₁ α)) (τ.subst δ₂) e ↔ HT Δ' δ' η' τ (e.cast rfl (by simp [hδ])) := by
  induction τ generalizing Δ with
  | var α =>
    specialize h α (e.cast rfl (by simp [hδ]))
    simp at h ⊢
    exact h
  | arr τ₁ τ₂ ih₁ ih₂ =>
    specialize @ih₁ Δ δ' η' δ₁ δ₂ hδ h
    specialize @ih₂ Δ δ' η' δ₁ δ₂ hδ h
    constructor
    . intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_lam] at this
      exists _, this
      intro e₁ ht₁
      specialize @ih₁ (e₁.cast rfl (by simp [hδ]))
      simp at ih₁
      refine Eq.mp ?_ (ih₂.mp (ht _ (ih₁.mpr ht₁)))
      congr
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl _ := cast_flip' h
      cases h
      intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_lam] at this
      exists _, this
      intro e₁ ht₁
      specialize @ih₂ (e.subst (Subst.mk (e₁.cast rfl (by simp [hδ]))) |>.cast rfl (by simp [hδ]))
      simp at ih₂
      refine Eq.mp ?_ (ih₂.mpr (ht _ (ih₁.mp ht₁)))
      congr
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
  | all τ ih =>
    constructor
    . intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_gen] at this
      exists _, this
      intro τ' C
      specialize @ih Δ.cons (Tp.Var.cases τ' δ') (Tp.Var.cases C η') δ₁.weaken δ₂.weaken (Tp.Var.cases rfl (by simp [hδ])) (Tp.Var.cases (by simp) fun α e => .trans (.symm (.trans (@rename Δ Δ.cons (Tp.Var.cases τ' fun α => δ' (δ₁ α)) (Tp.Var.cases C fun α => η' (δ₁ α)) (δ₂ α) .there (e.cast rfl _)) ?_)) (h α e)) (e.substTp (.mk τ') |>.cast rfl (by simp))
      . simp [← eq_iff_iff]
        congr 1
        . simp
        . apply funext'
          intro α
          cases α <;> rfl
        . simp
      refine Eq.mp ?_ (ih.mp (Eq.mp ?_ (ht τ' C)))
      . simp
      . congr <;> simp
        apply funext'
        intro α
        cases α <;> rfl
    . generalize h : e.cast _ _ = e'
      replace h : e = e'.cast rfl _ := cast_flip' h
      cases h
      intro ⟨e, r, ht⟩
      have' := r.cast
      rw [cast_gen] at this
      exists _, this
      intro τ' C
      specialize @ih Δ.cons (Tp.Var.cases τ' δ') (Tp.Var.cases C η') δ₁.weaken δ₂.weaken (Tp.Var.cases rfl (by simp [hδ])) (Tp.Var.cases (by simp) fun α e => .trans (.symm (.trans (@rename Δ Δ.cons (Tp.Var.cases τ' fun α => δ' (δ₁ α)) (Tp.Var.cases C fun α => η' (δ₁ α)) (δ₂ α) .there (e.cast rfl _)) ?_)) (h α e)) (e.substTp (.mk τ') |>.cast rfl (by simp [hδ]))
      . simp [← eq_iff_iff]
        congr 1
        . simp
        . apply funext'
          intro α
          cases α <;> rfl
        . simp
      simp at ih
      refine Eq.mp ?_ (ih.mpr (ht τ' C))
      congr 1 <;> simp
      apply funext'
      intro α
      cases α <;> rfl

def Tm.HTSubst Δ (δ : Tp.Subst Δ .nil) (η : ∀ α, Cand (δ α)) (Γ : Ctx Δ) (γ : Subst .nil (Γ.map (.subst δ)) .nil) : Prop :=
  ∀ {τ} x, HT Δ δ η τ (γ (.map (.subst δ) x))

def Tm.HT' Δ Γ τ (e : Tm Δ Γ τ) : Prop :=
  ∀ δ η γ, (ht_γ : HTSubst Δ δ η Γ @γ) → HT Δ δ η τ (e.substTp δ |>.subst @γ)

theorem Tm.ftlr : ∀ e, HT' Δ Γ τ e
  | var x, δ, η, γ, ht_γ => by simp; exact ht_γ x
  | lam e, δ, η, γ, ht_γ => ⟨_, .refl, fun e₁ ht => by simp; exact ftlr e δ η (Var.cases e₁ γ) (Var.cases ht ht_γ)⟩
  | app e e₁, δ, η, γ, ht_γ => let ⟨_, r, ht⟩ := ftlr e δ η γ ht_γ; .expand _ _ (r.app.trans (.step .app_lam .refl)) (ht (e₁.substTp δ |>.subst γ) (ftlr e₁ δ η γ ht_γ))
  | gen e, δ, η, γ, ht_γ => ⟨_, .refl, fun τ' C => by simp; exact ftlr e (Tp.Var.cases τ' δ) (Tp.Var.cases C η) γ.weakenTp (Var.casesMap fun x => by simp; exact HT.rename.mp (ht_γ x))⟩
  | inst e τ, δ, η, γ, ht_γ => let ⟨e', r, ht⟩ := ftlr e δ η γ ht_γ; .expand _ (e'.substTp (.mk (τ.subst δ)) |>.cast rfl (by simp)) (by simp; exact .cast (r.inst.trans (.step .inst_gen .refl))) <| have := @HT.subst Δ Δ.cons (Tp.Var.cases (τ.subst δ) δ) (Tp.Var.cases ⟨HT Δ δ η τ, HT.expand⟩ η) ‹_› .there (.mk τ) (Tp.Var.cases rfl fun _ => rfl) (Tp.Var.cases (by simp) (by simp)) (e'.substTp (.mk (τ.subst δ)) |>.cast rfl (by simp)); by simp at this; exact this.mpr (ht (τ.subst δ) ⟨HT Δ δ η τ, HT.expand⟩)

def Tm.termination (e : Tm .nil .nil τ) : Σ e', Val e' × Reduces e e' :=
  Tm.Reduces.irrelevant' <|
  match τ, e, ftlr e .var nofun nofun nofun with
  | .arr τ₁ τ₂, e, ⟨e', r, _⟩ => ⟨.lam (e'.cast (by simp) (by simp)), .lam, by simp at r; have := r.cast (hΓ := rfl) (hτ := show (τ₁.arr τ₂).subst .var = τ₁.arr τ₂ by simp); simp at this; exact this⟩
  | .all τ, _, ⟨e, r, _⟩ => ⟨.gen (e.cast rfl (by simp)), .gen, by simp at r; have := r.cast (hΓ := rfl) (hτ := show τ.all.subst .var = τ.all by simp); simp at this; exact this⟩

def Tm.PCand (τ τ' : Tp .nil) :=
  { R : (e : Tm .nil .nil τ) → (e' : Tm .nil .nil τ') → Prop // ∀ e₁ e₁' e₂ e₂', (r : Reduces e₁ e₂) → (r' : Reduces e₁' e₂') → (r : R e₂ e₂') → R e₁ e₁' }

@[simp]
def Tm.Sim Δ (δ δ' : Tp.Subst Δ .nil) (η : ∀ α, PCand (δ α) (δ' α)) (τ : Tp Δ) (e : Tm .nil .nil (τ.subst δ)) (e' : Tm .nil .nil (τ.subst δ')) : Prop :=
  match τ with
  | .var α => (η α).val e e'
  | .arr τ₁ τ₂ => ∃ e₂ e₂', ∃ _ : Reduces e (.lam e₂), ∃ _ : Reduces e' (.lam e₂'), ∀ e₁ e₁', (sim : Sim Δ δ δ' η τ₁ e₁ e₁') → Sim Δ δ δ' η τ₂ (e₂.subst (Subst.mk e₁)) (e₂'.subst (Subst.mk e₁'))
  | .all τ => ∃ e₁ e₁', ∃ _ : Reduces e (.gen e₁), ∃ _ : Reduces e' (.gen e₁'), ∀ τ₂ τ₂' R, Sim Δ.cons (Tp.Var.cases τ₂ δ) (Tp.Var.cases τ₂' δ') (Tp.Var.cases R η) τ (e₁.substTp (.mk τ₂) |>.cast rfl (by simp)) (e₁'.substTp (.mk τ₂') |>.cast rfl (by simp))

def Tm.Sim.arr (sim : Sim Δ δ δ' η (.arr τ₁ τ₂) e e') : Σ e₂ e₂', Reduces e (.lam e₂) × Reduces e' (.lam e₂') ×' ∀ e₁ e₁', (sim : Sim Δ δ δ' η τ₁ e₁ e₁') → Sim Δ δ δ' η τ₂ (e₂.subst (Subst.mk e₁)) (e₂'.subst (Subst.mk e₁')) :=
  let ⟨_, .lam, r⟩ := Reduces.irrelevant' (let ⟨_, _, r, _, _⟩ := sim; ⟨_, .lam, r⟩)
  let ⟨_, .lam, r'⟩ := Reduces.irrelevant' (let ⟨_, _, _, r', _⟩ := sim; ⟨_, .lam, r'⟩)
  ⟨_, _, r, r', let ⟨_, _, r'', r''', sim⟩ := sim; by cases r.deterministic r'' .lam .lam; cases r'.deterministic r''' .lam .lam; exact sim⟩

def Tm.Sim.all (sim : Sim Δ δ δ' η (.all τ) e e') : Σ e₁ e₁', Reduces e (.gen e₁) × Reduces e' (.gen e₁') ×' ∀ τ₂ τ₂' R, Sim Δ.cons (Tp.Var.cases τ₂ δ) (Tp.Var.cases τ₂' δ') (Tp.Var.cases R η) τ (e₁.substTp (.mk τ₂) |>.cast rfl (by simp)) (e₁'.substTp (.mk τ₂') |>.cast rfl (by simp)) :=
  let ⟨_, .gen, r⟩ := Reduces.irrelevant' (let ⟨_, _, r, _, _⟩ := sim; ⟨_, .gen, r⟩)
  let ⟨_, .gen, r'⟩ := Reduces.irrelevant' (let ⟨_, _, _, r', _⟩ := sim; ⟨_, .gen, r'⟩)
  ⟨_, _, r, r', let ⟨_, _, r'', r''', sim⟩ := sim; by cases r.deterministic r'' .gen .gen; cases r'.deterministic r''' .gen .gen; exact sim⟩

theorem Tm.Sim.expand : ∀ {τ} e₁ e₁' e₂ e₂', (r : Reduces e₁ e₂) → (r' : Reduces e₁' e₂') → (sim : Sim Δ δ δ' η τ e₂ e₂') → Sim Δ δ δ' η τ e₁ e₁'
  | .var α, e₁, e₁', e₂, e₂', r, r', sim => (η α).property e₁ e₁' e₂ e₂' r r' sim
  | .arr _τ₁ _τ₂, _, _, _, _, r, r', ⟨_, _, r₂, r₂', sim⟩ => ⟨_, _, r.trans r₂, r'.trans r₂', sim⟩
  | .all _τ, _, _, _, _, r, r', ⟨_, _, r₂, r₂', sim⟩ => ⟨_, _, r.trans r₂, r'.trans r₂', sim⟩

theorem Tm.Sim.rename {δ₁ : Tp.Rename Δ Δ'} {e e'} : Sim Δ (fun α => δ (δ₁ α)) (fun α => δ' (δ₁ α)) (fun α => η (δ₁ α)) τ e e' ↔ Sim Δ' δ δ' η (τ.rename δ₁) (e.cast rfl (by simp)) (e'.cast rfl (by simp)) := by
  induction τ generalizing Δ' with
  | var => simp
  | arr τ₁ τ₂ ih₁ ih₂ =>
    specialize @ih₁ Δ' δ δ' η δ₁
    specialize @ih₂ Δ' δ δ' η δ₁
    constructor
    . intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_lam] at r r'
      exists _, _, r, r'
      intro e₁ e₁' sim₁
      specialize @ih₁ (e₁.cast rfl (by simp)) (e₁'.cast rfl (by simp))
      simp at ih₁
      refine Eq.mp ?_ (ih₂.mp (sim _ _ (ih₁.mpr sim₁)))
      congr
      all_goals
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
    . generalize h : e.cast _ _ = e₁
      generalize h' : e'.cast _ _ = e₁'
      replace h : e = e₁.cast rfl _ := cast_flip' h
      replace h' : e' = e₁'.cast rfl _ := cast_flip' h'
      cases h
      cases h'
      intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_lam] at r r'
      exists _, _, r, r'
      intro e₁ e₁' sim₁
      specialize @ih₂ (e.subst (Subst.mk (e₁.cast rfl (by simp))) |>.cast rfl (by simp)) (e'.subst (Subst.mk (e₁'.cast rfl (by simp))) |>.cast rfl (by simp))
      simp at ih₂
      refine Eq.mp ?_ (ih₂.mpr (sim _ _ (ih₁.mp sim₁)))
      congr
      all_goals
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
  | all τ ih =>
    constructor
    . intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_gen] at r r'
      exists _, _, r, r'
      intro τ₂ τ₂' R
      specialize @ih Δ'.cons (Tp.Var.cases τ₂ δ) (Tp.Var.cases τ₂' δ') (Tp.Var.cases R η) δ₁.weaken (e.substTp (.mk τ₂) |>.cast rfl (by simp)) (e'.substTp (.mk τ₂') |>.cast rfl (by simp))
      refine Eq.mp ?_ (ih.mp (Eq.mp ?_ (sim τ₂ τ₂' R)))
      . simp
      . congr <;> simp
        apply funext'
        intro α
        cases α <;> rfl
    . generalize h : e.cast _ _ = e₁
      generalize h' : e'.cast _ _ = e₁'
      replace h : e = e₁.cast rfl _ := cast_flip' h
      replace h' : e' = e₁'.cast rfl _ := cast_flip' h'
      cases h
      cases h'
      intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_gen] at r r'
      exists _, _, r, r'
      intro τ₂ τ₂' R
      specialize @ih Δ'.cons (Tp.Var.cases τ₂ δ) (Tp.Var.cases τ₂' δ') (Tp.Var.cases R η) δ₁.weaken (e.substTp (.mk τ₂) |>.cast rfl (by simp)) (e'.substTp (.mk τ₂') |>.cast rfl (by simp))
      simp at ih
      refine Eq.mp ?_ (ih.mpr (sim τ₂ τ₂' R))
      congr 1 <;> simp
      apply funext'
      intro α
      cases α <;> rfl

theorem Tm.Sim.subst {δ₁ : Tp.Rename Δ Δ'} {δ₂ : Tp.Subst Δ' Δ} (hδ : ∀ α, (δ₂ α).subst (fun α => δ (δ₁ α)) = δ α) (hδ' : ∀ α, (δ₂ α).subst (fun α => δ' (δ₁ α)) = δ' α) (h : ∀ α e e', Sim Δ (fun α => δ (δ₁ α)) (fun α => δ' (δ₁ α)) (fun α => η (δ₁ α)) (δ₂ α) (e.cast rfl (by simp [hδ])) (e'.cast rfl (by simp [hδ'])) ↔ (η α).val e e') {e e'} : Sim Δ (fun α => δ (δ₁ α)) (fun α => δ' (δ₁ α)) (fun α => η (δ₁ α)) (τ.subst δ₂) e e' ↔ Sim Δ' δ δ' η τ (e.cast rfl (by simp [hδ])) (e'.cast rfl (by simp [hδ'])) := by
  induction τ generalizing Δ with
  | var α =>
    specialize h α (e.cast rfl (by simp [hδ])) (e'.cast rfl (by simp [hδ']))
    simp at h ⊢
    exact h
  | arr τ₁ τ₂ ih₁ ih₂ =>
    specialize @ih₁ Δ δ δ' η δ₁ δ₂ hδ hδ' h
    specialize @ih₂ Δ δ δ' η δ₁ δ₂ hδ hδ' h
    constructor
    . intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_lam] at r r'
      exists _, _, r, r'
      intro e₁ e₁' sim₁
      specialize @ih₁ (e₁.cast rfl (by simp [hδ])) (e₁'.cast rfl (by simp [hδ']))
      simp at ih₁
      refine Eq.mp ?_ (ih₂.mp (sim _ _ (ih₁.mpr sim₁)))
      congr
      all_goals
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
    . generalize h : e.cast _ _ = e₁
      generalize h' : e'.cast _ _ = e₁'
      replace h : e = e₁.cast rfl _ := cast_flip' h
      replace h' : e' = e₁'.cast rfl _ := cast_flip' h'
      cases h
      cases h'
      intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_lam] at r r'
      exists _, _, r, r'
      intro e₁ e₁' sim₁
      specialize @ih₂ (e.subst (Subst.mk (e₁.cast rfl (by simp [hδ]))) |>.cast rfl (by simp [hδ])) (e'.subst (Subst.mk (e₁'.cast rfl (by simp [hδ']))) |>.cast rfl (by simp [hδ']))
      simp at ih₂
      refine Eq.mp ?_ (ih₂.mpr (sim _ _ (ih₁.mp sim₁)))
      congr
      all_goals
      simp
      congr
      funext τ x
      cases x
      case there x => nomatch x
      simp [← heq_eq_eq]
      exact .symm <| Var.cases_cast ..
  | all τ ih =>
    constructor
    . intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_gen] at r r'
      exists _, _, r, r'
      intro τ₂ τ₂' R
      specialize @ih Δ.cons (Tp.Var.cases τ₂ δ) (Tp.Var.cases τ₂' δ') (Tp.Var.cases R η) δ₁.weaken δ₂.weaken (Tp.Var.cases rfl (by simp [hδ])) (Tp.Var.cases rfl (by simp [hδ'])) (Tp.Var.cases (by simp) fun α e e' => .trans (.symm (.trans (@rename Δ Δ.cons (Tp.Var.cases τ₂ fun α => δ (δ₁ α)) (Tp.Var.cases τ₂' fun α => δ' (δ₁ α)) (Tp.Var.cases R fun α => η (δ₁ α)) (δ₂ α) .there (e.cast rfl _) (e'.cast rfl _)) ?_)) (h α e e')) (e.substTp (.mk τ₂) |>.cast rfl (by simp)) (e'.substTp (.mk τ₂') |>.cast rfl (by simp))
      . simp [← eq_iff_iff]
        congr 1
        . simp
        . simp
        . apply funext'
          intro α
          cases α <;> rfl
        . simp
        . simp
      refine Eq.mp ?_ (ih.mp (Eq.mp ?_ (sim τ₂ τ₂' R)))
      . simp
      . congr <;> simp
        apply funext'
        intro α
        cases α <;> rfl
    . generalize h : e.cast _ _ = e₁
      generalize h' : e'.cast _ _ = e₁'
      replace h : e = e₁.cast rfl _ := cast_flip' h
      replace h' : e' = e₁'.cast rfl _ := cast_flip' h'
      cases h
      cases h'
      intro ⟨e, e', r, r', sim⟩
      have' r := r.cast
      have' r' := r'.cast
      rw [cast_gen] at r r'
      exists _, _, r, r'
      intro τ₂ τ₂' R
      specialize @ih Δ.cons (Tp.Var.cases τ₂ δ) (Tp.Var.cases τ₂' δ') (Tp.Var.cases R η) δ₁.weaken δ₂.weaken (Tp.Var.cases rfl (by simp [hδ])) (Tp.Var.cases rfl (by simp [hδ'])) (Tp.Var.cases (by simp) fun α e e' => .trans (.symm (.trans (@rename Δ Δ.cons (Tp.Var.cases τ₂ fun α => δ (δ₁ α)) (Tp.Var.cases τ₂' fun α => δ' (δ₁ α)) (Tp.Var.cases R fun α => η (δ₁ α)) (δ₂ α) .there (e.cast rfl _) (e'.cast rfl _)) ?_)) (h α e e')) (e.substTp (.mk τ₂) |>.cast rfl (by simp [hδ])) (e'.substTp (.mk τ₂') |>.cast rfl (by simp [hδ']))
      . simp [← eq_iff_iff]
        congr 1
        . simp
        . simp
        . apply funext'
          intro α
          cases α <;> rfl
        . simp
        . simp
      simp at ih
      refine Eq.mp ?_ (ih.mpr (sim τ₂ τ₂' R))
      congr 1 <;> simp
      apply funext'
      intro α
      cases α <;> rfl

def Tm.SimSubst Δ (δ δ' : Tp.Subst Δ .nil) (η : ∀ α, PCand (δ α) (δ' α)) (Γ : Ctx Δ) (γ : Subst .nil (Γ.map (.subst δ)) .nil) (γ' : Subst .nil (Γ.map (.subst δ')) .nil) : Prop :=
  ∀ {τ} x, Sim Δ δ δ' η τ (γ (.map (.subst δ) x)) (γ' (.map (.subst δ') x))

def Tm.ExactEq Δ Γ τ (e e' : Tm Δ Γ τ) : Prop :=
  ∀ δ δ' η γ γ', (sim_γ : SimSubst Δ δ δ' η Γ @γ @γ') → Sim Δ δ δ' η τ (e.substTp δ |>.subst @γ) (e'.substTp δ' |>.subst @γ')

theorem Tm.parametricity : ∀ e, ExactEq Δ Γ τ e e
  | var x, δ, δ', η, γ, γ', sim_γ => by simp; exact sim_γ x
  | lam e, δ, δ', η, γ, γ', sim_γ => ⟨_, _, .refl, .refl, fun e₁ e₁' sim => by simp; exact parametricity e δ δ' η (Var.cases e₁ γ) (Var.cases e₁' γ') (Var.cases sim sim_γ)⟩
  | app e e₁, δ, δ', η, γ, γ', sim_γ => let ⟨_, _, r, r', sim⟩ := parametricity e δ δ' η γ γ' sim_γ; .expand _ _ _ _ (r.app.trans (.step .app_lam .refl)) (r'.app.trans (.step .app_lam .refl)) (sim (e₁.substTp δ |>.subst γ) (e₁.substTp δ' |>.subst γ') (parametricity e₁ δ δ' η γ γ' sim_γ))
  | gen e, δ, δ', η, γ, γ', sim_γ => ⟨_, _, .refl, .refl, fun τ₂ τ₂' R => by simp; exact parametricity e (Tp.Var.cases τ₂ δ) (Tp.Var.cases τ₂' δ') (Tp.Var.cases R η) γ.weakenTp γ'.weakenTp (Var.casesMap fun x => by simp; exact Sim.rename.mp (sim_γ x))⟩
  | inst e τ, δ, δ', η, γ, γ', sim_γ => let ⟨e₁, e₁', r, r', sim⟩ := parametricity e δ δ' η γ γ' sim_γ; .expand _ _ (e₁.substTp (.mk (τ.subst δ)) |>.cast rfl (by simp)) (e₁'.substTp (.mk (τ.subst δ')) |>.cast rfl (by simp)) (by simp; exact .cast (r.inst.trans (.step .inst_gen .refl))) (by simp; exact .cast (r'.inst.trans (.step .inst_gen .refl))) <| have := @Sim.subst Δ Δ.cons (Tp.Var.cases (τ.subst δ) δ) (Tp.Var.cases (τ.subst δ') δ') (Tp.Var.cases ⟨Sim Δ δ δ' η τ, Sim.expand⟩ η) ‹_› .there (.mk τ) (Tp.Var.cases rfl fun _ => rfl) (Tp.Var.cases rfl fun _ => rfl) (Tp.Var.cases (by simp) (by simp)) (e₁.substTp (.mk (τ.subst δ)) |>.cast rfl (by simp)) (e₁'.substTp (.mk (τ.subst δ')) |>.cast rfl (by simp)); by simp at this; exact this.mpr (sim (τ.subst δ) (τ.subst δ') ⟨Sim Δ δ δ' η τ, Sim.expand⟩)

def two (e : Tm .nil .nil (.all (.arr (.var .here) (.arr (.var .here) (.var .here))))) : (∀ τ e₁ e₂, (((e.inst τ).app e₁).app e₂).Reduces e₁) ⊕ (∀ τ e₁ e₂, (((e.inst τ).app e₁).app e₂).Reduces e₂) :=
  let ⟨e₁, r₁, this⟩ := (e.ftlr .var nofun .var nofun).all
  let ⟨e₂, r₂, this⟩ := (this (.all (.arr (.var .here) (.arr (.var .here) (.var .here)))) ⟨fun e => Nonempty (e.Reduces (.gen (.lam (.lam (.var (.there .here))))) ⊕ e.Reduces (.gen (.lam (.lam (.var .here))))), fun _ _ r ⟨s⟩ => ⟨s.map r.trans r.trans⟩⟩).arr
  let ⟨e₃, r₃, this⟩ := (this _ ⟨.inl .refl⟩).arr
  have := this _ ⟨.inr .refl⟩
  let ⟨e', v, r⟩ := Tm.Reduces.irrelevant' (match this with | ⟨.inl r⟩ => ⟨_, .gen, r⟩ | ⟨.inr r⟩ => ⟨_, .gen, r⟩)
  if h₁ : e' = .gen (.lam (.lam (.var (.there .here)))) then
    .inl fun τ e₁' e₂' =>
    let ⟨_, _, r₁'', r₁', this⟩ := (e.parametricity .var .var nofun .var .var nofun).all
    let ⟨_, _, r₂'', r₂', this⟩ := (this (.all (.arr (.var .here) (.arr (.var .here) (.var .here)))) τ ⟨fun e e' => Nonempty (e.Reduces (.gen (.lam (.lam (.var .here)))) ⊕ e'.Reduces e₁'), fun _ _ _ _ r r' ⟨s⟩ => ⟨s.map r.trans r'.trans⟩⟩).arr
    let ⟨_, e, r₃'', r₃', this⟩ := (this (.gen (.lam (.lam (.var (.there .here))))) e₁' ⟨.inr .refl⟩).arr
    have r' := Tm.Reduces.irrelevant <|
      match this _ e₂' ⟨.inl .refl⟩ with
      | ⟨.inl r'⟩ => by
        cases h₁
        cases r₁.deterministic r₁'' .gen .gen
        cases r₂.deterministic r₂'' .lam .lam
        cases r₃.deterministic r₃'' .lam .lam
        cases r.deterministic r' .gen .gen
      | ⟨.inr r'⟩ => ⟨r'⟩
    by simp at r₁' r₂'; exact r₁'.inst.trans (.step .inst_gen r₂') |>.app.trans (.step .app_lam r₃') |>.app.trans (.step .app_lam r')
  else if h₂ : e' = .gen (.lam (.lam (.var .here))) then
    .inr fun τ e₁' e₂' =>
    let ⟨_, _, r₁'', r₁', this⟩ := (e.parametricity .var .var nofun .var .var nofun).all
    let ⟨_, _, r₂'', r₂', this⟩ := (this (.all (.arr (.var .here) (.arr (.var .here) (.var .here)))) τ ⟨fun e e' => Nonempty (e.Reduces (.gen (.lam (.lam (.var (.there .here))))) ⊕ e'.Reduces e₂'), fun _ _ _ _ r r' ⟨s⟩ => ⟨s.map r.trans r'.trans⟩⟩).arr
    let ⟨_, _, r₃'', r₃', this⟩ := (this _ e₁' ⟨.inl .refl⟩).arr
    have r' := Tm.Reduces.irrelevant <|
      match this (.gen (.lam (.lam (.var .here)))) e₂' ⟨.inr .refl⟩ with
      | ⟨.inl r'⟩ => by
        cases h₂
        cases r₁.deterministic r₁'' .gen .gen
        cases r₂.deterministic r₂'' .lam .lam
        cases r₃.deterministic r₃'' .lam .lam
        cases r.deterministic r' .gen .gen
      | ⟨.inr r'⟩ => ⟨r'⟩
    by simp at r₁' r₂'; exact r₁'.inst.trans (.step .inst_gen r₂') |>.app.trans (.step .app_lam r₃') |>.app.trans (.step .app_lam r')
  else
    False.elim <| this.elim (Sum.elim (fun r' => h₁ (r.deterministic r' v .gen)) (fun r' => h₂ (r.deterministic r' v .gen)))
