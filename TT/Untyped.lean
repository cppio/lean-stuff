inductive Ctx
  | nil
  | cons (Γ : Ctx)

inductive Var : (Γ : Ctx) → Type
  | here : Var (.cons Γ)
  | there (x : Var Γ) : Var Γ.cons

@[elab_as_elim]
def Var.cases {motive : (x : Var (.cons Γ)) → Sort u} (here : motive .here) (there : ∀ x, motive (.there x)) : ∀ x, motive x
  | .here => here
  | .there x => there x

inductive Term : (Γ : Ctx) → Type
  | var (x : Var Γ) : Term Γ
  | abs (e : Term Γ.cons) : Term Γ
  | app (e₁ e₂ : Term Γ) : Term Γ

def Term.rename (γ : (x : Var Γ) → Var Γ') : (e : Term Γ) → Term Γ'
  | var x => var (γ x)
  | abs e => abs (e.rename <| Var.cases .here fun x => .there (γ x))
  | app e₁ e₂ => app (e₁.rename γ) (e₂.rename γ)

def Term.subst (γ : (x : Var Γ) → Term Γ') : (e : Term Γ) → Term Γ'
  | var x => γ x
  | abs e => abs (e.subst <| Var.cases (.var .here) fun x => (γ x).rename .there)
  | app e₁ e₂ => app (e₁.subst γ) (e₂.subst γ)

theorem Term.rename_cong (h : ∀ x, γ x = γ' x) : ∀ e, rename γ e = rename γ' e
  | var x => congrArg var (h x)
  | abs e => congrArg abs (e.rename_cong <| Var.cases rfl fun x => congrArg Var.there (h x))
  | app e₁ e₂ => (congr (congrArg app (e₁.rename_cong h)) (e₂.rename_cong h) :)

theorem Term.subst_cong (h : ∀ x, γ x = γ' x) : ∀ e, subst γ e = subst γ' e
  | var x => h x
  | abs e => congrArg abs (e.subst_cong <| Var.cases rfl fun x => congrArg (rename .there) (h x))
  | app e₁ e₂ => (congr (congrArg app (e₁.subst_cong h)) (e₂.subst_cong h) :)

theorem Term.rename_id : (e : Term Γ) → e.rename id = e
  | var _ => rfl
  | abs e => congrArg abs ((e.rename_cong <| Var.cases rfl fun _ => rfl).trans e.rename_id)
  | app e₁ e₂ => (congr (congrArg app e₁.rename_id) e₂.rename_id :)

theorem Term.subst_var : (e : Term Γ) → e.subst var = e
  | var _ => rfl
  | abs e => congrArg abs ((e.subst_cong <| Var.cases rfl fun _ => rfl).trans e.subst_var)
  | app e₁ e₂ => (congr (congrArg app e₁.subst_var) e₂.subst_var :)

theorem Term.rename_rename : ∀ e, rename γ₂ (rename γ₁ e) = rename (fun x => γ₂ (γ₁ x)) e
  | var _ => rfl
  | abs e => congrArg abs (e.rename_rename.trans <| e.rename_cong <| Var.cases rfl fun _ => rfl)
  | app e₁ e₂ => congr (congrArg app e₁.rename_rename) e₂.rename_rename

theorem Term.subst_rename : ∀ e, subst γ₂ (rename γ₁ e) = subst (fun x => γ₂ (γ₁ x)) e
  | var _ => rfl
  | abs e => congrArg abs (e.subst_rename.trans <| e.subst_cong <| Var.cases rfl fun _ => rfl)
  | app e₁ e₂ => congr (congrArg app e₁.subst_rename) e₂.subst_rename

theorem Term.rename_subst : ∀ e, rename γ₂ (subst γ₁ e) = subst (fun x => (γ₁ x).rename γ₂) e
  | var _ => rfl
  | abs e => congrArg abs (e.rename_subst.trans <| e.subst_cong <| Var.cases rfl fun x => (γ₁ x).rename_rename.trans <| .symm (γ₁ x).rename_rename)
  | app e₁ e₂ => congr (congrArg app e₁.rename_subst) e₂.rename_subst

theorem Term.subst_subst : ∀ e, subst γ₂ (subst γ₁ e) = subst (fun x => (γ₁ x).subst γ₂) e
  | var _ => rfl
  | abs e => congrArg abs (e.subst_subst.trans <| e.subst_cong <| Var.cases rfl fun x => (γ₁ x).subst_rename.trans (γ₁ x).rename_subst.symm)
  | app e₁ e₂ => congr (congrArg app e₁.subst_subst) e₂.subst_subst

def Term.sub (e' : Term Γ) : (e : Term Γ.cons) → Term Γ :=
  Term.subst (Var.cases e' .var)

inductive BetaRed : (e e' : Term Γ) → Type
  | abs (r : BetaRed e e') : BetaRed (.abs e) (.abs e')
  | app₁ (r : BetaRed e₁ e₁') : BetaRed (.app e₁ e₂) (.app e₁' e₂)
  | app₂ (r : BetaRed e₂ e₂') : BetaRed (.app e₁ e₂) (.app e₁ e₂')
  | app_abs : BetaRed (.app (.abs e₁) e₂) (e₂.sub e₁)

inductive ParBetaRed : (e e' : Term Γ) → Type
  | var : ParBetaRed (.var x) (.var x)
  | abs (r : ParBetaRed e e') : ParBetaRed (.abs e) (.abs e')
  | app (r₁ : ParBetaRed e₁ e₁') (r₂ : ParBetaRed e₂ e₂') : ParBetaRed (.app e₁ e₂) (.app e₁' e₂')
  | app_abs (r₁ : ParBetaRed e₁ e₁') (r₂ : ParBetaRed e₂ e₂') : ParBetaRed (.app (.abs e₁) e₂) (e₂'.sub e₁')

def ParBetaRed.rename : (r : ParBetaRed e e') → ParBetaRed (e.rename γ) (e'.rename γ)
  | var => var
  | abs r => abs r.rename
  | app r₁ r₂ => app r₁.rename r₂.rename
  | app_abs (e₁' := e₁') r₁ r₂ => Eq.ndrec (app_abs r₁.rename r₂.rename) <| e₁'.subst_rename.trans <| .trans (e₁'.subst_cong <| Var.cases (by exact rfl) fun x => by exact rfl) e₁'.rename_subst.symm

def ParBetaRed.subst (rγ : ∀ x, ParBetaRed (γ x) (γ' x)) : (r : ParBetaRed e e') → ParBetaRed (e.subst γ) (e'.subst γ')
  | var => rγ _
  | abs r => abs (r.subst <| Var.cases var fun x => (rγ x).rename)
  | app r₁ r₂ => app (r₁.subst rγ) (r₂.subst rγ)
  | app_abs (e₁ := e₁) (e₂ := e₂) (e₁' := e₁') (e₂' := e₂') r₁ r₂ => Eq.ndrec (app_abs (r₁.subst (γ := Var.cases (.var .here) fun x => (γ x).rename .there) (γ' := Var.cases (.var .here) fun x => (γ' x).rename .there) <| Var.cases var fun x => (rγ x).rename) (r₂.subst (γ := γ) (γ' := γ') rγ)) <| e₁'.subst_subst.trans <| .trans (e₁'.subst_cong <| Var.cases (by exact rfl) fun x => by exact (γ' x).subst_rename.trans (γ' x).subst_var) (.symm e₁'.subst_subst)

def ParBetaRed.sub (r₁ : ParBetaRed e₁ e₁') (r₂ : ParBetaRed e₂ e₂') : ParBetaRed (e₁.sub e₂) (e₁'.sub e₂') :=
  r₂.subst <| Var.cases r₁ fun _ => var

def ParBetaRed.diamond : (r₁ : ParBetaRed e e₁) → (r₂ : ParBetaRed e e₂) → Σ e', ParBetaRed e₁ e' × ParBetaRed e₂ e'
  | var, var => ⟨_, var, var⟩
  | abs r₁, abs r₂ => let ⟨_, r₁', r₂'⟩ := diamond r₁ r₂; ⟨_, abs r₁', abs r₂'⟩
  | app r₁₁ r₁₂, app r₂₁ r₂₂ => let ⟨_, r₁₁', r₂₁'⟩ := diamond r₁₁ r₂₁; let ⟨_, r₁₂', r₂₂'⟩ := diamond r₁₂ r₂₂; ⟨_, app r₁₁' r₁₂', app r₂₁' r₂₂'⟩
  | app (abs r₁₁) r₁₂, app_abs r₂₁ r₂₂ => let ⟨_, r₁₁', r₂₁'⟩ := diamond r₁₁ r₂₁; let ⟨_, r₁₂', r₂₂'⟩ := diamond r₁₂ r₂₂; ⟨_, app_abs r₁₁' r₁₂', sub r₂₂' r₂₁'⟩
  | app_abs r₁₁ r₁₂, app (abs r₂₁) r₂₂ => let ⟨_, r₁₁', r₂₁'⟩ := diamond r₁₁ r₂₁; let ⟨_, r₁₂', r₂₂'⟩ := diamond r₁₂ r₂₂; ⟨_, sub r₁₂' r₁₁', app_abs r₂₁' r₂₂'⟩
  | app_abs r₁₁ r₁₂, app_abs r₂₁ r₂₂ => let ⟨_, r₁₁', r₂₁'⟩ := diamond r₁₁ r₂₁; let ⟨_, r₁₂', r₂₂'⟩ := diamond r₁₂ r₂₂; ⟨_, sub r₁₂' r₁₁', sub r₂₂' r₂₁'⟩

def ParBetaRed.refl : {e : Term Γ} → ParBetaRed e e
  | .var _ => var
  | .abs _ => abs refl
  | .app .. => app refl refl

def BetaRed.toParBetaRed : (r : BetaRed e e') → ParBetaRed e e'
  | abs r => .abs r.toParBetaRed
  | app₁ r => .app r.toParBetaRed .refl
  | app₂ r => .app .refl r.toParBetaRed
  | app_abs => .app_abs .refl .refl

inductive TransClos {α : Type u} (R : (x y : α) → Type v) : (x y : α) → Type (max u v)
  | base (r : R x y) : TransClos R x y
  | refl : TransClos R x x
  | trans (r₁ : TransClos R x y) (r₂ : TransClos R y z) : TransClos R x z

def TransClos.map (f : (x : α) → β) (g : ∀ {x y}, R x y → R' (f x) (f y)) : (r : TransClos R x y) → TransClos R' (f x) (f y)
  | base r => base (g r)
  | refl => refl
  | trans r₁ r₂ => trans (r₁.map f @g) (r₂.map f @g)

def TransClos.flatMap (f : (x : α) → β) (g : ∀ {x y}, R x y → TransClos R' (f x) (f y)) : (r : TransClos R x y) → TransClos R' (f x) (f y)
  | base r => g r
  | refl => refl
  | trans r₁ r₂ => trans (r₁.flatMap f @g) (r₂.flatMap f @g)

def ParBetaRed.toBetaRed : (r : ParBetaRed e e') → TransClos BetaRed e e'
  | var => .refl
  | abs r => r.toBetaRed.map _ .abs
  | app r₁ r₂ => .trans (r₁.toBetaRed.map (fun e₁ => Term.app e₁ _) .app₁) (r₂.toBetaRed.map _ .app₂)
  | app_abs r₁ r₂ => .trans (r₁.toBetaRed.map (fun e₁ => Term.app (.abs e₁) _) fun r => .app₁ <| .abs r) <| .trans (r₂.toBetaRed.map _ .app₂) (.base .app_abs)

def ParBetaRed.confluence' (r₁ : ParBetaRed e e₁) : (r₂ : TransClos ParBetaRed e e₂) → Σ e', TransClos ParBetaRed e₁ e' × ParBetaRed e₂ e'
  | .base r₂ => let ⟨e', r₁', r₂'⟩ := diamond r₁ r₂; ⟨e', .base r₁', r₂'⟩
  | .refl => ⟨e₁, .refl, r₁⟩
  | .trans r₂₁ r₂₂ => let ⟨_, e₁₁', e₂₁'⟩ := confluence' r₁ r₂₁; let ⟨e', e₁₂', e₂'⟩ := confluence' e₂₁' r₂₂; ⟨e', .trans e₁₁' e₁₂', e₂'⟩

def ParBetaRed.confluence : (r₁ : TransClos ParBetaRed e e₁) → (r₂ : TransClos ParBetaRed e e₂) → Σ e', TransClos ParBetaRed e₁ e' × TransClos ParBetaRed e₂ e'
  | .refl, r₂ => ⟨e₂, r₂, .refl⟩
  | .base r₁, r₂ => let ⟨e', r₁', r₂'⟩ := confluence' r₁ r₂; ⟨e', r₁', .base r₂'⟩
  | .trans r₁₁ r₁₂, r₂ => let ⟨_, r₁₁', r₂₁'⟩ := confluence r₁₁ r₂; let ⟨e', r₁', r₂₂'⟩ := confluence r₁₂ r₁₁'; ⟨e', r₁', .trans r₂₁' r₂₂'⟩

def BetaRed.confluence (r₁ : TransClos BetaRed e e₁) (r₂ : TransClos BetaRed e e₂) : Σ e', TransClos BetaRed e₁ e' × TransClos BetaRed e₂ e' :=
  let ⟨e', r₁', r₂'⟩ := ParBetaRed.confluence (r₁.map _ toParBetaRed) (r₂.map (fun e => e) toParBetaRed)
  ⟨e', r₁'.flatMap _ ParBetaRed.toBetaRed, r₂'.flatMap _ ParBetaRed.toBetaRed⟩
