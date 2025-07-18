-- https://fredriknf.com/thesis/thesis.pdf

mutual

inductive Ctxt.Raw
  | nil : Ctxt.Raw
  | cons (Γ : Ctxt.Raw) (σ : Ty.Raw) : Ctxt.Raw

inductive Ty.Raw
  | base (Γ : Ctxt.Raw) : Ty.Raw
  | pi (Γ : Ctxt.Raw) (σ : Ty.Raw) (τ : Ty.Raw) : Ty.Raw

end

mutual

inductive Ctxt.Raw'
  | nil : Ctxt.Raw'
  | cons (Γ : Ctxt.Raw') (σ : Ty.Raw') : Ctxt.Raw'

inductive Ty.Raw'
  | base (Γ' : Ctxt.Raw') (Γ : Ctxt.Raw') : Ty.Raw'
  | pi (Γ' : Ctxt.Raw') (Γ : Ctxt.Raw') (σ : Ty.Raw') (τ : Ty.Raw') : Ty.Raw'

end

mutual

def Ctxt.Raw.f : Ctxt.Raw → Ctxt.Raw'
  | .nil => .nil
  | .cons Γ σ => .cons Γ.f σ.f

def Ty.Raw.f : Ty.Raw → Ty.Raw'
  | .base Γ => .base Γ.f Γ.f
  | .pi Γ σ τ => .pi Γ.f Γ.f σ.f τ.f

end

mutual

def Ctxt.Raw.g : Ctxt.Raw → Ctxt.Raw'
  | .nil => .nil
  | .cons Γ σ => .cons Γ.g (σ.g Γ.g)

def Ty.Raw.g (Γ' : Ctxt.Raw') : Ty.Raw → Ty.Raw'
  | .base Γ => .base Γ' Γ.g
  | .pi Γ σ τ => .pi Γ' Γ.g (σ.g Γ.g) (τ.g (.cons Γ.g (σ.g Γ.g)))

end

theorem Ctxt.Raw.f.inj : f Γ₁ = f Γ₂ → Γ₁ = Γ₂ := by
  apply @Ctxt.Raw.rec (fun Γ₁ => ∀ Γ₂, Γ₁.f = Γ₂.f → Γ₁ = Γ₂) (fun τ₁ => ∀ τ₂, τ₁.f = τ₂.f → τ₁ = τ₂)
  all_goals
    intros
    rename_i x h
    cases x <;> simp! at h
    repeat cases ‹_ ∧ _›
    congr <;> apply_rules

theorem Ty.Raw.f.inj : f τ₁ = f τ₂ → τ₁ = τ₂ := by
  apply @Ty.Raw.rec (fun Γ₁ => ∀ Γ₂, Γ₁.f = Γ₂.f → Γ₁ = Γ₂) (fun τ₁ => ∀ τ₂, τ₁.f = τ₂.f → τ₁ = τ₂)
  all_goals
    intros
    rename_i x h
    cases x <;> simp! at h
    repeat cases ‹_ ∧ _›
    congr <;> apply_rules

theorem Ctxt.Raw.g.inj : g Γ₁ = g Γ₂ → Γ₁ = Γ₂ := by
  apply @Ctxt.Raw.rec (fun Γ₁ => ∀ Γ₂, Γ₁.g = Γ₂.g → Γ₁ = Γ₂) (fun τ₁ => ∀ Γ₁ Γ₂ τ₂, τ₁.g Γ₁ = τ₂.g Γ₂ → Γ₁ = Γ₂ ∧ τ₁ = τ₂)
  all_goals
    intros
    rename_i x h
    cases x <;> simp! at h
    repeat simp only [forall_and] at ‹∀ _, _›
    repeat cases ‹_ ∧ _›
    and_intros <;> congr <;> apply_rules

theorem Ty.Raw.g.inj : g Γ₁ τ₁ = g Γ₂ τ₂ → Γ₁ = Γ₂ ∧ τ₁ = τ₂ := by
  apply @Ty.Raw.rec (fun Γ₁ => ∀ Γ₂, Γ₁.g = Γ₂.g → Γ₁ = Γ₂) (fun τ₁ => ∀ Γ₁ Γ₂ τ₂, τ₁.g Γ₁ = τ₂.g Γ₂ → Γ₁ = Γ₂ ∧ τ₁ = τ₂)
  all_goals
    intros
    rename_i x h
    cases x <;> simp! at h
    repeat simp only [forall_and] at ‹∀ _, _›
    repeat cases ‹_ ∧ _›
    and_intros <;> congr <;> apply_rules

def Ctxt : Type :=
  { Γ : Ctxt.Raw // Γ.f = Γ.g }

def Ty (Γ : Ctxt) : Type :=
  { τ : Ty.Raw // τ.f = τ.g Γ.val.g }

def Ctxt.nil : Ctxt :=
  ⟨.nil, rfl⟩

def Ctxt.cons (Γ : Ctxt) (σ : Ty Γ) : Ctxt :=
  ⟨.cons Γ.val σ.val, (congr (congrArg Raw'.cons Γ.property) σ.property :)⟩

def Ty.base (Γ : Ctxt) : Ty Γ :=
  ⟨.base Γ.val, (congr (congrArg Raw'.base Γ.property) Γ.property :)⟩

def Ty.pi (Γ : Ctxt) (σ : Ty Γ) (τ : Ty (.cons Γ σ)) : Ty Γ :=
  ⟨.pi Γ.val σ.val τ.val, (congr (congr (congr (congrArg Raw'.pi Γ.property) Γ.property) σ.property) τ.property :)⟩

section

variable
  {motive_1 : Ctxt → Sort u}
  {motive_2 : ∀ Γ, Ty Γ → Sort u}
  (nil : motive_1 .nil)
  (cons : ∀ Γ σ, motive_1 Γ → motive_2 Γ σ → motive_1 (.cons Γ σ))
  (base : ∀ Γ, motive_1 Γ → motive_2 Γ (.base Γ))
  (pi : ∀ Γ σ τ, motive_1 Γ → motive_2 Γ σ → motive_2 (.cons Γ σ) τ → motive_2 Γ (.pi Γ σ τ))

mutual

def Ctxt.rec'.raw : ∀ Γ hΓ, motive_1 ⟨Γ, hΓ⟩
  | .nil, _ => nil
  | .cons Γ σ, h => cons ⟨Γ, (Ctxt.Raw'.cons.inj h).left⟩ ⟨σ, (Ctxt.Raw'.cons.inj h).right⟩ (Ctxt.rec'.raw ..) (Ty.rec'.raw ..)

def Ty.rec'.raw Γ : ∀ τ hτ, motive_2 Γ ⟨τ, hτ⟩
  | .base Γ', h => Ctxt.Raw.g.inj ((Ty.Raw'.base.inj h).left.symm.trans (Ty.Raw'.base.inj h).right) ▸ base ⟨Γ', (Ty.Raw'.base.inj h).right⟩ (Ctxt.rec'.raw ..)
  | .pi Γ' σ τ, h => Ctxt.Raw.g.inj ((Ty.Raw'.pi.inj h).left.symm.trans (Ty.Raw'.pi.inj h).right.left) ▸ pi ⟨Γ', (Ty.Raw'.pi.inj h).right.left⟩ ⟨σ, (Ty.Raw'.pi.inj h).right.right.left⟩ ⟨τ, (Ty.Raw'.pi.inj h).right.right.right⟩ (Ctxt.rec'.raw ..) (Ty.rec'.raw ..) (Ty.rec'.raw ..)

end

def Ctxt.rec' Γ : motive_1 Γ :=
  rec'.raw nil cons base pi Γ.val Γ.property

def Ty.rec' Γ τ : motive_2 Γ τ :=
  rec'.raw nil cons base pi Γ τ.val τ.property

@[simp]
theorem Ctxt.rec'_nil : rec' nil cons base pi .nil = nil := rfl

@[simp]
theorem Ctxt.rec'_cons : rec' nil cons base pi (.cons Γ σ) = cons Γ σ (rec' nil cons base pi Γ) (Ty.rec' nil cons base pi Γ σ) := rfl

@[simp]
theorem Ty.rec'_base : rec' nil cons base pi Γ (.base Γ) = base Γ (Ctxt.rec' nil cons base pi Γ) := rfl

@[simp]
theorem Ty.rec'_pi : rec' nil cons base pi Γ (.pi Γ σ τ) = pi Γ σ τ (Ctxt.rec' nil cons base pi Γ) (rec' nil cons base pi Γ σ) (rec' nil cons base pi (.cons Γ σ) τ) := rfl

end

section

variable
  {motive_1 : Ctxt → Sort u}
  {motive_2 : ∀ Γ, Ty Γ → motive_1 Γ → Sort u}
  (nil : motive_1 .nil)
  (cons : ∀ Γ σ hΓ, motive_2 Γ σ hΓ → motive_1 (.cons Γ σ))
  (base : ∀ Γ hΓ, motive_2 Γ (.base Γ) hΓ)
  (pi : ∀ Γ σ τ hΓ hσ, motive_2 (.cons Γ σ) τ (cons Γ σ hΓ hσ) → motive_2 Γ (.pi Γ σ τ) hΓ)

mutual

def Ctxt.rec.raw : ∀ Γ hΓ, motive_1 ⟨Γ, hΓ⟩
  | .nil, _ => nil
  | .cons Γ σ, h => cons ⟨Γ, (Ctxt.Raw'.cons.inj h).left⟩ ⟨σ, (Ctxt.Raw'.cons.inj h).right⟩ (Ctxt.rec.raw ..) (Ty.rec.raw ..)

def Ty.rec.raw Γ hΓ : ∀ τ hτ, motive_2 Γ ⟨τ, hτ⟩ hΓ
  | .base Γ', h => Ctxt.Raw.g.inj ((Ty.Raw'.base.inj h).left.symm.trans (Ty.Raw'.base.inj h).right) ▸ base Γ hΓ
  | .pi Γ' σ τ, h => have := Ctxt.Raw.g.inj ((Ty.Raw'.pi.inj h).left.symm.trans (Ty.Raw'.pi.inj h).right.left); let σ := ⟨σ, this ▸ (Ty.Raw'.pi.inj h).right.right.left⟩; let τ : Ty (Γ.cons σ) := ⟨τ, (Ty.Raw'.pi.inj h).right.right.right.trans (this ▸ rfl)⟩; this ▸ pi Γ σ τ hΓ (Ty.rec.raw ..) (Ty.rec.raw ..)

end

def Ctxt.rec Γ : motive_1 Γ :=
  rec.raw nil cons base pi Γ.val Γ.property

def Ty.rec Γ τ : motive_2 Γ τ (Ctxt.rec nil cons base pi Γ) :=
  rec.raw nil cons base pi Γ (Ctxt.rec nil cons base pi Γ) τ.val τ.property

@[simp]
theorem Ctxt.rec_nil : rec nil cons base pi .nil = nil := rfl

@[simp]
theorem Ctxt.rec_cons : rec nil cons base pi (.cons Γ σ) = cons Γ σ (rec nil cons base pi Γ) (Ty.rec nil cons base pi Γ σ) := rfl

@[simp]
theorem Ty.rec_base : rec nil cons base pi Γ (.base Γ) = base Γ (Ctxt.rec nil cons base pi Γ) := rfl

@[simp]
theorem Ty.rec_pi : rec nil cons base pi Γ (.pi Γ σ τ) = pi Γ σ τ (Ctxt.rec nil cons base pi Γ) (rec nil cons base pi Γ σ) (rec nil cons base pi (.cons Γ σ) τ) := rfl

end

def Ctxt.id : Ctxt → Ctxt :=
  @Ctxt.rec (fun _ => Ctxt) (fun _ _ => Ty)
    (nil := nil)
    (cons := fun _ _ => cons)
    (base := fun _ => .base)
    (pi := fun _ _ _ => .pi)

def Ty.id : ∀ {Γ}, Ty Γ → Ty Γ.id :=
  @Ty.rec (fun _ => Ctxt) (fun _ _ => Ty)
    (nil := .nil)
    (cons := fun _ _ => .cons)
    (base := fun _ => base)
    (pi := fun _ _ _ => pi)

theorem Ctxt.id_eq : ∀ Γ, id Γ = Γ := by
  apply @rec (fun Γ => Γ.id = Γ) (fun Γ τ hΓ => τ.id = hΓ.symm ▸ τ)
  case nil => rfl
  case cons => intro Γ σ hΓ hσ; change Ctxt.cons Γ.id σ.id = _; grind
  case base => intro Γ hΓ; change Ty.base Γ.id = _; grind
  case pi => intro Γ σ τ hΓ hσ hτ; change Ty.pi Γ.id σ.id τ.id = _; grind

theorem Ty.id_eq : ∀ {Γ} τ, @id Γ τ = Γ.id_eq.symm ▸ τ := by
  apply @rec (fun Γ => Γ.id = Γ) (fun Γ τ hΓ => τ.id = hΓ.symm ▸ τ)
  case nil => rfl
  case cons => intro Γ σ hΓ hσ; change Ctxt.cons Γ.id σ.id = _; grind
  case base => intro Γ hΓ; change Ty.base Γ.id = _; grind
  case pi => intro Γ σ τ hΓ hσ hτ; change Ty.pi Γ.id σ.id τ.id = _; grind
