-- https://fredriknf.com/thesis/thesis.pdf

mutual

inductive Ctxt.Pre
  | nil : Ctxt.Pre
  | cons (Γ : Ctxt.Pre) (σ : Ty.Pre) : Ctxt.Pre

inductive Ty.Pre
  | base (Γ : Ctxt.Pre) : Ty.Pre
  | pi (Γ : Ctxt.Pre) (σ : Ty.Pre) (τ : Ty.Pre) : Ty.Pre

end

mutual

inductive Ctxt.Pre.Good : Ctxt.Pre → Prop
  | nil : Ctxt.Pre.Good .nil
  | cons (hΓ : Γ.Good) (hσ : σ.Good Γ) : Ctxt.Pre.Good (.cons Γ σ)

inductive Ty.Pre.Good : Ctxt.Pre → Ty.Pre → Prop
  | base (hΓ : Γ.Good) : Ty.Pre.Good Γ (.base Γ)
  | pi (hΓ : Γ.Good) (hσ : σ.Good Γ) (hτ : τ.Good (.cons Γ σ)) : Ty.Pre.Good Γ (.pi Γ σ τ)

end

def Ctxt : Type :=
  { Γ : Ctxt.Pre // Γ.Good }

def Ty (Γ : Ctxt) : Type :=
  { τ : Ty.Pre // τ.Good Γ.val }

def Ctxt.nil : Ctxt :=
  ⟨.nil, .nil⟩

def Ctxt.cons (Γ : Ctxt) (σ : Ty Γ) : Ctxt :=
  ⟨.cons Γ.val σ.val, .cons Γ.property σ.property⟩

def Ty.base (Γ : Ctxt) : Ty Γ :=
  ⟨.base Γ.val, .base Γ.property⟩

def Ty.pi (Γ : Ctxt) (σ : Ty Γ) (τ : Ty (.cons Γ σ)) : Ty Γ :=
  ⟨.pi Γ.val σ.val τ.val, .pi Γ.property σ.property τ.property⟩

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
  | .cons Γ σ, h => cons ⟨Γ, by cases h; assumption⟩ ⟨σ, by cases h; assumption⟩ (Ctxt.rec'.raw ..) (Ty.rec'.raw ..)

def Ty.rec'.raw Γ : ∀ τ hτ, motive_2 Γ ⟨τ, hτ⟩
  | .base Γ', h => have : Γ'.Good := (by cases h; assumption); (by cases h; rfl : Γ = ⟨Γ', this⟩) ▸ base ⟨Γ', this⟩ (Ctxt.rec'.raw ..)
  | .pi Γ' σ τ, h => have : Γ'.Good := (by cases h; assumption); (by cases h; rfl : Γ = ⟨Γ', this⟩) ▸ pi ⟨Γ', this⟩ ⟨σ, by cases h; assumption⟩ ⟨τ, by cases h; assumption⟩ (Ctxt.rec'.raw ..) (Ty.rec'.raw ..) (Ty.rec'.raw ..)

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
  | .cons Γ σ, h => cons ⟨Γ, by cases h; assumption⟩ ⟨σ, by cases h; assumption⟩ (Ctxt.rec.raw ..) (Ty.rec.raw ..)


def Ty.rec.raw Γ hΓ : ∀ τ hτ, motive_2 Γ ⟨τ, hτ⟩ hΓ
  | .base Γ', h => have : Γ'.Good := (by cases h; assumption); (by cases h; rfl : Γ = ⟨Γ', this⟩) ▸ base Γ hΓ
  | .pi Γ' σ τ, h => have : Γ'.Good := (by cases h; assumption); have hσ := (by cases h; assumption); have hτ := (by cases h; assumption); (by cases h; rfl : Γ = ⟨Γ', this⟩) ▸ pi Γ ⟨σ, hσ⟩ ⟨τ, hτ⟩ hΓ (Ty.rec.raw ..) (Ty.rec.raw ..)

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
