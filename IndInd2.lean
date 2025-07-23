mutual

inductive Ctx.Pre
  | nil
  | consTp (Γ : Ctx.Pre)
  | consTm (Γ : Ctx.Pre) (τ : Tp.Pre)

inductive TpVar.Pre
  | here (Γ : Ctx.Pre)
  | there (Γ : Ctx.Pre) (α : TpVar.Pre)
  | skip (Γ : Ctx.Pre) (τ : Tp.Pre) (α : TpVar.Pre)

inductive Tp.Pre
  | var (Γ : Ctx.Pre) (α : TpVar.Pre)
  | arr (Γ : Ctx.Pre) (τ₁ τ₂ : Tp.Pre)
  | all (Γ : Ctx.Pre) (τ : Tp.Pre)

end

mutual

inductive Ctx.Pre.Good : Ctx.Pre → Prop
  | nil : Ctx.Pre.Good .nil
  | consTp (hΓ : Γ.Good) : Ctx.Pre.Good (.consTp Γ)
  | consTm (hΓ : Γ.Good) (hτ : τ.Good Γ) : Ctx.Pre.Good (.consTm Γ τ)

inductive TpVar.Pre.Good : Ctx.Pre → TpVar.Pre → Prop
  | here (hΓ : Γ.Good) : TpVar.Pre.Good (.consTp Γ) (.here Γ)
  | there (hΓ : Γ.Good) (hα : α.Good Γ) : TpVar.Pre.Good (.consTp Γ) (.there Γ α)
  | skip (hΓ : Γ.Good) (hτ : τ.Good Γ) (hα : α.Good Γ) : TpVar.Pre.Good (.consTm Γ τ) (.skip Γ τ α)

inductive Tp.Pre.Good : Ctx.Pre → Tp.Pre → Prop
  | var (hΓ : Γ.Good) (hα : α.Good Γ) : Tp.Pre.Good Γ (.var Γ α)
  | arr (hΓ : Γ.Good) (hτ₁ : τ₁.Good Γ) (hτ₂ : τ₂.Good Γ) : Tp.Pre.Good Γ (.arr Γ τ₁ τ₂)
  | all (hΓ : Γ.Good) (hτ : τ.Good (.consTp Γ)) : Tp.Pre.Good Γ (.all Γ τ)

end

def Ctx : Type :=
  { Γ : Ctx.Pre // Γ.Good }

def TpVar (Γ : Ctx) : Type :=
  { α : TpVar.Pre // α.Good Γ.val }

def Tp (Γ : Ctx) : Type :=
  { τ : Tp.Pre // τ.Good Γ.val }

def Ctx.nil : Ctx :=
  ⟨.nil, .nil⟩

def Ctx.consTp (Γ : Ctx) : Ctx :=
  ⟨.consTp Γ.val, .consTp Γ.property⟩

def Ctx.consTm (Γ : Ctx) (τ : Tp Γ) : Ctx :=
  ⟨.consTm Γ.val τ.val, .consTm Γ.property τ.property⟩

def TpVar.here : TpVar (.consTp Γ) :=
  ⟨.here Γ.val, .here Γ.property⟩

def TpVar.there (α : TpVar Γ) : TpVar (.consTp Γ) :=
  ⟨.there Γ.val α.val, .there Γ.property α.property⟩

def TpVar.skip (α : TpVar Γ) : TpVar (.consTm Γ τ) :=
  ⟨.skip Γ.val τ.val α.val, .skip Γ.property τ.property α.property⟩

def Tp.var (α : TpVar Γ) : Tp Γ :=
  ⟨.var Γ.val α.val, .var Γ.property α.property⟩

def Tp.arr (τ₁ τ₂ : Tp Γ) : Tp Γ :=
  ⟨.arr Γ.val τ₁.val τ₂.val, .arr Γ.property τ₁.property τ₂.property⟩

def Tp.all (τ : Tp (.consTp Γ)) : Tp Γ :=
  ⟨.all Γ.val τ.val, .all Γ.property τ.property⟩

section

variable
  {motive_1 : Ctx → Sort u}
  {motive_2 : ∀ Γ, TpVar Γ → Sort u}
  {motive_3 : ∀ Γ, Tp Γ → Sort u}
  (nil : motive_1 .nil)
  (consTp : ∀ Γ, motive_1 Γ → motive_1 (.consTp Γ))
  (consTm : ∀ Γ τ, motive_1 Γ → motive_3 Γ τ → motive_1 (.consTm Γ τ))
  (here : ∀ Γ, motive_1 Γ → motive_2 (.consTp Γ) .here)
  (there : ∀ Γ α, motive_1 Γ → motive_2 Γ α → motive_2 (.consTp Γ) (.there α))
  (skip : ∀ Γ τ α, motive_1 Γ → motive_3 Γ τ → motive_2 Γ α → motive_2 (.consTm Γ τ) (.skip α))
  (var : ∀ Γ α, motive_1 Γ → motive_2 Γ α → motive_3 Γ (.var α))
  (arr : ∀ Γ τ₁ τ₂, motive_1 Γ → motive_3 Γ τ₁ → motive_3 Γ τ₂ → motive_3 Γ (.arr τ₁ τ₂))
  (all : ∀ Γ τ, motive_1 Γ → motive_3 (.consTp Γ) τ → motive_3 Γ (.all τ))

mutual

def Ctx.rec'.raw : ∀ Γ hΓ, motive_1 ⟨Γ, hΓ⟩
  | .nil, _ => nil
  | .consTp Γ, h => consTp ⟨Γ, by cases h; assumption⟩ (Ctx.rec'.raw ..)
  | .consTm Γ τ, h => consTm ⟨Γ, by cases h; assumption⟩ ⟨τ, by cases h; assumption⟩ (Ctx.rec'.raw ..) (Tp.rec'.raw ..)

def TpVar.rec'.raw Γ : ∀ α hα, motive_2 Γ ⟨α, hα⟩
  | .here Γ', h => have : Γ'.Good := (by cases Γ; cases h; assumption); (by cases Γ; cases h; rfl : Γ = .consTp ⟨Γ', this⟩) ▸ here ⟨Γ', this⟩ (Ctx.rec'.raw ..)
  | .there Γ' α, h => have : Γ'.Good := (by cases Γ; cases h; assumption); (by cases Γ; cases h; rfl : Γ = .consTp ⟨Γ', this⟩) ▸ there ⟨Γ', this⟩ ⟨α, by (try cases Γ); cases h; assumption⟩ (Ctx.rec'.raw ..) (TpVar.rec'.raw ..)
  | .skip Γ' τ α, h => have : Γ'.Good := (by cases Γ; cases h; assumption); have : τ.Good Γ' := (by cases Γ; cases h; assumption); (by cases Γ; cases h; rfl : Γ = .consTm ⟨Γ', ‹_›⟩ ⟨τ, this⟩) ▸ skip ⟨Γ', ‹_›⟩ ⟨τ, this⟩ ⟨α, by (try cases Γ); cases h; assumption⟩ (Ctx.rec'.raw ..) (Tp.rec'.raw ..) (TpVar.rec'.raw ..)

def Tp.rec'.raw Γ : ∀ τ hτ, motive_3 Γ ⟨τ, hτ⟩
  | .var Γ' α, h => have : Γ'.Good := (by cases h; assumption); (by cases h; rfl : Γ = ⟨Γ', this⟩) ▸ var ⟨Γ', this⟩ ⟨α, by cases h; assumption⟩ (Ctx.rec'.raw ..) (TpVar.rec'.raw ..)
  | .arr Γ' τ₁ τ₂, h => have : Γ'.Good := (by cases h; assumption); (by cases h; rfl : Γ = ⟨Γ', this⟩) ▸ arr ⟨Γ', this⟩ ⟨τ₁, by cases h; assumption⟩ ⟨τ₂, by cases h; assumption⟩ (Ctx.rec'.raw ..) (Tp.rec'.raw ..) (Tp.rec'.raw ..)
  | .all Γ' τ, h => have : Γ'.Good := (by cases h; assumption); (by cases h; rfl : Γ = ⟨Γ', this⟩) ▸ all ⟨Γ', this⟩ ⟨τ, by cases h; assumption⟩ (Ctx.rec'.raw ..) (Tp.rec'.raw ..)
 
end

def Ctx.rec' Γ : motive_1 Γ :=
  rec'.raw nil consTp consTm here there skip var arr all Γ.val Γ.property

def TpVar.rec' Γ α : motive_2 Γ α :=
  rec'.raw nil consTp consTm here there skip var arr all Γ α.val α.property

def Tp.rec' Γ τ : motive_3 Γ τ :=
  rec'.raw nil consTp consTm here there skip var arr all Γ τ.val τ.property

@[simp]
theorem Ctx.rec'_nil : rec' nil consTp consTm here there skip var arr all .nil = nil := rfl

@[simp]
theorem Ctx.rec'_consTp : rec' nil consTp consTm here there skip var arr all (.consTp Γ) = consTp Γ (rec' nil consTp consTm here there skip var arr all Γ) := rfl

@[simp]
theorem Ctx.rec'_consTm : rec' nil consTp consTm here there skip var arr all (.consTm Γ τ) = consTm Γ τ (rec' nil consTp consTm here there skip var arr all Γ) (Tp.rec' nil consTp consTm here there skip var arr all Γ τ) := rfl

@[simp]
theorem TpVar.rec'_here : rec' nil consTp consTm here there skip var arr all (.consTp Γ) .here = here Γ (Ctx.rec' nil consTp consTm here there skip var arr all Γ) := rfl

@[simp]
theorem TpVar.rec'_there : rec' nil consTp consTm here there skip var arr all (.consTp Γ) (.there α) = there Γ α (Ctx.rec' nil consTp consTm here there skip var arr all Γ) (rec' nil consTp consTm here there skip var arr all Γ α) := rfl

@[simp]
theorem TpVar.rec'_skip : rec' nil consTp consTm here there skip var arr all (.consTm Γ τ) (.skip α) = skip Γ τ α (Ctx.rec' nil consTp consTm here there skip var arr all Γ) (Tp.rec' nil consTp consTm here there skip var arr all Γ τ) (rec' nil consTp consTm here there skip var arr all Γ α) := rfl

@[simp]
theorem Tp.rec'_var : rec' nil consTp consTm here there skip var arr all Γ (.var α) = var Γ α (Ctx.rec' nil consTp consTm here there skip var arr all Γ) (TpVar.rec' nil consTp consTm here there skip var arr all Γ α) := rfl

@[simp]
theorem Tp.rec'_arr : rec' nil consTp consTm here there skip var arr all Γ (.arr τ₁ τ₂) = arr Γ τ₁ τ₂ (Ctx.rec' nil consTp consTm here there skip var arr all Γ) (Tp.rec' nil consTp consTm here there skip var arr all Γ τ₁) (Tp.rec' nil consTp consTm here there skip var arr all Γ τ₂) := rfl

@[simp]
theorem Tp.rec'_all : rec' nil consTp consTm here there skip var arr all Γ (.all τ) = all Γ τ (Ctx.rec' nil consTp consTm here there skip var arr all Γ) (Tp.rec' nil consTp consTm here there skip var arr all (.consTp Γ) τ) := rfl

end

section

variable
  {motive_1 : Ctx → Sort u}
  {motive_2 : ∀ Γ, TpVar Γ → motive_1 Γ → Sort u}
  {motive_3 : ∀ Γ, Tp Γ → motive_1 Γ → Sort u}
  (nil : motive_1 .nil)
  (consTp : ∀ Γ, motive_1 Γ → motive_1 (.consTp Γ))
  (consTm : ∀ Γ τ hΓ, motive_3 Γ τ hΓ → motive_1 (.consTm Γ τ))
  (here : ∀ Γ hΓ, motive_2 (.consTp Γ) .here (consTp Γ hΓ))
  (there : ∀ Γ α hΓ, motive_2 Γ α hΓ → motive_2 (.consTp Γ) (.there α) (consTp Γ hΓ))
  (skip : ∀ Γ τ α hΓ hτ, motive_2 Γ α hΓ → motive_2 (.consTm Γ τ) (.skip α) (consTm Γ τ hΓ hτ))
  (var : ∀ Γ α hΓ, motive_2 Γ α hΓ → motive_3 Γ (.var α) hΓ)
  (arr : ∀ Γ τ₁ τ₂ hΓ, motive_3 Γ τ₁ hΓ → motive_3 Γ τ₂ hΓ → motive_3 Γ (.arr τ₁ τ₂) hΓ)
  (all : ∀ Γ τ hΓ, motive_3 (.consTp Γ) τ (consTp Γ hΓ) → motive_3 Γ (.all τ) hΓ)

def motive_1' : ∀ Γ hΓ, motive_1 ⟨Γ, hΓ⟩ → Sort (max 1 u)
  | .nil, h, hΓ' => PUnit
  | .consTp Γ, h, hΓ' => (hΓ : motive_1 ⟨Γ, by cases h; assumption⟩) ×' hΓ' = consTp _ hΓ ×' motive_1' Γ _ hΓ
  | .consTm Γ τ, h, hΓ' => (hΓ : motive_1 ⟨Γ, by cases h; assumption⟩) ×' (hτ : motive_3 _ ⟨τ, by cases h; assumption⟩ hΓ) ×' hΓ' = consTm _ _ hΓ hτ ×' motive_1' Γ _ hΓ

mutual

def Ctx.rec.raw : ∀ Γ hΓ, Σ' hΓ', motive_1' consTp consTm Γ hΓ hΓ'
  | .nil, _ => ⟨nil, ⟨⟩⟩
  | .consTp Γ, h => ⟨consTp ⟨Γ, by cases h; assumption⟩ (Ctx.rec.raw ..).1, _, rfl, (Ctx.rec.raw ..).2⟩
  | .consTm Γ τ, h => ⟨consTm ⟨Γ, by cases h; assumption⟩ ⟨τ, by cases h; assumption⟩ (Ctx.rec.raw ..).1 (Tp.rec.raw _ _ (Ctx.rec.raw ..).2 ..), _, _, rfl, (Ctx.rec.raw ..).2⟩

def TpVar.rec.raw Γ hΓ (hhΓ : motive_1' consTp consTm Γ.val Γ.property hΓ) : ∀ α hα, motive_2 Γ ⟨α, hα⟩ hΓ
  | .here Γ', h => by
    have : Γ'.Good := by cases Γ; cases h; assumption
    obtain rfl : Γ = .consTp ⟨Γ', this⟩ := by cases Γ; cases h; rfl
    exact hhΓ.2.1 ▸ here ⟨Γ', this⟩ hhΓ.1
  | .there Γ' α, h => by
    have : Γ'.Good := by cases Γ; cases h; assumption
    obtain rfl : Γ = .consTp ⟨Γ', this⟩ := by cases Γ; cases h; rfl
    exact hhΓ.2.1 ▸ there ⟨Γ', this⟩ ⟨α, by cases h; assumption⟩ hhΓ.1 (TpVar.rec.raw _ _ hhΓ.2.2 ..)
  | .skip Γ' τ α, h => by
    have : Γ'.Good ∧ τ.Good Γ' := by cases Γ; cases h; constructor <;> assumption
    obtain rfl : Γ = .consTm ⟨Γ', this.left⟩ ⟨τ, this.right⟩ := by cases Γ; cases h; rfl
    exact hhΓ.2.2.1 ▸ skip ⟨Γ', this.left⟩ ⟨τ, this.right⟩ ⟨α, by cases h; assumption⟩ hhΓ.1 hhΓ.2.1 (TpVar.rec.raw _ _ hhΓ.2.2.2 ..)

def Tp.rec.raw Γ hΓ (hhΓ : motive_1' consTp consTm Γ.val Γ.property hΓ) : ∀ τ hτ, motive_3 Γ ⟨τ, hτ⟩ hΓ
  | .var Γ' α, h => by
    have : Γ'.Good := by cases h; assumption
    obtain rfl : Γ = ⟨Γ', this⟩ := by cases h; rfl
    exact var ⟨Γ', this⟩ ⟨α, by cases h; assumption⟩ hΓ (TpVar.rec.raw _ _ hhΓ ..)
  | .arr Γ' τ₁ τ₂, h => by
    have : Γ'.Good := by cases h; assumption
    obtain rfl : Γ = ⟨Γ', this⟩ := by cases h; rfl
    exact arr ⟨Γ', this⟩ ⟨τ₁, by cases h; assumption⟩ ⟨τ₂, by cases h; assumption⟩ hΓ (Tp.rec.raw _ _ hhΓ ..) (Tp.rec.raw _ _ hhΓ ..)
  | .all Γ' τ, h => by
    have : Γ'.Good := by cases h; assumption
    obtain rfl : Γ = ⟨Γ', this⟩ := by cases h; rfl
    exact all ⟨Γ', this⟩ ⟨τ, by cases h; assumption⟩ hΓ (Tp.rec.raw _ _ (by exact ⟨hΓ, rfl, hhΓ⟩) ..)

end

def Ctx.rec Γ : motive_1 Γ :=
  (rec.raw nil consTp consTm here there skip var arr all Γ.val Γ.property).1

def TpVar.rec Γ α : motive_2 Γ α (Ctx.rec nil consTp consTm here there skip var arr all Γ) :=
  rec.raw nil consTp consTm here there skip var arr all Γ _ (Ctx.rec.raw nil consTp consTm here there skip var arr all Γ.val Γ.property).2 α.val α.property

def Tp.rec Γ τ : motive_3 Γ τ (Ctx.rec nil consTp consTm here there skip var arr all Γ) :=
  rec.raw nil consTp consTm here there skip var arr all Γ _ (Ctx.rec.raw nil consTp consTm here there skip var arr all Γ.val Γ.property).2 τ.val τ.property

@[simp]
theorem Ctx.rec_nil : rec nil consTp consTm here there skip var arr all .nil = nil := rfl

@[simp]
theorem Ctx.rec_consTp : rec nil consTp consTm here there skip var arr all (.consTp Γ) = consTp Γ (rec nil consTp consTm here there skip var arr all Γ) := rfl

@[simp]
theorem Ctx.rec_consTm : rec nil consTp consTm here there skip var arr all (.consTm Γ τ) = consTm Γ τ (rec nil consTp consTm here there skip var arr all Γ) (Tp.rec nil consTp consTm here there skip var arr all Γ τ) := rfl

@[simp]
theorem TpVar.rec_here : rec nil consTp consTm here there skip var arr all (.consTp Γ) .here = here Γ (Ctx.rec nil consTp consTm here there skip var arr all Γ) := rfl

@[simp]
theorem TpVar.rec_there : rec nil consTp consTm here there skip var arr all (.consTp Γ) (.there α) = there Γ α (Ctx.rec nil consTp consTm here there skip var arr all Γ) (rec nil consTp consTm here there skip var arr all Γ α) := rfl

@[simp]
theorem TpVar.rec_skip : rec nil consTp consTm here there skip var arr all (.consTm Γ τ) (.skip α) = skip Γ τ α (Ctx.rec nil consTp consTm here there skip var arr all Γ) (Tp.rec nil consTp consTm here there skip var arr all Γ τ) (rec nil consTp consTm here there skip var arr all Γ α) := rfl

@[simp]
theorem Tp.rec_var : rec nil consTp consTm here there skip var arr all Γ (.var α) = var Γ α (Ctx.rec nil consTp consTm here there skip var arr all Γ) (TpVar.rec nil consTp consTm here there skip var arr all Γ α) := rfl

@[simp]
theorem Tp.rec_arr : rec nil consTp consTm here there skip var arr all Γ (.arr τ₁ τ₂) = arr Γ τ₁ τ₂ (Ctx.rec nil consTp consTm here there skip var arr all Γ) (Tp.rec nil consTp consTm here there skip var arr all Γ τ₁) (Tp.rec nil consTp consTm here there skip var arr all Γ τ₂) := rfl

@[simp]
theorem Tp.rec_all : rec nil consTp consTm here there skip var arr all Γ (.all τ) = all Γ τ (Ctx.rec nil consTp consTm here there skip var arr all Γ) (Tp.rec nil consTp consTm here there skip var arr all (.consTp Γ) τ) := rfl

end

def Ctx.id : Ctx → Ctx :=
  @rec (fun _ => Ctx) (fun _ _ => TpVar) (fun _ _ => Tp)
    (nil := .nil)
    (consTp := fun _ => .consTp)
    (consTm := fun _ _ => .consTm)
    (here := fun _ _ => .here)
    (there := fun _ _ _ => .there)
    (skip := fun _ _ _ _ _ => .skip)
    (var := fun _ _ _ => .var)
    (arr := fun _ _ _ _ => .arr)
    (all := fun _ _ _ => .all)

def TpVar.id : ∀ {Γ}, TpVar Γ → TpVar Γ.id :=
  @rec (fun _ => Ctx) (fun _ _ => TpVar) (fun _ _ => Tp)
    (nil := .nil)
    (consTp := fun _ => .consTp)
    (consTm := fun _ _ => .consTm)
    (here := fun _ _ => .here)
    (there := fun _ _ _ => .there)
    (skip := fun _ _ _ _ _ => .skip)
    (var := fun _ _ _ => .var)
    (arr := fun _ _ _ _ => .arr)
    (all := fun _ _ _ => .all)

def Tp.id : ∀ {Γ}, Tp Γ → Tp Γ.id :=
  @rec (fun _ => Ctx) (fun _ _ => TpVar) (fun _ _ => Tp)
    (nil := .nil)
    (consTp := fun _ => .consTp)
    (consTm := fun _ _ => .consTm)
    (here := fun _ _ => .here)
    (there := fun _ _ _ => .there)
    (skip := fun _ _ _ _ _ => .skip)
    (var := fun _ _ _ => .var)
    (arr := fun _ _ _ _ => .arr)
    (all := fun _ _ _ => .all)

theorem Ctx.id_eq : ∀ Γ, id Γ = Γ := by
  apply @rec (fun Γ => Γ.id = Γ) (fun Γ α hΓ => α.id = hΓ.symm ▸ α) (fun Γ τ hΓ => τ.id = hΓ.symm ▸ τ)
  case nil => rfl
  case consTp => intro Γ hΓ; change Ctx.consTp Γ.id = _; grind
  case consTm => intro Γ τ hΓ hτ; change Ctx.consTm Γ.id τ.id = _; grind
  case here => intro Γ hΓ; change @TpVar.here Γ.id = _; grind
  case there => intro Γ α hΓ hα; change TpVar.there α.id = _; grind
  case skip => intro Γ τ α hΓ hτ hα; change @TpVar.skip _ τ.id α.id = _; grind
  case var => intro Γ α hΓ hα; change Tp.var α.id = _; grind
  case arr => intro Γ τ₁ τ₂ hΓ hτ₁ hτ₂; change Tp.arr τ₁.id τ₂.id = _; grind
  case all => intro Γ τ hΓ hτ; change @Tp.all Γ.id τ.id = _; grind

theorem TpVar.id_eq : ∀ {Γ} α, @id Γ α = Γ.id_eq.symm ▸ α := by
  apply @rec (fun Γ => Γ.id = Γ) (fun Γ α hΓ => α.id = hΓ.symm ▸ α) (fun Γ τ hΓ => τ.id = hΓ.symm ▸ τ)
  case nil => rfl
  case consTp => intro Γ hΓ; change Ctx.consTp Γ.id = _; grind
  case consTm => intro Γ τ hΓ hτ; change Ctx.consTm Γ.id τ.id = _; grind
  case here => intro Γ hΓ; change @TpVar.here Γ.id = _; grind
  case there => intro Γ α hΓ hα; change TpVar.there α.id = _; grind
  case skip => intro Γ τ α hΓ hτ hα; change @TpVar.skip _ τ.id α.id = _; grind
  case var => intro Γ α hΓ hα; change Tp.var α.id = _; grind
  case arr => intro Γ τ₁ τ₂ hΓ hτ₁ hτ₂; change Tp.arr τ₁.id τ₂.id = _; grind
  case all => intro Γ τ hΓ hτ; change @Tp.all Γ.id τ.id = _; grind

theorem Tp.id_eq : ∀ {Γ} τ, @id Γ τ = Γ.id_eq.symm ▸ τ := by
  apply @rec (fun Γ => Γ.id = Γ) (fun Γ α hΓ => α.id = hΓ.symm ▸ α) (fun Γ τ hΓ => τ.id = hΓ.symm ▸ τ)
  case nil => rfl
  case consTp => intro Γ hΓ; change Ctx.consTp Γ.id = _; grind
  case consTm => intro Γ τ hΓ hτ; change Ctx.consTm Γ.id τ.id = _; grind
  case here => intro Γ hΓ; change @TpVar.here Γ.id = _; grind
  case there => intro Γ α hΓ hα; change TpVar.there α.id = _; grind
  case skip => intro Γ τ α hΓ hτ hα; change @TpVar.skip _ τ.id α.id = _; grind
  case var => intro Γ α hΓ hα; change Tp.var α.id = _; grind
  case arr => intro Γ τ₁ τ₂ hΓ hτ₁ hτ₂; change Tp.arr τ₁.id τ₂.id = _; grind
  case all => intro Γ τ hΓ hτ; change @Tp.all Γ.id τ.id = _; grind
