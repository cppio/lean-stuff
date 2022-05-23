import data.multiset.basic term

namespace linear

variable {n : ℕ}

inductive cctx : ℕ → Type
| nil : cctx 0
| cons {n} : ctx → cctx n → cctx (n + 1)

infixr ` ∷ `:66 := cctx.cons
notation `⟦` Δ:(foldr `, ` (Γ Δ, cctx.cons Γ Δ) cctx.nil `⟧`) := Δ

protected def cctx.repr_aux : bool → Π {n}, cctx n → string
| _ _ ⟦⟧ := ""
| tt _ (Γ ∷ Δ) := repr Γ ++ Δ.repr_aux ff
| ff _ (Γ ∷ Δ) := ", " ++ repr Γ ++ Δ.repr_aux ff

protected def cctx.repr (Δ : cctx n) : string := "⟦" ++ Δ.repr_aux tt ++ "⟧"

instance : has_repr (cctx n) := ⟨cctx.repr⟩

@[simp]
protected def cctx.append : Π {n}, cctx n → cctx n → cctx n
| _ ⟦⟧ ⟦⟧ := ⟦⟧
| _ (Γ₁ ∷ Δ₁) (Γ₂ ∷ Δ₂) := (Γ₁ ++ Γ₂) ∷ (Δ₁.append Δ₂)

instance : has_append (cctx n) := ⟨cctx.append⟩

namespace cctx

@[simp]
def head : cctx (n + 1) → ctx
| (Γ ∷ _) := Γ

@[simp]
def tail : cctx (n + 1) → cctx n
| (_ ∷ Δ) := Δ

@[simp]
def to_ctx : Π {n}, cctx n → ctx
| _ ⟦⟧ := []
| _ (Γ ∷ Δ) := Γ ++ Δ.to_ctx

@[simp]
lemma append_nil : ⟦⟧ ++ ⟦⟧ = ⟦⟧ := rfl

@[simp]
lemma append_cons (Γ₁) (Δ₁ : cctx n) (Γ₂ Δ₂) : Γ₁ ∷ Δ₁ ++ Γ₂ ∷ Δ₂ = (Γ₁ ++ Γ₂) ∷ (Δ₁ ++ Δ₂) := rfl

@[simp]
lemma append_assoc : Π {n} (Δ₁ Δ₂ Δ₃ : cctx n), Δ₁ ++ Δ₂ ++ Δ₃ = Δ₁ ++ (Δ₂ ++ Δ₃)
| _ ⟦⟧ ⟦⟧ ⟦⟧ := rfl
| _ (Γ₁ ∷ Δ₁) (Γ₂ ∷ Δ₂) (Γ₃ ∷ Δ₃) :=
  let this := congr_arg2 (∷) (Γ₁.append_assoc Γ₂ Γ₃) (Δ₁.append_assoc Δ₂ Δ₃) in
  this

theorem to_ctx_append : Π {n} (Δ₁ Δ₂ : cctx n), (Δ₁ ++ Δ₂).to_ctx ~ Δ₁.to_ctx ++ Δ₂.to_ctx
| _ ⟦⟧ ⟦⟧ := by refl
| _ (Γ₁ ∷ Δ₁) (Γ₂ ∷ Δ₂) := by {
    have := Δ₁.to_ctx_append Δ₂,
    simp [← multiset.coe_eq_coe, ← multiset.coe_add] at *,
    cc,
  }

@[simp]
def perm : Π {n}, cctx n → cctx n → Prop
| _ ⟦⟧ ⟦⟧ := true
| _ (Γ₁ ∷ Δ₁) (Γ₂ ∷ Δ₂) := Γ₁ ~ Γ₂ ∧ Δ₁.perm Δ₂

@[refl, simp]
lemma perm.refl : Π {n} (Δ : cctx n), Δ.perm Δ
| _ ⟦⟧ := trivial
| _ (Γ ∷ Δ) := ⟨list.perm.refl Γ, perm.refl Δ⟩

@[symm]
lemma perm.symm : Π {n} {Δ₁ Δ₂ : cctx n}, Δ₁.perm Δ₂ → Δ₂.perm Δ₁
| _ ⟦⟧ ⟦⟧ _ := trivial
| _ (_ ∷ _) (_ ∷ _) h := ⟨h.left.symm, h.right.symm⟩

@[trans]
lemma perm.trans : Π {n} {Δ₁ Δ₂ Δ₃ : cctx n}, Δ₁.perm Δ₂ → Δ₂.perm Δ₃ → Δ₁.perm Δ₃
| _ ⟦⟧ ⟦⟧ ⟦⟧ _ _ := trivial
| _ (_ ∷ _) (_ ∷ _) (_ ∷ _) h₁ h₂ := ⟨h₁.left.trans h₂.left, h₁.right.trans h₂.right⟩

lemma perm.append_left : Π {n} {Δ₁ Δ₂ : cctx n} Δ, Δ₁.perm Δ₂ → (Δ ++ Δ₁).perm (Δ ++ Δ₂)
| _ ⟦⟧ ⟦⟧ ⟦⟧ _ := trivial
| _ (_ ∷ _) (_ ∷ _) (_ ∷ _) h := ⟨list.perm.append_left _ h.left, perm.append_left _ h.right⟩

lemma perm.append_right : Π {n} {Δ₁ Δ₂ : cctx n} Δ, Δ₁.perm Δ₂ → (Δ₁ ++ Δ).perm (Δ₂ ++ Δ)
| _ ⟦⟧ ⟦⟧ ⟦⟧ _ := trivial
| _ (_ ∷ _) (_ ∷ _) (_ ∷ _) h := ⟨list.perm.append_right _ h.left, perm.append_right _ h.right⟩

lemma cctx.perm_append_comm : Π {n} {Δ₁ Δ₂ : cctx n}, (Δ₁ ++ Δ₂).perm (Δ₂ ++ Δ₁)
| _ ⟦⟧ ⟦⟧ := trivial
| _ (_ ∷ _) (_ ∷ _) := ⟨list.perm_append_comm, cctx.perm_append_comm⟩

@[simp]
protected def empty : Π n, cctx n
| 0 := ⟦⟧
| (n + 1) := [] ∷ empty n

@[simp]
theorem to_ctx_empty : Π n, (cctx.empty n).to_ctx = []
| 0 := rfl
| (n + 1) := to_ctx_empty n

theorem empty_of_to_ctx_nil : Π {n} {Δ : cctx n}, Δ.to_ctx = [] → Δ = cctx.empty _
| _ ⟦⟧ _ := rfl
| _ (Γ ∷ Δ) h :=
  let ⟨hΓ, hΔ⟩ := list.append_eq_nil.mp h in congr_arg2 (∷) hΓ (empty_of_to_ctx_nil hΔ)

@[simp]
theorem empty_append : Π {n} Δ, cctx.empty n ++ Δ = Δ
| _ ⟦⟧ := rfl
| _ (_ ∷ _) := congr_arg ((∷) _) (empty_append _)

@[simp]
theorem append_empty : Π {n} Δ, Δ ++ cctx.empty n = Δ
| _ ⟦⟧ := rfl
| _ (_ ∷ _) := congr_arg2 (∷) (list.append_nil _) (append_empty _)

def follows {n} (Δ₁ Δ₂ : cctx (n + 1)) :=
-- Σ' Δ, Δ₂.tail.perm (Δ ++ Δ₁.tail) ∧ Δ₁.head ~ (Δ.to_ctx ++ Δ₂.head)
{Δ // Δ₂.tail.perm (Δ ++ Δ₁.tail) ∧ Δ₁.head ~ (Δ.to_ctx ++ Δ₂.head)}

-- instance {n} {Δ₁ Δ₂ : cctx (n + 1)} : has_repr (Δ₁.follows Δ₂) := ⟨repr ∘ psigma.fst⟩
instance {n} {Δ₁ Δ₂ : cctx (n + 1)} : has_repr (Δ₁.follows Δ₂) := ⟨repr ∘ subtype.val⟩

@[simp]
theorem follows_cons {n} (Γ₁ Δ₁ Γ₂ Δ₂) :
--  (Γ₁ ∷ Δ₁).follows (Γ₂ ∷ Δ₂) = Σ' (Δ : cctx n), Δ₂.perm (Δ ++ Δ₁) ∧ Γ₁ ~ Δ.to_ctx ++ Γ₂ :=
  (Γ₁ ∷ Δ₁).follows (Γ₂ ∷ Δ₂) = {Δ : cctx n // Δ₂.perm (Δ ++ Δ₁) ∧ Γ₁ ~ Δ.to_ctx ++ Γ₂} :=
rfl

@[refl]
theorem follows.refl {n} (Δ : cctx (n + 1)) : Δ.follows Δ := ⟨
  cctx.empty _,
  Δ.tail.empty_append.symm ▸ perm.refl _,
  (to_ctx_empty n).symm ▸ (list.nil_append Δ.head).symm ▸ list.perm.refl _,
⟩

@[trans]
theorem follows.trans {n} {Δ₁ Δ₂ Δ₃ : cctx (n + 1)} :
  Δ₁.follows Δ₂ → Δ₂.follows Δ₃ → Δ₁.follows Δ₃ :=
begin
  rintros ⟨Δ₁₂, h₁₂⟩ ⟨Δ₂₃, h₂₃⟩,
  use Δ₁₂ ++ Δ₂₃,
  split,
  {
    apply h₂₃.left.trans,
    transitivity,
      apply perm.append_left,
      apply h₁₂.left,
    rw ←cctx.append_assoc,
    apply cctx.perm.append_right,
    apply cctx.perm_append_comm,
  },
  {
    have := to_ctx_append Δ₁₂ Δ₂₃,
    simp [← multiset.coe_eq_coe, ← multiset.coe_add] at *,
    cc,
  },
end

end cctx

end linear
