import check

open linear

#eval check ⟦[("x", one)]⟧ (t.var one "x")
#eval check ⟦[], [("x", one)]⟧ (t.var one "x")

theorem check_complete : Π {Γ a n} (e : cterm Γ a) (Δ : cctx (n + 1)),
  Δ.to_ctx = Γ → ∃ h, check Δ e.to_tterm = some ⟨Γ ∷ cctx.empty _, e, Δ.tail, h⟩
| _ _ n (c.var a x) (Γ ∷ Δ) h :=
  by {
    cases Γ with xa Γ,
    case list.nil {
      cases Δ with _ Γ Δ, contradiction,
      cases Γ with xa Γ,
      case list.nil {
        dsimp at h,
        dsimp [nat.add_zero],
        simp [check, check_var],
        simp [h],
        sorry,
      },
      case list.cons {
        sorry,
      },
    },
    case list.cons {
      simp at h,
      cases h.left,
      cases h.right.left,
      cases cctx.empty_of_to_ctx_nil h.right.right,
      simp [check, check_var],
    },
  }
| _ _ _ c.one_intro _ h :=
  by {
    cases cctx.empty_of_to_ctx_nil h,
    dsimp [nat.add_zero],
    simp [check],
    refl,
  }
/-
| _ _ (c.var a x) := by dsimp; simp [check, check_var]; refl
| _ _ c.one_intro := by dsimp; simp [check]; refl
| _ _ (@c.one_elim Γ₁ Γ₂ _ e₁ e₂) := by {
  cases check_complete e₁ with h₁ ih₁,
  cases check_complete e₂ with h₂ ih₂,
  dsimp at *,
  simp [check],
  dsimp,
  existsi list.perm.refl _,
}
-/
| _ _ _ (c.top_intro _) _ _ := sorry
| _ _ _ (c.zero_elim _ _ _) _ _ := sorry

example : false := begin
  generalize he : c.zero_elim [] one (c.var zero "x") = e,
  have : check ⟦[("x", zero)]⟧ e.to_tterm = none,
    rw ← he,
    refl,
  rw (check_complete e ⟦[("x", zero)]⟧ rfl).snd at this,
  contradiction,
end

def check' {a} (e : tterm a) : option (Σ Γ, cterm Γ a) :=
do ⟨Γ ∷ _, e, _⟩ ← check ⟦[]⟧ e,
   some ⟨Γ, e.flatten⟩

meta def unwrap' {a} : option (Σ Γ, cterm Γ a) → ctx
| (some ⟨Γ, _⟩) := Γ
| none := unwrap' none

meta def unwrap {a} : Π r, cterm (unwrap' r) a
| (some ⟨_, e⟩) := e
| none := unwrap none

#eval unwrap $ check' $
        t.cut "x" t.one_intro $
          t.cut "y" t.one_intro $
            t.one_elim (t.var one "y") $
              t.one_elim (t.var one "x") $
                t.one_intro

#eval unwrap $ check' $
        t.cut "x" t.one_intro $
          t.cut "y" t.one_intro $
            t.one_elim (t.var one "x") $
              t.one_elim (t.var one "y") $
                t.one_intro

/-
let x = () in
  let y = () in
    let () = y in
      let () = x in
        ⟨⟩
-/

#check u.cut "x" u.one_intro $
         u.cut "y" u.one_intro $
           u.one_elim (u.var "y") $
             u.one_elim (u.var "x") $
               u.top_intro

#check t.cut "x" t.one_intro $
         t.cut "y" t.one_intro $
           t.one_elim (t.var one "y") $
             t.one_elim (t.var one "x") $
               t.top_intro

#check c.cut "x" c.one_intro $
         c.cut "y" c.one_intro $
           c.one_elim (c.var one "y") $
             c.one_elim (c.var one "x") $
               c.top_intro []

/-
let x = () in
  let y = () in
    let () = x in
      let () = y in
        ⟨⟩
-/

#check u.cut "x" u.one_intro $
         u.cut "y" u.one_intro $
           u.one_elim (u.var "x") $
             u.one_elim (u.var "y") $
               u.top_intro

#check t.cut "x" t.one_intro $
         t.cut "y" t.one_intro $
           t.one_elim (t.var one "x") $
             t.one_elim (t.var one "y") $
               t.top_intro

#check c.cut "x" c.one_intro $
         c.cut "y" c.one_intro $ c.exchange (list.perm.swap _ _ _) $
           c.one_elim (c.var one "x") $
             c.one_elim (c.var one "y") $
               c.top_intro []
