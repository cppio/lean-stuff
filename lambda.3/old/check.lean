import cctx

namespace linear

def check_var (a x) : Π {n} Δ, option (Σ (Δ' : cctx (n + 1)), cterm Δ'.head a × Δ'.follows Δ)
| _ (_ :: _ :: _ ∷ _) := none
| _ ([(x', a')] ∷ Δ) :=
  if h : x = x' ∧ a = a'
  then some ⟨[(x, a)] ∷ Δ, c.var a x, cctx.empty _, by simp [h]⟩
  else none
| _ ([] ∷ ⟦⟧) := none
| _ ([] ∷ [] ∷ Δ) :=
  do ⟨Γ ∷ Δ, e, Δ', h⟩ ← check_var ([] ∷ Δ),
     some ⟨Γ ∷ [] ∷ Δ, e, [] ∷ Δ', by simp at h; simp [h]⟩
| _ ([] ∷ (x', a') :: Γ ∷ Δ) :=
  if h : x = x' ∧ a = a'
  then some ⟨[(x, a)] ∷ Γ ∷ Δ, c.var a x, [(x, a)] ∷ cctx.empty _, by simp [h]⟩
  else do ⟨Γ' ∷ Γ ∷ Δ, e, Δ', h⟩ ← check_var ([] ∷ Γ ∷ Δ),
          some ⟨Γ' ∷ (x', a') :: Γ ∷ Δ, e, Δ', by {
            cases Δ',
            simp [← multiset.coe_eq_coe, ← multiset.coe_add, ← multiset.cons_coe] at *,
            simp [h],
          }, by simp at h; simp [h]⟩

def check : Π {n a} Δ, tterm a → option (Σ (Δ' : cctx (n + 1)), cterm Δ'.head a × Δ'.follows Δ)
| _ _ Δ (t.var a x) := check_var a x Δ
| _ _ Δ (@t.cut a _ x e₁ e₂) :=
  do ⟨Γ₁ ∷ Γ ∷ Δ, e₁, Γ' ∷ Δ₁, h₁⟩ ← check ([] ∷ Δ) e₁,
     ⟨Γ₂ ∷ Δ, e₂, Δ₂, h₂⟩ ← check ((x, a) :: Γ ∷ Δ) e₂,
     some ⟨(Γ₁ ++ (Δ₂.to_ctx ++ Γ)) ∷ Δ, c.cut x e₁ $ c.exchange (by {
       simp [← multiset.coe_eq_coe, ← multiset.coe_add, ← multiset.cons_coe] at *,
       simp [h₂],
     }) e₂, Δ₁ ++ Δ₂, by {
       clear _do_match _do_match,
       dedup,
       cases Δ,
       split,
       {
         simp at *,
         apply h₁.left.right.trans,
         apply cctx.perm.append_left,
         simp [h₂],
       },
       {
         have := Δ₁.to_ctx_append Δ₂,
         simp [← multiset.coe_eq_coe, ← multiset.coe_add] at *,
         cc,
       },
     }⟩
| _ _ Δ t.one_intro :=
  match Δ with
  | [] ∷ Δ := some ⟨[] ∷ Δ, c.one_intro, cctx.empty _, by simp⟩
  | _ :: _ ∷ _ := none
  end
| _ _ Δ (t.one_elim e₁ e₂) :=
  do ⟨Γ₁ ∷ Δ, e₁, Γ' ∷ Δ₁, h₁⟩ ← check ([] ∷ Δ) e₁,
     ⟨Γ₂ ∷ Δ, e₂, Δ₂, h₂⟩ ← check Δ e₂,
     some ⟨(Γ₁ ++ Γ₂) ∷ Δ, c.one_elim e₁ e₂, Δ₁ ++ Δ₂, by {
       clear _do_match _do_match,
       dedup,
       cases Δ,
       cases Δ_1,
       split,
       {
         simp at *,
         apply h₁.left.right.trans,
         apply cctx.perm.append_left,
         simp [h₂],
       },
       {
         have := Δ₁.to_ctx_append Δ₂,
         simp [← multiset.coe_eq_coe, ← multiset.coe_add] at *,
         cc,
       },
     }⟩

| _ _ _ t.top_intro := none
| _ _ _ (t.zero_elim _ _) := none

theorem check_var_sound {a x} : Π {n Δ r}, @check_var a x n Δ = some r → r.snd.fst.to_tterm = t.var a x
| _ ((_, _) :: _ :: _ ∷ _) := by simp [check_var]
| _ ([(x', a')] ∷ _) :=
  by {
    simp [check_var],
    rintros (_ | ⟨_, _, _⟩) ⟨_, _, _⟩,
    cases (infer_instance : decidable (x = x' ∧ a = a')) with h h,
    case decidable.is_true {
      rcases h with ⟨⟨⟩, ⟨⟩⟩,
      simp,
      rintros ⟨⟩ ⟨⟩ hr,
      simp at hr,
      rw ← hr.left,
      simp,
    },
    case decidable.is_false {
      simp [h],
    },
  }
| _ ([] ∷ ⟦⟧) := by simp [check_var]
| _ ([] ∷ [] ∷ Δ) :=
  by {
    simp [check_var],
    rintros (_ | ⟨_, _, _ | ⟨_, _, _⟩⟩) ⟨_, _ | ⟨_, _, _⟩, _⟩ (_ | ⟨_, _, _⟩) _ ⟨_, _⟩ hr₁,
    simp [check_var._match_1],
    rintros ⟨⟩ ⟨⟩ ⟨⟩ hr,
    simp at hr,
    rw ← hr.left,
    simp [check_var_sound hr₁],
  }
| _ ([] ∷ (x', a') :: _ ∷ _) :=
  by {
    simp [check_var],
    rintros (_ | ⟨_, _, _ | ⟨_, _, _⟩⟩) ⟨_, _ | ⟨_, _, _⟩, _⟩,
    cases (infer_instance : decidable (x = x' ∧ a = a')) with h h,
    case decidable.is_true {
      rcases h with ⟨⟨⟩, ⟨⟩⟩,
      simp,
      rintros ⟨⟩ ⟨⟩ ⟨⟩ hr,
      simp at hr,
      rw ← hr.left,
      simp,
    },
    case decidable.is_false {
      simp [h],
      rintros (_ | ⟨_, _, _ | ⟨_, _, _⟩⟩) _ ⟨_ | ⟨_, _, _⟩, _⟩ hr₁,
      simp [check_var._match_2],
      rintros ⟨⟩ ⟨⟩ ⟨⟩ hr,
      simp at hr,
      rw ← hr.left,
      simp [check_var_sound hr₁],
    },
  }

theorem check_sound : Π {n a Δ e r}, @check n a Δ e = some r → r.snd.fst.to_tterm = e
| _ _ _ (t.var _ _) _ := check_var_sound
| _ _ Δ (@t.cut a _ x e₁ e₂) _ :=
  by {
    simp [check],
    rintros (_ | ⟨_, _, _ | ⟨_, _, _⟩⟩) _ ⟨_ | ⟨_, _, _⟩, _⟩ hr₁,
    simp [check._match_2],
    rintros (_ | ⟨_, _, _⟩) _ ⟨_, _⟩ hr₂,
    simp [check._match_1],
    intro hr,
    rw ← hr,
    simp [check_sound hr₁, check_sound hr₂],
  }
| _ _ ([] ∷ _) t.one_intro _ :=
  by {
    simp [check],
    intro hr,
    rw ← hr,
    simp,
  }
| _ _ (_ :: _ ∷ _) t.one_intro _ := by simp [check]
| _ _ Δ (t.one_elim e₁ e₂) _ := by {
    simp [check],
    rintros (_ | ⟨_, _, _ | ⟨_, _, _⟩⟩) _ ⟨_ | ⟨_, _, _⟩, _⟩ hr₁,
    simp [check._match_5],
    rintros (_ | ⟨_, _, _⟩) _ ⟨_, _⟩ hr₂,
    simp [check._match_4],
    intro hr,
    rw ← hr,
    simp [check_sound hr₁, check_sound hr₂],
  }
| _ _ _ t.top_intro _ := by simp [check]
| _ _ _ (t.zero_elim _ _) _ := by simp [check]

end linear
