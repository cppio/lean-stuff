import logic.basic
import data.nat.basic
import data.fin.basic
import tactic.by_contra

namespace social_choice.pref

variables (α : Type*) (n : ℕ)

structure preorder := (r : α → α → Prop) (total : total r) (trans : transitive r)

structure order := (preorder : preorder α) (antisymm : anti_symmetric preorder.r)

def profile := fin n → preorder α

def agg := profile α n → preorder α

variables {α n}

instance : has_coe_to_fun (preorder α) (λ _, α → α → Prop) := ⟨preorder.r⟩

instance : has_coe_to_fun (order α) (λ _, α → α → Prop) := ⟨preorder.r ∘ order.preorder⟩

@[simp] lemma preorder.coe (r : α → α → Prop) (total : total r) (trans : transitive r) : ⇑(preorder.mk r total trans) = r := rfl

notation [parsing_only] x ` ≤⟪`:35 r `⟫ ` y:35 := r x y

notation [parsing_only] x ` <⟪`:35 r `⟫ ` y:35 := ¬r y x

lemma preorder.lt_trans {r : preorder α} {x y z} (hxy : x <⟪r⟫ y) (hyz : y <⟪r⟫ z) : x <⟪r⟫ z :=
begin
  cases r.total z y with _ hyz',
    contradiction,
  exact hxy ∘ r.trans hyz',
end

namespace agg

variables (f : agg α n)

def unanimity := ∀ (p : profile α n) x y, (∀ i, x <⟪p i⟫ y) → x <⟪f p⟫ y
def independence := ∀ (p q : profile α n) x y, (∀ i, x <⟪p i⟫ y ↔ x <⟪q i⟫ y) → (x <⟪f p⟫ y ↔ x <⟪f q⟫ y)

end agg

/-\--------\-/

def extreme (r : preorder α) (x) := (∀ y ≠ x, x <⟪r⟫ y) ∨ (∀ y ≠ x, y <⟪r⟫ x)

def exists_extreme₁ (x) : Σ' r : preorder α, ∀ y ≠ x, x <⟪r⟫ y :=
begin
  use λ a b, a = x ∨ b ≠ x,
  intros a b,
  by_cases hax : a = x; simp [hax],
  intros a b c hab hbc,
  cases hab,
    simp [hab],
  cases hbc,
    swap,
    simp [hbc],
  contradiction,
  dsimp [coe_fn, has_coe_to_fun.coe],
  simp,
end

def exists_extreme₂ (x) : Σ' r : preorder α, ∀ y ≠ x, y <⟪r⟫ x :=
begin
  use λ a b, a ≠ x ∨ b = x,
  intros a b,
  by_cases hax : a = x; simp [hax],
  intros a b c hab hbc,
  cases hab,
    simp [hab],
  cases hbc,
    swap,
    simp [hbc],
  contradiction,
  dsimp [coe_fn, has_coe_to_fun.coe],
  simp,
end

def exists_preorder {x y z} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : Σ' r : preorder α, x <⟪r⟫ y ∧ y <⟪r⟫ z ∧ x <⟪r⟫ z :=
begin
  use λ a b, (a = x ∨ b ≠ x) ∧ (a ≠ z ∨ b = z),
  intros a b,
  by_cases hax : a = x; simp [hax, hxz]; by_cases hbz : b = z; simp [hbz, hxz.symm],
  intros a b c hab hbc,
  cases hab with hab hab',
  cases hbc with hbc hbc',
  cases hab,
    simp [hab, hxz],
  cases hbc',
    swap,
    simp [hbc', hxz.symm],
  simp [hbc'] at hab',
  simp [hab] at hbc,
  simp [hab', hbc],
  dsimp [coe_fn, has_coe_to_fun.coe],
  simp [hxy.symm, hyz, hxz],
end

def move_top (r : preorder α) (x) : Σ' r' : preorder α, (∀ a ≠ x, a <⟪r'⟫ x) ∧ (∀ (a ≠ x) (c ≠ x), (a <⟪r'⟫ c ↔ a <⟪r⟫ c) ∧ (c <⟪r'⟫ a ↔ c <⟪r⟫ a)) :=
begin
  use λ a b, b = x ∨ a ≠ x ∧ r a b,
  intros a b,
  by_cases hax : a = x; by_cases hbx : b = x; simp [hax, hbx],
  apply r.total,
  intros a b c hab hbc,
  cases hab; cases hbc;
    simp [hab, hbc],
  simp [hab] at hbc,
  contradiction,
  exact or.inr (r.trans hab.right hbc.right),
  split,
    intros a hax,
    simp [coe_fn, has_coe_to_fun.coe, hax],
  intros a hax c hcx,
  simp [coe_fn, has_coe_to_fun.coe, hax, hcx],
end

def move_bot (r : preorder α) (x) : Σ' r' : preorder α, (∀ a ≠ x, x <⟪r'⟫ a) ∧ (∀ (a ≠ x) (c ≠ x), (a <⟪r'⟫ c ↔ a <⟪r⟫ c) ∧ (c <⟪r'⟫ a ↔ c <⟪r⟫ a)) :=
begin
  use λ a b, a = x ∨ b ≠ x ∧ r a b,
  intros a b,
  by_cases hax : a = x; by_cases hbx : b = x; simp [hax, hbx],
  apply r.total,
  intros a b c hab hbc,
  cases hab; cases hbc;
    simp [hab, hbc],
  simp [hab] at hbc,
  contradiction,
  exact or.inr (r.trans hab.right hbc.right),
  split,
    intros a hax,
    simp [coe_fn, has_coe_to_fun.coe, hax],
  intros a hax c hcx,
  simp [coe_fn, has_coe_to_fun.coe, hax, hcx],
end

def extreme_seq (b : α) : fin (n + 1) → profile α n :=
λ j i, ite (i.cast_succ < j) (exists_extreme₂ b).fst (exists_extreme₁ b).fst

lemma extreme_seq_extreme (b : α) (j) (i : fin n) : extreme (extreme_seq b j i) b :=
begin
  by_cases hij : i.cast_succ < j; simp [extreme_seq, hij],
  exact or.inr (exists_extreme₂ b).snd,
  exact or.inl (exists_extreme₁ b).snd,
end

lemma extreme_seq_succ (b : α) (j i : fin n) (hij : i ≠ j) : extreme_seq b j.cast_succ i = extreme_seq b j.succ i :=
begin
  simp [extreme_seq, has_lt.lt, fin.lt],
  change ite (i < j) _ _ = ite (i.val < j.val.succ) _ _,
  cases lt_or_gt_of_ne hij with hij' hij',
    simp only [hij', hij'.step],
  have : ¬i.val < j.val.succ := λ h, not_lt_of_gt hij' (lt_of_le_of_ne (nat.le_of_lt_succ h) hij),
  simp only [not_lt_of_gt hij', this],
end

variables {C : fin 3 → α} (hC : function.injective C)
include C hC

lemma card₃ (a b : α) : ∃ c, c ≠ a ∧ c ≠ b :=
begin
  by_cases hx : C 0 = a ∨ C 0 = b,
    swap,
    exact ⟨C 0, not_or_distrib.mp hx⟩,
  by_cases hy : C 1 = a ∨ C 1 = b,
    swap,
    exact ⟨C 1, not_or_distrib.mp hy⟩,
  by_cases hz : C 2 = a ∨ C 2 = b,
    swap,
    exact ⟨C 2, not_or_distrib.mp hz⟩,
  exfalso,
  cases hx,
    cases hy,
      cases hC (hx.trans hy.symm),
    cases hz,
      cases hC (hx.trans hz.symm),
    cases hC (hy.trans hz.symm),
  cases hy,
    cases hz,
      cases hC (hy.trans hz.symm),
    cases hC (hx.trans hz.symm),
  cases hC (hx.trans hy.symm),
end

variables (f : agg α n) (fu : f.unanimity) (fi : f.independence)
include f fu fi

lemma extremal {p : profile α n} {b} (h : ∀ i, extreme (p i) b) : extreme (f p) b :=
begin
  unfold extreme,
  by_contra' h',
  cases h' with ha hc,
  cases ha with a' ha,
  cases ha with hab ha,
  cases hc with c' hc,
  cases hc with hcb hc,
  have : ∃ a c, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a ≤⟪f p⟫ b ∧ b ≤⟪f p⟫ c,
    by_cases hac : a' = c',
      subst hac,
      have hd := card₃ hC b a',
      cases hd with d hd,
      have hbd := (f p).total b d,
      cases hbd,
        exact ⟨a', d, hab, hd.left.symm, hd.right.symm, ha, hbd⟩,
      exact ⟨d, a', hd.left, hcb.symm, hd.right, hbd, hc⟩,
    exact ⟨a', c', hab, hcb.symm, hac, ha, hc⟩,
  clear ha hab a' hc hcb c',
  cases this with a this,
  cases this with c this,
  cases this with hab this,
  cases this with hbc this,
  cases this with hac this,
  cases this with ha hc,

  have : ∀ i, ∃ q : preorder α, c <⟪q⟫ a ∧ (b <⟪q⟫ a ↔ b <⟪p i⟫ a) ∧ (c <⟪q⟫ b ↔ c <⟪p i⟫ b),
    intro i,
    specialize h i,
    cases h,
      cases exists_preorder hbc hac.symm hab.symm with q hq,
      use q,
      use hq.right.left,
      simp [h a hab, h c hbc.symm, hq.left, hq.right.right],
      have : q c b ∨ q b c := q.total c b,
      simp [hq.left] at this,
      simp [this],
      have : (p i) c b ∨ (p i) b c := (p i).total c b,
      simp [h c hbc.symm] at this,
      simp [this],
    cases exists_preorder hac.symm hab hbc.symm with q hq,
    use q,
    use hq.left,
    simp [h a hab, h c hbc.symm, hq.right.left, hq.right.right],
    have : (p i) a b ∨ (p i) b a := (p i).total a b,
    cases this,
      simp [this],
      have : q a b ∨ q b a := q.total a b,
      simp [hq.right.left] at this,
      exact this,
    exfalso,
    exact h a hab this,

  let q := λ i, classical.some (this i),
  have ia := fi q p b a _,
    swap,
    intro i,
    exact (classical.some_spec (this i)).right.left,
  have ic := fi q p c b _,
    swap,
    intro i,
    exact (classical.some_spec (this i)).right.right,
  simp [ha] at ia,
  simp [hc] at ic,
  have := fu q c a _,
    swap,
    intro i,
    exact (classical.some_spec (this i)).left,
  exact this ((f q).trans ia ic),
end

lemma extreme_seq_extreme' (b : α) (j : fin (n + 1)) : extreme (f (extreme_seq b j)) b :=
extremal hC f fu fi $ extreme_seq_extreme b j

lemma extreme_seq_0 (b a : α) (hab : a ≠ b) : b <⟪f (extreme_seq b 0)⟫ a :=
begin
  apply fu,
  intro i,
  change ¬(ite (i.val < 0) (exists_extreme₂ _).fst _) _ _,
  simp,
  apply (exists_extreme₁ _).snd,
  exact hab,
end

lemma extreme_seq_n (b a : α) (hab : a ≠ b) : a <⟪f (extreme_seq b (fin.last n))⟫ b :=
begin
  apply fu,
  intro i,
  change ¬(ite (i.val < n) (exists_extreme₂ _).fst _) _ _,
  have := i.property,
  simp only [this, if_pos],
  apply (exists_extreme₂ _).snd,
  exact hab,
end

lemma pivotal (b) : ∃ nb : fin n, ∀ a ≠ b, b <⟪f (extreme_seq b nb.cast_succ)⟫ a ∧ a <⟪f (extreme_seq b nb.succ)⟫ b :=
begin
  have : ∀ j i, extreme (extreme_seq b j i) b,
    apply extreme_seq_extreme b,
  have he : ∀ j, extreme (f (extreme_seq b j)) b := λ j, extremal hC f fu fi (this j),
  have he0 : ∀ a ≠ b, b <⟪f (extreme_seq b 0)⟫ a,
    exact extreme_seq_0 hC f fu fi b,
  have hen : ∀ a ≠ b, a <⟪f (extreme_seq b (fin.last n))⟫ b,
    exact extreme_seq_n hC f fu fi b,

  have hnb : (∃ nb : fin n, ∀ a ≠ b, b <⟪f (extreme_seq b nb.cast_succ)⟫ a ∧ a <⟪f (extreme_seq b nb.succ)⟫ b) ∨ (∀ k : fin (n + 1), ∀ a ≠ b, b <⟪f (extreme_seq b k)⟫ a),
    apply @nat.rec (λ m, ∀ hmn : m ≤ n, (∃ nb : fin n, ∀ a ≠ b, b <⟪f (extreme_seq b nb.cast_succ)⟫ a ∧ a <⟪f (extreme_seq b nb.succ)⟫ b) ∨ (∀ k : fin (m + 1), ∀ a ≠ b, b <⟪f (extreme_seq b ⟨k.val, nat.le_trans k.property (nat.succ_le_succ hmn)⟩)⟫ a)) _ _ n (nat.le_refl n),
    intro hmn,
    right,
    intro k,
    cases k with k hk,
    cases k,
    exact he0,
    have hk' := nat.lt_of_succ_lt_succ hk,
    cases hk',
    intros n' ih hn',
    specialize ih ((nat.le_succ n').trans hn'),
    cases ih,
      exact or.inl ih,
    specialize he ⟨n' + 1, nat.succ_lt_succ hn'⟩,
    cases he,
      right,
      intro k,
      apply fin.last_cases _ _ k,
        intros a hab,
        specialize he a hab,
        exact he,
      intros i a hab,
      specialize ih i a hab,
      exact ih,
    left,
    use ⟨n', hn'⟩,
    intros a hab,
    split,
      specialize ih (fin.last n') a hab,
      exact ih,
    specialize he a hab,
    exact he,

  cases hnb,
    swap,
    specialize hnb (fin.last n),
    by_cases hCb : C 0 = b,
      by_cases hCb' : C 1 = b,
        specialize hC (hCb.trans hCb'.symm),
        cases hC,
      specialize hen (C 1) hCb',
      specialize hnb (C 1) hCb',
      have : (f (extreme_seq b (fin.last n))) b (C 1) ∨ (f (extreme_seq b (fin.last n))) (C 1) b := (f (extreme_seq b (fin.last n))).total b (C 1),
      simp [hen, hnb] at this,
      contradiction,
    specialize hen (C 0) hCb,
    specialize hnb (C 0) hCb,
    have : (f (extreme_seq b (fin.last n))) b (C 0) ∨ (f (extreme_seq b (fin.last n))) (C 0) b := (f (extreme_seq b (fin.last n))).total b (C 0),
    simp [hen, hnb] at this,
    contradiction,

  exact hnb,
end

lemma dictator (b) : ∃ nb : fin n, (∀ a ≠ b, b <⟪f (extreme_seq b nb.cast_succ)⟫ a ∧ a <⟪f (extreme_seq b nb.succ)⟫ b) ∧ ∀ (p : profile α n) (a ≠ b) (c ≠ b), c <⟪p nb⟫ a → c <⟪f p⟫ a :=
begin
  have := pivotal hC f fu fi b,
  cases this with nb hnb,
  use nb,
  use hnb,
  intros r a hab c hcb hac,
  have hac' : a ≠ c,
    intro hac',
    subst hac',
    have := (r nb).total a a,
    cases this; exact hac this,
  let s : ∀ i : fin n, preorder α := λ i, ite (i < nb) (move_top (r i) b).fst (ite (i > nb) (move_bot (r i) b).fst (exists_preorder hcb hab.symm hac'.symm).fst),
  have h₁ := fi (extreme_seq b nb.cast_succ) s b a _,
    swap,
    intro i,
    simp [extreme_seq, s],
    by_cases hi : i < nb; simp [hi],
      simp [exists_extreme₂, move_top],
    by_cases hi' : nb < i; simp [hi'],
      simp [exists_extreme₁, move_bot],
    simp [exists_extreme₁, exists_preorder, hab, hab.symm],
  have h₂ := fi (extreme_seq b nb.succ) s c b _,
    swap,
    intro i,
    simp [extreme_seq, s, has_lt.lt, fin.lt],
    change ¬(ite (i.val < nb.val.succ) (exists_extreme₂ _).fst _) _ _ ↔ ¬(ite (i.val < nb.val) (move_top _ _).fst _) _ _,
    by_cases hi : i.val < nb.val; simp only [hi],
      simp only [hi.step],
      simp [exists_extreme₂, move_top],
    simp only [if_false],
    change _ ↔ ¬(ite (nb.val < i.val) (move_bot _ _).fst _) _ _,
    by_cases hi' : nb.val < i.val; simp only [hi'],
      have : ¬i.val < nb.val.succ := λ h, not_lt_of_gt hi' (lt_of_le_of_ne (nat.le_of_lt_succ h) (ne_of_gt hi')),
      simp only [this],
      simp [exists_extreme₁, move_bot],
    have hinb := lt_trichotomy i.val nb.val,
    cases hinb,
      contradiction,
    cases hinb,
      swap,
      contradiction,
    simp only [hinb, nat.lt_succ_self],
    simp [exists_extreme₂, exists_preorder, hcb, hcb.symm],

  simp [hnb a hab] at h₁,
  simp [hnb c hcb] at h₂,
  apply (fi s r c a _).mp (preorder.lt_trans h₂ h₁),
  intro i,
  simp [s],
  by_cases hi : i < nb; simp [hi],
    simp [move_top, hab, hcb],
  by_cases hi' : nb < i; simp [hi'],
    simp [move_bot, hab, hcb],
  have hinb := lt_trichotomy i nb,
  cases hinb,
    contradiction,
  cases hinb,
    swap,
    contradiction,
  subst hinb,
  simp [exists_preorder, hac', hac],
end

theorem arrow : ∃ d, ∀ (p : profile α n) x y, x <⟪p d⟫ y → x <⟪f p⟫ y :=
begin
  cases dictator hC f fu fi (C 0) with d hd,
  use d,
  intros p x y hxy,
  have hxy' : x ≠ y,
    intro hxy',
    subst hxy',
    have := (p d).total x x,
    cases this; exact hxy this,
  by_cases hxhy : x = C 0 ∨ y = C 0,
    swap,
    rw not_or_distrib at hxhy,
    exact hd.right p y hxhy.right x hxhy.left hxy,
  cases card₃ hC x y with z hz,
  cases dictator hC f fu fi z with d' hd',
  have : d' = d,
    cases hxhy,
      subst hxhy,
      by_contra,
      have := extreme_seq_extreme (C 0) d.cast_succ d',
      unfold extreme at this,
      replace this := this.elim (λ h, or.inl $ h y hxy'.symm) (λ h, or.inr $ h y hxy'.symm),
      have : (C 0 <⟪extreme_seq (C 0) d.succ d'⟫ y ∧ y <⟪f (extreme_seq (C 0) d.succ)⟫ C 0) ∨ (y <⟪extreme_seq (C 0) d.cast_succ d'⟫ C 0 ∧ C 0 <⟪f (extreme_seq (C 0) d.cast_succ)⟫ y),
        cases this,
          left,
          split,
            rw extreme_seq_succ (C 0) d d' h at this,
            exact this,
          exact (hd.left y hxy'.symm).right,
        right,
        split,
          exact this,
        exact (hd.left y hxy'.symm).left,
      cases this with this' this',
        cases (f (extreme_seq (C 0) d.succ)).total (C 0) y with hyC hyC,
          exact this'.right hyC,
        exact hd'.right (extreme_seq (C 0) d.succ) y hz.right.symm (C 0) hz.left.symm this'.left hyC,
      cases (f (extreme_seq (C 0) d.cast_succ)).total y (C 0) with hyC hyC,
        exact this'.right hyC,
      exact hd'.right (extreme_seq (C 0) d.cast_succ) (C 0) hz.left.symm y hz.right.symm this'.left hyC,
    subst hxhy,
    by_contra,
    have := extreme_seq_extreme (C 0) d.cast_succ d',
    unfold extreme at this,
    replace this := this.elim (λ h, or.inl $ h x hxy') (λ h, or.inr $ h x hxy'),
    have : (C 0 <⟪extreme_seq (C 0) d.succ d'⟫ x ∧ x <⟪f (extreme_seq (C 0) d.succ)⟫ C 0) ∨ (x <⟪extreme_seq (C 0) d.cast_succ d'⟫ C 0 ∧ C 0 <⟪f (extreme_seq (C 0) d.cast_succ)⟫ x),
      cases this,
        left,
        split,
          rw extreme_seq_succ (C 0) d d' h at this,
          exact this,
        exact (hd.left x hxy').right,
      right,
      split,
        exact this,
      exact (hd.left x hxy').left,
    cases this with this' this',
      cases (f (extreme_seq (C 0) d.succ)).total (C 0) x with hxC hxC,
        exact this'.right hxC,
      exact hd'.right (extreme_seq (C 0) d.succ) x hz.left.symm (C 0) hz.right.symm this'.left hxC,
    cases (f (extreme_seq (C 0) d.cast_succ)).total x (C 0) with hxC hxC,
      exact this'.right hxC,
    exact hd'.right (extreme_seq (C 0) d.cast_succ) (C 0) hz.right.symm x hz.left.symm this'.left hxC,
  subst this,
  exact hd'.right p y hz.right.symm x hz.left.symm hxy,
end

end social_choice.pref

#print social_choice.pref.arrow
