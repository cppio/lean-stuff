import data.set.basic
import data.finset.basic
import data.fin.tuple
import data.set.prod
import data.nat.modeq

def set.finitely_indexed {α} (s : set α) := ∃ n (f : fin n → s), function.surjective f

def union₁ {α} {s t : set α} : s → s ∪ t :=
λ x, ⟨x.val, or.inl x.property⟩

def union₂ {α} {s t : set α} : t → s ∪ t :=
λ x, ⟨x.val, or.inr x.property⟩

example {α} {s t : set α} : s.finitely_indexed → t.finitely_indexed → (s ∪ t).finitely_indexed :=
λ ⟨ns, fs, hs⟩ ⟨nt, ft, ht⟩, ⟨ns + nt, fin.append rfl (union₁ ∘ fs) (union₂ ∘ ft), λ ⟨x, hx⟩, by {
  cases hx,

  cases hs ⟨x, hx⟩ with n hn,
  existsi fin.cast_add nt n,
  have : ↑n < ns := n.property,
  simp [fin.append, this, union₁, hn],

  cases ht ⟨x, hx⟩ with n hn,
  existsi fin.nat_add ns n,
  simp [fin.append, union₂, hn],
}⟩

def fin.div' : ∀ {n m}, fin (n * m) → fin n
| 0 m x := fin.elim0' $ cast (congr_arg fin $ zero_mul m) x
| n 0 x := fin.elim0 x
| (n + 1) (m + 1) ⟨x, hx⟩ := ⟨x / (m + 1), nat.div_lt_of_lt_mul (nat.mul_comm (n + 1) (m + 1) ▸ hx)⟩

def fin.mod' {n} : fin n → ∀ m > 0, fin m
| ⟨x, hx⟩ m hm := ⟨x % m, x.mod_lt hm⟩

def fin.prod : ∀ {m n α β o}, o = m * n → (fin m → α) → (fin n → β) → fin o → α × β
| m 0 α β o ho u v i := fin.elim0' $ cast (congr_arg fin ho) i
| m (n + 1) α β o ho u v i := ⟨u $ fin.div' $ cast (congr_arg fin ho) i, v $ i.mod' (n + 1) (nat.zero_lt_succ n)⟩

def prod₁ {α β} {s : set α} {t : set β} : s × t → ↥(s ×ˢ t) :=
λ x, ⟨⟨x.fst.val, x.snd.val⟩, x.fst.property, x.snd.property⟩

example {α β} {s : set α} {t : set β} : s.finitely_indexed → t.finitely_indexed → set.finitely_indexed (s ×ˢ t) :=
λ ⟨ns, fs, hs⟩ ⟨nt, ft, ht⟩, ⟨ns * nt, prod₁ ∘ fin.prod rfl fs ft, λ ⟨⟨xs, xt⟩, ⟨hxs, hxt⟩⟩, by {
  cases hs ⟨xs, hxs⟩ with sn hsn,
  cases ht ⟨xt, hxt⟩ with tn htn,
  clear _fun_match,
  cases nt,
  exact fin.elim0 tn,
  cases ns,
  exact fin.elim0 sn,
  use sn * nt.succ + tn,
  calc ↑sn * nt.succ + ↑tn ≤ (ns.succ - 1) * nt.succ + ↑tn : nat.add_le_add_right (nat.mul_le_mul_right _ $ nat.le_pred_of_lt sn.property) _
                  ... < (ns.succ - 1) * nt.succ + nt.succ : nat.add_le_add_left tn.property _
                  ... = ns * nt.succ + nt.succ : rfl
                  ... = ns.succ * nt.succ : (nat.succ_mul _ _).symm,
  simp [prod₁, fin.prod, fin.div', fin.mod'],
  split,

  have : nt + 1 ∣ ↑sn * nt.succ,
    rw mul_comm,
    apply nat.dvd_mul_right,
  simp [nat.add_div_of_dvd_right this],
  have : ↑tn / (nt + 1) = 0 := nat.div_eq_zero tn.property,
  simp [this, hsn],

  have : ↑tn % (nt + 1) = ↑tn := nat.mod_eq_of_lt tn.property,
  simp [nat.add_mod, this, htn],
}⟩
