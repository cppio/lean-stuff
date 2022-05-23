import data.bitvec.basic

theorem vector.to_list_tail {α : Type*} {n : ℕ} {v : vector α n} :
  v.tail.to_list = v.to_list.tail :=
begin
  cases v with vl,
  cases vl; simp [vector.tail],
end

variables {n : ℕ} (x y z : bitvec n)

/-
def bitvec.sbb' (b : bool) : bitvec (n+1) := let ⟨b, z⟩ := x.sbb y b in b ::ᵥ z

def bitvec.of_int' : Π (n : ℕ), ℤ → bitvec n
| 0 := λ _, bitvec.of_nat 0 0
| (n+1) := bitvec.of_int n
-/

theorem bitvec.to_nat_inj :
  x.to_nat = y.to_nat ↔ x = y :=
begin
  split,

  intro h,
  have := congr_arg (bitvec.of_nat n) h,
  simp [bitvec.of_nat_to_nat] at this,
  exact this,

  intro h,
  simp [h],
end

theorem bitvec.mod_to_nat :
  x.to_nat % 2 ^ n = x.to_nat :=
begin
  have := @bitvec.to_nat_of_nat n x.to_nat,
  rw bitvec.of_nat_to_nat at this,
  exact this.symm,
end

theorem tail_of_nat {m : ℕ} :
  (bitvec.of_nat n m).tail = bitvec.of_nat (n - 1) m :=
begin
  cases n,
    simp,
  induction n with k ih generalizing m,
    simp,

  apply vector.to_list_injective,
  rw vector.to_list_tail,
  have : k.succ.succ - 1 = (k.succ - 1).succ,
    simp,
  rw this,
  rw bitvec.of_nat,
  symmetry,
  rw bitvec.of_nat,
  simp [vector.to_list_append],
  rw list.tail_append_of_ne_nil,
  rw ←vector.to_list_tail,
  congr,
  symmetry,
  exact ih,

  apply list.ne_nil_of_length_eq_succ,
  simp,
end

theorem to_nat_tail :
  bitvec.to_nat x.tail = x.to_nat % 2 ^ (n - 1) :=
begin
  rw ←bitvec.to_nat_of_nat,
  congr,
  rw ←tail_of_nat,
  congr,
  exact (bitvec.of_nat_to_nat x).symm,
end

lemma vector.map_accumr₂_cons {α β σ φ} (f : α → β → σ → σ × φ) (xr : vector α n) (yr : vector β n) (c : σ) (x : α) (y : β) :
  vector.map_accumr₂ f (x ::ᵥ xr) (y ::ᵥ yr) c = let r := vector.map_accumr₂ f xr yr c, q := f x y r.fst in (q.fst, q.snd ::ᵥ r.snd) :=
begin
  cases xr with xv xp,
  cases yr with yv yp,
  refl,
end

private lemma to_nat_cons' {xh : bool} :
  bitvec.to_nat (xh ::ᵥ x).reverse = bitvec.add_lsb (bitvec.to_nat x.reverse) xh :=
begin
  rw [bitvec.to_nat, vector.reverse],
  simp [bitvec.bits_to_nat],
  refl,
end

def bits_to_nat : list bool → ℕ
| [] := 0
| (b::l) := bits_to_nat l + cond b (2 ^ l.length) 0

lemma bits_to_nat'' (l : list bool) (b : bool) :
  bits_to_nat (l ++ [b]) = bitvec.add_lsb (bits_to_nat l) b :=
begin
  induction l with lh lt ih,
    refl,
  simp [bits_to_nat, ih, bitvec.add_lsb],
  cases lh,
    refl,
  simp [pow_add, mul_two],
  simp [add_assoc],
  rw ←add_assoc (2 ^ _),
  rw add_comm _ (bits_to_nat _),
  simp [add_assoc],
  rw add_comm,
  simp [add_assoc],
end

lemma bits_to_nat' (v : list bool) :
  bitvec.bits_to_nat v.reverse = bits_to_nat v.reverse :=
begin
  induction v with vh vt ih,
    refl,
  have : bits_to_nat (vh :: vt).reverse = bitvec.add_lsb (bitvec.bits_to_nat vt.reverse) vh,
    simp [bits_to_nat'', ih],
  rw this,
  simp [bitvec.bits_to_nat],
end

theorem bits_to_nat_is_bitvec (v : list bool) :
  bitvec.bits_to_nat v = bits_to_nat v :=
begin
  generalize h : v.reverse = w,
  have : v = w.reverse,
    simp [←h],
  rw this,
  exact bits_to_nat' w,
end

theorem to_nat_cons {xh : bool} :
  bitvec.to_nat (xh ::ᵥ x) = x.to_nat + cond xh (2 ^ n) 0 :=
begin
  simp [bitvec.to_nat, bits_to_nat_is_bitvec, bits_to_nat],
end

/-
def to_int : Π {n : ℕ}, bitvec n → ℤ
| 0     ⟨[],   _⟩ := 0
| (n+1) ⟨b::l, h⟩ := bits_to_nat l + cond b (-2 ^ l.length) 0

theorem to_int_cons {xh : bool} :
  bitvec.to_int (xh ::ᵥ x) = x.to_int + cond xh (-2 ^ n) 0 :=
begin
  sorry
end

-- def test' := ((x.sub y).to_nat, (x.sub y).to_int)
def test (x y : ℕ) := ((bitvec.of_nat 2 x - bitvec.of_nat 2 y).to_nat, (bitvec.of_nat 2 (x - y)).to_nat, x - y)
#reduce test 0 0
#reduce test 0 1
#reduce test 0 2
#reduce test 0 3
#reduce test 1 0
#reduce test 1 1
#reduce test 1 2
#reduce test 1 3
#reduce test 2 0
#reduce test 2 1
#reduce test 2 2
#reduce test 2 3
#reduce test 3 0
#reduce test 3 1
#reduce test 3 2
#reduce test 3 3
-/

theorem bitvec.adc_is_add :
  (x.adc y ff).to_nat = x.to_nat + y.to_nat :=
begin
  cases x with xv xp,
  cases y with yv yp,
  induction n with k ih generalizing xv yv,
    simp [list.length_eq_zero.mp xp, list.length_eq_zero.mp yp],
    refl,
  cases xv with xh xt,
    contradiction,
  cases yv with yh yt,
    contradiction,
  have xp' : xt.length = k,
    simp [nat.add_one] at xp,
    assumption,
  have yp' : yt.length = k,
    simp [nat.add_one] at yp,
    assumption,
  have ih' := ih xt yt xp' yp',
  have : xh ::ᵥ ⟨xt, xp'⟩ = ⟨xh :: xt, xp⟩,
    refl,
  rw ←this,
  have : yh ::ᵥ ⟨yt, yp'⟩ = ⟨yh :: yt, yp⟩,
    refl,
  rw ←this,

  simp [bitvec.adc, vector.map_accumr₂_cons],
  generalize h : bitvec.adc ⟨xt, xp'⟩ ⟨yt, yp'⟩ ff = t,
  rw h at ih',
  simp [bitvec.adc] at h,
  generalize h' : vector.map_accumr₂ (λ x y c, (bitvec.carry x y c, bitvec.xor3 x y c)) ⟨xt, xp'⟩ ⟨yt, yp'⟩ ff = t',
  rw h' at h,
  simp [to_nat_cons],
  cases t' with tl tr,

  simp [add_assoc],
  rw ←add_assoc (cond _ _ _),
  rw add_comm _ (bitvec.to_nat _),
  simp [add_assoc],
  rw ←add_assoc (bitvec.to_nat _) (bitvec.to_nat _),
  rw ←ih',
  rw ←h,
  simp [bitvec.adc._match_1, to_nat_cons, add_assoc],
  cases xh; cases yh; cases tl; simp [bitvec.carry, bitvec.xor3, ←nat.add_one, pow_add, nat.mul, mul_two],
end

/-
theorem bitvec.sbb_is_sub :
  (x.sbb' y ff).to_int = x.to_int - y.to_int :=
begin
  cases x with xv xp,
  cases y with yv yp,
  induction n with k ih generalizing xv yv,
    simp [list.length_eq_zero.mp xp, list.length_eq_zero.mp yp],
    refl,
  cases xv with xh xt,
    contradiction,
  cases yv with yh yt,
    contradiction,
  have xp' : xt.length = k,
    simp [nat.add_one] at xp,
    assumption,
  have yp' : yt.length = k,
    simp [nat.add_one] at yp,
    assumption,
  have ih' := ih xt yt xp' yp',
  have : xh ::ᵥ ⟨xt, xp'⟩ = ⟨xh :: xt, xp⟩,
    refl,
  rw ←this,
  have : yh ::ᵥ ⟨yt, yp'⟩ = ⟨yh :: yt, yp⟩,
    refl,
  rw ←this,

  simp [bitvec.sbb', bitvec.sbb, vector.map_accumr₂_cons],
  generalize h : bitvec.sbb' ⟨xt, xp'⟩ ⟨yt, yp'⟩ ff = t,
  rw h at ih',
  simp [bitvec.sbb', bitvec.sbb] at h,
  generalize h' : vector.map_accumr₂ (λ x y c, (bitvec.carry (!x) y c, bitvec.xor3 x y c)) ⟨xt, xp'⟩ ⟨yt, yp'⟩ ff = t',
  rw h' at h,
end
-/

theorem bitvec.add_is_add :
  x + y = bitvec.of_nat n (x.to_nat + y.to_nat) :=
begin
  have : x + y = x.add y := rfl, rw this,
  simp [bitvec.add],
  apply (bitvec.to_nat_inj _ _).mp,
  rw to_nat_tail,
  rw @bitvec.to_nat_of_nat n _,
  simp,
  congr,
  exact bitvec.adc_is_add _ _,
end


/-
theorem bitvec.sub_is_sub :
  x - y = bitvec.of_int' n (x.to_int - y.to_int) :=
begin
  sorry
end
-/

/-
def bitvec.checked_add : option (bitvec n)
  := let z := x.adc y ff in if z.head then none else some z.tail

def bitvec.checked_sub : option (bitvec n)
  := let z := x.sbb y ff in if z.fst then none else some z.snd

lemma checked_add_is_add :
  some z = x.checked_add y → z.to_nat = x.to_nat + y.to_nat :=
begin
  simp [bitvec.checked_add],
  generalize hw : x.adc y ff = w,
  cases w with wv wp,
  cases wv with wh wt,
    contradiction,
  cases wh; simp [vector.head, vector.tail],
  intro h,
  rw h,
  have := congr_arg bitvec.to_nat hw,
  simp [bitvec.adc_is_add] at this,
  rw this,
  have wp' : wt.length = n,
    simp at wp,
    assumption,
  have : ff ::ᵥ ⟨wt, wp'⟩ = ⟨ff :: wt, wp⟩,
    refl,
  simp [←this, to_nat_cons, bitvec.to_nat_inj],
end

/-
lemma checked_sub_is_sub :
  some z = x.checked_sub y → x.to_nat = y.to_nat + z.to_nat :=
begin
  sorry
end
-/

theorem bitvec.checked_add_is_add :
  some z = x.checked_add y ↔ z.to_nat = x.to_nat + y.to_nat :=
begin
  split,
    exact checked_add_is_add x y z,

  intro h,
  simp [bitvec.checked_add],
  generalize hw : x.adc y ff = w,
  cases w with wv wp,
  cases wv with wh wt,
    contradiction,
  have wp' : wt.length = n,
    simp at wp,
    assumption,
  cases wh; simp [vector.head, vector.tail],

  have : x.checked_add y = some ⟨wt, wp'⟩,
    simp [bitvec.checked_add, hw, vector.head, vector.tail],
  have := checked_add_is_add _ _ _ this.symm,
  rw ←h at this,
  rw bitvec.to_nat_inj at this,
  exact this.symm,

  have := congr_arg bitvec.to_nat hw,
  rw bitvec.adc_is_add at this,
  have hc : tt ::ᵥ ⟨wt, wp'⟩ = ⟨tt :: wt, wp⟩,
    refl,
  simp [←hc, to_nat_cons, ←h] at this,
  rw ←bitvec.mod_to_nat at this,
  have hp : 0 < 2 ^ n,
    induction n with n ih; simp,
  have hl := @nat.mod_lt z.to_nat (2 ^ n) hp,
  rw this at hl,
  simp at hl,
  contradiction,
end

/-
theorem bitvec.checked_sub_is_sub :
  some z = x.checked_sub y ↔ x.to_nat = y.to_nat + z.to_nat :=
begin
  sorry
end
-/

@[reducible] def u64 := bitvec 64
@[reducible] def u128 := bitvec 128
-/
