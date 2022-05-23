import data.bitvec.basic

@[simp]
def list.skip {α} : ℕ → list α → list α
| 0       l        := l
| (_ + 1) []       := []
| (n + 1) (_ :: l) := list.skip n l

@[simp]
theorem list.length_skip {α} : ∀ n l, (@list.skip α n l).length = l.length - n
| 0 _ := rfl
| (_ + 1) [] := (nat.zero_sub _).symm
| (_ + 1) (_ :: l) := (list.length_skip _ l).trans (nat.succ_sub_succ _ _).symm

@[simp]
theorem list.take_append_skip {α} : ∀ n l, @list.take α n l ++ list.skip n l = l
| 0 _ := rfl
| (_ + 1) [] := rfl
| (_ + 1) (_ :: _) := congr_arg (list.cons _) (list.take_append_skip _ _)

def vector.skip {α n} (i) : vector α n → vector α (n - i)
| ⟨l, p⟩ := ⟨list.skip i l, p ▸ list.length_skip _ _⟩

namespace rust

@[derive decidable_eq]
structure u (n : ℕ) := (val : bitvec n)

instance {n} : has_repr (u n) := ⟨repr ∘ bitvec.to_nat ∘ u.val⟩

instance {n} : has_zero (u n) := ⟨⟨0⟩⟩

def u.checked_add {n} (x y : u n) : option (u n) :=
  let z := x.val.adc y.val ff in
    if z.head
    then none
    else some ⟨z.tail⟩

def u.checked_sub {n} (x y : u n) : option (u n) :=
  let z := x.val.sbb y.val ff in
    if z.fst
    then none
    else some ⟨z.snd⟩

def u.checked_mul {n} (x y : u n) : option (u n) :=
  let z := (bitvec.zero n).append x.val * (bitvec.zero n).append y.val in
    if z.take n = bitvec.zero _
    then some ⟨cast (congr_arg _ (nat.add_sub_cancel _ _)) (z.skip n)⟩
    else none

abbreviation u64 := u 64
abbreviation u128 := u 128

end rust
