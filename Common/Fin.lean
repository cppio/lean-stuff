theorem cast_to_cast (h : x = x') (y : β x) : h ▸ y = cast (congrArg β h) y :=
  by cases h; rfl

theorem cast_app' {α : Sort u} {β : α → Sort v} (f : ∀ x, β x) {x x'} (h : x = x') : h ▸ f x = f x' :=
  by cases h; rfl

theorem cast_app {α : Sort u} {β : α → Sort v} {γ : α → Sort w} (f : ∀ x, β x → γ x) {x} (y : β x) {x'} (h : x = x') : h ▸ f x y = f x' (h ▸ y) :=
  by cases h; rfl

theorem cast_swap {α : Sort u} {β : α → Sort v} {x x'} (hx : x = x') {y : β x} {y' : β x'} (h : y = hx ▸ y') : hx ▸ y = y' :=
  by cases hx; cases h; rfl

@[simp]
theorem cast_cast {α : Sort u} (h : α = α') (h' : α' = α'') (x : α) : h' ▸ h ▸ x = h.trans h' ▸ x :=
  by cases h; rfl

@[simp]
theorem cast_cast' {α : Sort u} {β : α → Sort v} {x x' x'' : α} (h : x = x') (h' : x' = x'') (y : β x) : h' ▸ h ▸ y = h.trans h' ▸ y :=
  by cases h; rfl

theorem cast_app'' {α : Sort u} {β : α → Sort v} (f : ∀ x, β x) {x x'} (h : x = x') : congrArg β h ▸ f x = f x' :=
  by cases h; rfl

namespace Fin

def zero' : Fin (.succ n) := ⟨.zero, n.zero_lt_succ⟩
def last' : Fin (.succ n) := ⟨n, n.lt_succ_self⟩
def succ' (i : Fin n) : Fin n.succ := ⟨.succ i, Nat.succ_lt_succ i.2⟩
def castSucc' (i : Fin n) : Fin n.succ := ⟨i, .step i.2⟩

@[simp] theorem val_zero' : (@zero' n).1 = .zero := rfl
@[simp] theorem val_last' : (@last' n).1 = n := rfl
@[simp] theorem val_succ' (i : Fin n) : i.succ'.1 = .succ i := rfl
@[simp] theorem val_castSucc' (i : Fin n) : i.castSucc'.1 = i := rfl

def addL (i : Fin n) (m : Nat) : Fin (m + n) := ⟨.add i m, m.add_comm n ▸ Nat.add_lt_add_right i.2 m⟩
def addR (i : Fin n) (m : Nat) : Fin (n + m) := ⟨.add i m, Nat.add_lt_add_right i.2 m⟩
def castAdd' (i : Fin n) (m : Nat) : Fin (n + m) := ⟨i, Nat.le_trans i.2 <| n.le_add_right m⟩

@[simp] theorem val_addL (i : Fin n) m : (addL i m).1 = .add i m := rfl
@[simp] theorem val_addR (i : Fin n) m : (addR i m).1 = .add i m := rfl
@[simp] theorem val_castAdd' (i : Fin n) m : (castAdd' i m).1 = i := rfl

def lift (i : Fin n) (h : n ≤ m) : Fin m := ⟨.add i (m.sub n), (Nat.add_sub_of_le h ▸ Nat.add_lt_add_right i.2 (m.sub n) :)⟩
def castLe (i : Fin n) (h : n ≤ m) : Fin m := ⟨i, Nat.le_trans i.2 h⟩

@[simp] theorem val_lift (i : Fin n) (h : n ≤ m) : (lift i h).1 = .add i (m.sub n) := rfl
@[simp] theorem val_castLe (i : Fin n) (h : n ≤ m) : (castLe i h).1 = i := rfl

section

variable {i j : Fin n}

@[simp] theorem cast_eq_castLe (h : n = m) : h ▸ i = i.castLe (Nat.le_of_eq h) :=
  by cases h; rfl

@[simp] theorem val_ne : i.1 ≠ n := Nat.ne_of_lt i.2
@[simp] theorem ne_val : n ≠ i := val_ne.symm

@[simp] theorem eq_iff_val_eq : i = j ↔ i.1 = j.1 := ⟨val_eq_of_eq, eq_of_val_eq⟩

theorem succ'.inj : succ' i = succ' j → i = j := eq_of_val_eq ∘ Nat.succ.inj ∘ val_eq_of_eq
@[simp] theorem succ'.injIff : succ' i = succ' j ↔ i = j := ⟨inj, congrArg succ'⟩

@[simp] theorem succ'_ne_zero : succ' i ≠ zero' := Nat.succ_ne_zero _ ∘ val_eq_of_eq
@[simp] theorem zero_ne_succ' : zero' ≠ succ' i := succ'_ne_zero.symm

theorem castSucc.inj : castSucc i = castSucc j → i = j := eq_of_val_eq ∘ val_eq_of_eq
@[simp] theorem castSucc.injIff : castSucc i = castSucc j ↔ i = j := ⟨inj, congrArg castSucc⟩

@[simp] theorem castSucc_ne_last : castSucc i ≠ last' := val_ne (i := i) ∘ val_eq_of_eq
@[simp] theorem last_ne_castSucc : last' ≠ castSucc' i := castSucc_ne_last.symm

theorem addR.inj : addR i m = addR j m → i = j := eq_of_val_eq ∘ Nat.add_right_cancel ∘ val_eq_of_eq
@[simp] theorem addR.injIff : addR i m = addR j m ↔ i = j := ⟨inj, congrArg (addR · m)⟩

theorem castAdd.inj : castAdd' i m = castAdd' j m → i = j := eq_of_val_eq ∘ val_eq_of_eq
@[simp] theorem castAdd.injIff : castAdd' i m = castAdd' j m ↔ i = j := ⟨inj, congrArg (castAdd' · m)⟩

@[simp] theorem addR_zero : addR i 0 = i := rfl
@[simp] theorem castAdd_zero' : castAdd' i 0 = i := rfl

@[simp] theorem addR_one : addR i 1 = succ' i:= rfl
@[simp] theorem castAdd_one' : castAdd' i 1 = castSucc' i := rfl

@[simp] theorem lift_refl : lift i h = i := eq_of_val_eq <| congrArg i.1.add n.sub_self
@[simp] theorem castLe_refl : castLe i h = i := rfl

@[simp] theorem lift_add : lift i (h : n ≤ n.add k) = addR i k := eq_of_val_eq <| congrArg i.1.add <| n.add_sub_cancel_left k
@[simp] theorem castLe_add : castLe i (h : n ≤ n.add k) = castAdd' i k := rfl

@[simp] theorem succ'_succ' : succ' (succ' i) = addR i 2 := rfl
@[simp] theorem castSucc_castSucc : castSucc' (castSucc' i) = castAdd' i 2 := rfl

@[simp] theorem addR_addR : addR (addR i k) k' = lift i (Nat.le_trans (n.le_add_right k) <| (n.add k).le_add_right k') := eq_of_val_eq <| by dsimp; sorry
@[simp] theorem castAdd_castAdd : castAdd (castAdd i k) k' = castLe i (Nat.le_trans (n.le_add_right k) <| (n.add k).le_add_right k') := rfl

@[simp] theorem lift_lift {h : n ≤ m} {h' : m ≤ k} : lift (lift i h) h' = lift i (Nat.le_trans h h') := eq_of_val_eq <| by dsimp; sorry
@[simp] theorem castLe_castLe {h : n ≤ m} {h' : m ≤ k} : castLe (castLe i h) h' = castLe i (Nat.le_trans h h') := rfl

@[simp] theorem succ'_addR : succ' (addR i k) = addR i k.succ := rfl
@[simp] theorem addR_succ' : addR (succ' i) k = lift i (Nat.le_trans n.le_succ <| n.succ.le_add_right k) := eq_of_val_eq <| by dsimp; sorry

@[simp] theorem castSucc_castAdd : castSucc (castAdd i k) = castAdd i k.succ := rfl
@[simp] theorem castAdd_castSucc : castAdd (castSucc i) k = castLe i (Nat.le_trans n.le_succ <| n.succ.le_add_right k) := rfl

@[simp] theorem succ'_lift {h : n ≤ m} : succ' (lift i h) = lift i h.step := eq_of_val_eq <| by dsimp; sorry
@[simp] theorem lift_succ' {h : n.succ ≤ m} : lift (succ' i) h = lift i (Nat.le_of_succ_le h) := eq_of_val_eq <| by dsimp; sorry

@[simp] theorem castSucc_castLe {h : n ≤ m} : castSucc (castLe i h) = castLe i h.step := rfl
@[simp] theorem castLe_castSucc {h : n.succ ≤ m} : castLe (castSucc i) h = castLe i (Nat.le_of_succ_le h) := rfl

@[simp] theorem addR_lift {h : n ≤ m} : addR (lift i h) k = lift i (Nat.le_trans h <| m.le_add_right k) := eq_of_val_eq <| by dsimp; sorry
@[simp] theorem lift_addR {h : n.add k ≤ m} : lift (addR i k) h = lift i (Nat.le_trans (n.le_add_right k) h) := eq_of_val_eq <| by dsimp; sorry

@[simp] theorem castAdd_castLe {h : n ≤ m} : castAdd (castLe i h) k = castLe i (Nat.le_trans h <| m.le_add_right k) := rfl
@[simp] theorem castLe_castAdd {h : n.add k ≤ m} : castLe (castAdd i k) h = castLe i (Nat.le_trans (n.le_add_right k) h) := rfl

variable {h : n ≤ m}

theorem lift.inj : lift i h = lift j h → i = j := eq_of_val_eq ∘ Nat.add_right_cancel ∘ val_eq_of_eq
@[simp] theorem lift.injIff : lift i h = lift j h ↔ i = j := ⟨inj, congrArg (lift · h)⟩

theorem castLe.inj : castLe i h = castLe j h → i = j := eq_of_val_eq ∘ val_eq_of_eq
@[simp] theorem castLe.injIff : castLe i h = castLe j h ↔ i = j := ⟨inj, congrArg (castLe · h)⟩

variable {i : Fin n.succ}

@[simp] theorem succ'_last : succ' (@last n) = last := rfl
theorem eq_last_of_succ'_eq_last : succ' i = last → i = last := eq_of_val_eq ∘ Nat.succ.inj ∘ val_eq_of_eq
@[simp] theorem succ'_eq_last_iff_eq_last : succ' i = last ↔ i = last := ⟨eq_last_of_succ'_eq_last, congrArg succ'⟩
@[simp] theorem last_eq_succ'_iff_last_eq : last = succ' i ↔ last = i := ⟨.symm ∘ eq_last_of_succ'_eq_last ∘ .symm, congrArg succ'⟩

@[simp] theorem castSucc_zero : castSucc (@zero n) = zero := rfl
theorem eq_zero_of_castSucc_eq_zero : castSucc i = zero → i = zero := eq_of_val_eq ∘ val_eq_of_eq
@[simp] theorem castSucc_eq_zero_iff_eq_zero : castSucc i = zero ↔ i = zero := ⟨eq_zero_of_castSucc_eq_zero, congrArg castSucc⟩
@[simp] theorem zero_eq_castSucc_iff_zero_eq : zero = castSucc i ↔ zero = i := ⟨.symm ∘ eq_zero_of_castSucc_eq_zero ∘ .symm, congrArg castSucc⟩

end

def elim {α : Fin .zero → Sort u} i : α i := nomatch i

def cases' {α : Fin (.succ n) → Sort u} (zero : α zero') (succ : ∀ i, α (succ' i)) : ∀ i, α i
  | ⟨.zero, _⟩ => zero
  | ⟨.succ i, h⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ h⟩

def rcases {α : Fin (.succ n) → Sort u} (castSucc : ∀ i, α (castSucc' i)) (last : α last') i : α i :=
  if h : i = _
  then h ▸ last
  else castSucc ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.2) (h <| eq_of_val_eq ·)⟩

@[simp] theorem cases_zero' zero succ : @cases n α zero succ .zero' = zero := rfl
@[simp] theorem cases'_succ' zero succ i : @cases n α zero succ i.succ' = succ i := rfl
@[simp] theorem rcases_last' castSucc last : @rcases n α castSucc last .last' = last := dif_pos rfl
@[simp] theorem rcases_castSucc' castSucc last i : @rcases n α castSucc last i.castSucc' = castSucc i := dif_neg castSucc_ne_last

@[simp] theorem cases_zero_succ xs : @cases n α (xs zero) (xs ·.succ') = xs := funext <| cases rfl λ _ => rfl
@[simp] theorem rcases_castSucc_last xs : @rcases n α (xs ·.castSucc) (xs last) = xs := funext <| rcases (rcases_castSucc _ _) (rcases_last ..)

def append {α : Fin (.add n m) → Sort u} (xs : ∀ i, α (castAdd i m)) (ys : ∀ i, α (addL i n)) i : α i :=
  if h : i < n
  then xs ⟨i, h⟩
  else (Fin.eq_of_val_eq <| Nat.sub_add_cancel <| Nat.ge_of_not_lt h : addL ⟨_, _⟩ n = i) ▸ ys ⟨i - n, Nat.succ_sub (Nat.ge_of_not_lt h) ▸ Nat.sub_le_of_le_add <| n.add_comm m ▸ i.2⟩

@[simp] theorem append_castAdd xs ys i : @append n m α xs ys (castAdd i m) = xs i := dif_pos i.2
@[simp] theorem append_addL xs ys i : @append n m α xs ys (addL i n) = ys i := by
  apply dif_neg (λ h : (i + n).succ ≤ n => nomatch Nat.le_of_add_le_add_right (i.1.succ_add n ▸ n.zero_add.symm ▸ h : i.succ + n ≤ .zero + n)) |>.trans
  rw [cast_to_cast, ← cast_to_cast (β := (α <| addL · n))]
  apply cast_app'
  simp [addL, Nat.add_sub_cancel]

theorem append_cases {α} x xs ys : @append n.succ m α (@cases n _ x xs) ys i = @cases (.add n m) (λ i => α <| i.castLe <| Nat.le_of_eq <| .symm <| n.succ_add m) x (append xs ys) (i.castLe <| Nat.le_of_eq <| n.succ_add m) := by
  let i' := i.castLe (m := .succ (n.add m)) (Nat.le_of_eq <| n.succ_add m)
  have : i = i'.castLe (m := n.succ.add m) (Nat.le_of_eq <| .symm <| n.succ_add m) := rfl
  generalize i' = j at this
  clear i'
  cases this
  dsimp
  cases j using Fin.cases with
  | zero =>
    show append _ _ _ = x
    simp
  | succ j =>
    dsimp [append]
    split
    next h =>
      simp [Nat.lt_of_succ_lt_succ h]
      rfl
    next h =>
      simp [show ¬_ < _ from h ∘ Nat.succ_lt_succ]

      rw [@cast_to_cast _ (addL ..) j (λ i => α <| i.succ'.castLe <| Nat.le_of_eq <| .symm <| n.succ_add m)]
      rw [← @cast_to_cast (Fin _) ⟨j - n + n.succ, _⟩ ⟨.succ j, _⟩ _ <| by simp [Nat.add_succ, Nat.sub_add_cancel <| Nat.ge_of_not_lt (h ∘ Nat.succ_lt_succ)]]
      rw [cast_to_cast]
      rw [← @cast_to_cast (Fin _) ⟨.succ j - n.succ + n.succ, _⟩ ⟨.succ j, _⟩ _ <| by simp [Nat.sub_add_cancel <| Nat.ge_of_not_lt h]]

      have := @cast_app'' _ _ ys ⟨.succ j - n.succ, sorry⟩ ⟨j - n, sorry⟩ sorry

      dsimp
      dsimp only [HAdd.hAdd, Add.add, HSub.hSub, Sub.sub, LT.lt, LE.le, Nat.lt] at h ⊢
      set_option pp.explicit true in trace_state
      apply Eq.symm
      simp
      have h := Nat.le_of_succ_le_succ <| Nat.ge_of_not_lt h
      have ⟨j', h⟩ : ∃ j' : Fin m, j'.addL n = j := ⟨⟨j - n, Nat.succ_sub h ▸ Nat.sub_le_of_le_add <| n.add_comm m ▸ j.2⟩, Fin.eq_of_val_eq <| Nat.sub_add_cancel h⟩
      cases h
      clear h
      dsimp
      rw [cast_to_cast]
      sorry

@[simp]
def dfoldr {α : Fin n → Sort u} {β : Fin n.succ → Sort v} (f : ∀ i, α i → β i.succ' → β i.castSucc) (y : β last) (xs : ∀ i, α i) : β zero :=
  match n with
  | .zero => y
  | .succ n => f _ (xs _) (@dfoldr n _ (β ·.succ') (f ·.succ') y (xs ·.succ'))

@[simp]
def rdfoldr {α : Fin n → Sort u} {β : Fin n.succ → Sort v} (f : ∀ i, α i → β i.succ' → β i.castSucc) (y : β last) (xs : ∀ i, α i) : β zero :=
  match n with
  | .zero => y
  | .succ n => @rdfoldr n _ (β ·.castSucc) (f ·.castSucc) (f _ (xs _) y) (xs ·.castSucc)

@[simp]
def dfoldl {α : Fin n → Sort u} {β : Fin n.succ → Sort v} (f : ∀ i, β i.castSucc → α i → β i.succ') (y : β zero) (xs : ∀ i, α i) : β last :=
  match n with
  | .zero => y
  | .succ n => @dfoldl n _ (β ·.succ') (f ·.succ') (f _ y (xs _)) (xs ·.succ')

@[simp]
def rdfoldl {α : Fin n → Sort u} {β : Fin n.succ → Sort v} (f : ∀ i, β i.castSucc → α i → β i.succ') (y : β zero) (xs : ∀ i, α i) : β last :=
  match n with
  | .zero => y
  | .succ n => f _ (@rdfoldl n _ (β ·.castSucc) (f ·.castSucc) y (xs ·.castSucc)) (xs _)

private theorem dfoldr_eq_rdfoldr' {α : Fin _ → Sort u} {β : Fin _ → Sort v} f y xs : @rdfoldr (.succ n) α β f y xs = f _ (xs _) (@rdfoldr n _ (β ·.succ') (f ·.succ') y (xs ·.succ')) := by
  induction n with
  | zero => rfl
  | succ _ hn => exact @hn _ (β ·.castSucc) (f ·.castSucc) _ (xs ·.castSucc)

theorem dfoldr_eq_rdfoldr {α : Fin n → Sort u} {β : Fin _ → Sort v} f y xs : @dfoldr n α β f y xs = @rdfoldr n α β f y xs := by
  induction n with
  | zero => rfl
  | succ _ hn => rw [dfoldr_eq_rdfoldr']; exact congrArg (f _ _) (hn ..)

private theorem dfoldl_eq_rdfoldl' {α : Fin _ → Sort u} {β : Fin _ → Sort v} f y xs : @dfoldl (.succ n) α β f y xs = f _ (@dfoldl n _ (β ·.castSucc) (f ·.castSucc) y (xs ·.castSucc)) (xs _) := by
  induction n with
  | zero => rfl
  | succ _ hn => exact @hn _ (β ·.succ') (f ·.succ') _ (xs ·.succ')

theorem dfoldl_eq_rdfoldl {α : Fin n → Sort u} {β : Fin _ → Sort v} f y xs : @dfoldl n α β f y xs = @rdfoldl n α β f y xs := by
  induction n with
  | zero => rfl
  | succ _ hn => rw [dfoldl_eq_rdfoldl']; exact congrArg (f _ · _) (hn ..)

theorem dfoldr_ext {α : Fin n → Sort u}
  {β β' : Fin _ → Sort v} (hβ : ∀ i, β i = β' i)
  {f f'} (hf : ∀ i x y, f i x (hβ _ ▸ y) = hβ _ ▸ f' i x y)
  {y y'} (hy : y = hβ _ ▸ y')
xs : @dfoldr n α β f y xs = hβ _ ▸ @dfoldr n α β' f' y' xs := by
  induction n with
  | zero => exact hy
  | succ _ hn => exact hn (hβ ·.succ') (hf ·.succ') hy _ |> congrArg (f _ _) |>.trans <| hf ..

theorem rdfoldr_ext {α : Fin n → Sort u}
  {β β' : Fin _ → Sort v} (hβ : ∀ i, β i = β' i)
  {f f'} (hf : ∀ i x y, f i x (hβ _ ▸ y) = hβ _ ▸ f' i x y)
  {y y'} (hy : y = hβ _ ▸ y')
xs : @rdfoldr n α β f y xs = hβ _ ▸ @rdfoldr n α β' f' y' xs :=
  dfoldr_eq_rdfoldr .. ▸ dfoldr_eq_rdfoldr .. ▸ dfoldr_ext hβ hf hy _

theorem rdfoldl_ext {α : Fin n → Sort u}
  {β β' : Fin _ → Sort v} (hβ : ∀ i, β i = β' i)
  {f f'} (hf : ∀ i y x, f i (hβ _ ▸ y) x = hβ _ ▸ f' i y x)
  {y y'} (hy : y = hβ _ ▸ y')
xs : @rdfoldl n α β f y xs = hβ _ ▸ @rdfoldl n α β' f' y' xs := by
  induction n with
  | zero => exact hy
  | succ n hn => exact hn (hβ ·.castSucc) (hf ·.castSucc) hy _ |> congrArg (f _ · _) |>.trans <| hf ..

theorem dfoldl_ext {α : Fin n → Sort u}
  {β β' : Fin _ → Sort v} (hβ : ∀ i, β i = β' i)
  {f f'} (hf : ∀ i y x, f i (hβ _ ▸ y) x = hβ _ ▸ f' i y x)
  {y y'} (hy : y = hβ _ ▸ y')
xs : @dfoldl n α β f y xs = hβ _ ▸ @dfoldl n α β' f' y' xs :=
  (dfoldl_eq_rdfoldl ..).symm ▸ (dfoldl_eq_rdfoldl ..).symm ▸ rdfoldl_ext hβ hf hy _

variable {motive : ∀ n, Fin n → Sort u} (zero : ∀ {n}, motive (.succ n) zero) (succ : ∀ {n} i, motive n i → motive n.succ i.succ') in
def recL : ∀ {n} i, motive n i
  | .succ _, ⟨.zero, _⟩ => zero
  | .succ _, ⟨.succ i, h⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ (recL _)

variable {motive : ∀ n, Fin n → Sort u} (castSucc : ∀ {n} i, motive n i → motive n.succ i.castSucc) (last : ∀ {n}, motive (.succ n) last) in
def recR : ∀ {n} i, motive n i
  | .succ _, i =>
    if h : i = _
    then h ▸ last
    else castSucc ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.2) (h <| eq_of_val_eq ·)⟩ (recR _)

@[simp] theorem recL_zero zero succ : @recL motive @zero succ (.succ n) .zero = zero := rfl
@[simp] theorem recL_succ' zero succ i : @recL motive @zero succ (.succ n) (.succ' i) = succ i (@recL motive @zero @succ n i) := rfl
@[simp] theorem recR_last castSucc last : @recR motive castSucc @last (.succ n) .last = last := dif_pos rfl
@[simp] theorem recR_castSucc castSucc last i : @recR motive castSucc last (.succ n) (.castSucc i) = castSucc i (@recR @motive @castSucc @last n i) := dif_neg castSucc_ne_last
