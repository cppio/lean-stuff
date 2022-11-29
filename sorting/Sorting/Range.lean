structure Range where
  start : Nat
  len : Nat
  dir : Bool

notation "(" start " ..< " stop ")" => Range.mk start (stop - start) false
notation "(" start " ..≤ " stop ")" => Range.mk start (stop + 1 - start) false

notation "(" start " ..> " stop ")" => Range.mk (stop + 1) (start - stop) true
notation "(" start " ..≥ " stop ")" => Range.mk stop (start + 1 - stop) true

def Range.rev (range : Range) : Range :=
  { range with dir := !range.dir }

instance : Membership Nat Range where
  mem n range := range.start ≤ n ∧ n < range.len + range.start

instance : ForIn m Range Nat where
  forIn range b f :=
    let rec forward b i
      | 0 => return b
      | l + 1 => do
        match ← f i b with
        | .done b => return b
        | .yield b => forward b (i + 1) l
    let rec reverse b i
      | 0 => return b
      | l + 1 => do
        match ← f (i + l) b with
        | .done b => return b
        | .yield b => reverse b i l
    match range.dir with
    | false => forward b range.start range.len
    | true => reverse b range.start range.len

instance : ForIn' m Range Nat inferInstance where
  forIn' range b f :=
    let rec forward b i : ∀ l, range.start ≤ i ∧ i + l ≤ range.len + range.start → _
      | 0, _ => return b
      | l + 1, h => do
        match ← f i ⟨h.1, Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ _)) h.2⟩ b with
        | .done b => return b
        | .yield b => forward b (i + 1) l ⟨h.1.step, Nat.add_assoc i 1 l ▸ Nat.add_comm 1 l ▸ h.2⟩
    let rec reverse b : ∀ l, l ≤ range.len → _
      | 0, _ => return b
      | l + 1, h => do
        match ← f (l + range.start) ⟨Nat.le_add_left _ l, Nat.add_lt_add_right h _⟩ b with
        | .done b => return b
        | .yield b => reverse b l (Nat.pred_le_pred h.step)
    match range.dir with
    | false => forward b range.start range.len ⟨.refl, Nat.add_comm _ _ ▸ .refl⟩
    | true => reverse b range.len .refl
