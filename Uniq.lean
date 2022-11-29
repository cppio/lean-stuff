def uniq [DecidableEq α] : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: l =>
    if x = y
    then uniq (y :: l)
    else x :: uniq (y :: l)

inductive List.Sublist : List α → List α → Prop
  | nil : Sublist [] []
  | cons x : Sublist l₁ l₂ → Sublist l₁ (x :: l₂)
  | cons₂ x : Sublist l₁ l₂ → Sublist (x :: l₁) (x :: l₂)

inductive List.Chain (r : α → α → Prop) : List α → Prop
  | nil : Chain r []
  | singleton x : Chain r [x]
  | cons : r x y → Chain r (y :: l) → Chain r (x :: y :: l)

theorem sublist_uniq [DecidableEq α] : (l : List α) → List.Sublist (uniq l) l
  | [] => .nil
  | [x] => .cons₂ x .nil
  | x :: y :: l => show List.Sublist (ite ..) _ from
    if h : x = y
    then if_pos h ▸ .cons x (sublist_uniq (y :: l))
    else if_neg h ▸ .cons₂ x (sublist_uniq (y :: l))

theorem chain_uniq [DecidableEq α] : (l : List α) → List.Chain Ne (uniq l)
  | [] => .nil
  | [x] => .singleton x
  | x :: y :: l => show List.Chain _ (ite ..) from
    if h : x = y
    then if_pos h ▸ chain_uniq (y :: l)
    else if_neg h ▸
      match l with
      | [] => .cons h (.singleton y)
      | z :: l => show List.Chain _ (x :: ite ..) from
        if h' : y = z
        then if_pos h' ▸ (have := if_neg (h <| .trans · h'.symm) ▸ show List.Chain _ (ite ..) from chain_uniq (x :: z :: l); by exact this)
        else if_neg h' ▸ .cons h (have := if_neg h' ▸ show List.Chain _ (ite ..) from chain_uniq (y :: z :: l); by exact this)

instance [BEq α] [LawfulBEq α] : DecidableEq α
  | x, y => if h : x == y then .isTrue (eq_of_beq h) else .isFalse (h <| · ▸ LawfulBEq.rfl)
