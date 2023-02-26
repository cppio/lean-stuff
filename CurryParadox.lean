unsafe inductive Curry (α : Sort u)
  | mk : (Curry α → α) → Curry α

noncomputable section

unsafe def Curry.get {α : Sort u} (c : Curry α) : α :=
  rec (· c) c

unsafe def inhabit {α : Sort u} : α :=
  Curry.get ⟨Curry.get⟩

end
