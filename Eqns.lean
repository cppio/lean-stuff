import Common.Meta

run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.Extension.addMatcherInfo env ``List.casesOn {
  numParams := 1
  numDiscrs := 1
  altNumParams := #[0, 2]
  uElimPos? := some 0
  discrInfos := #[{ hName? := none }]
}

noncomputable def List_id.{u} {α : Type u} (xs : List.{u} α) : List.{u} α :=
  @List.recOn.{u + 1, u} α (fun (_xs : List.{u} α) => List.{u} α) xs (@List.nil.{u} α) (fun (x : α) (_xs : List.{u} α) (List_id_xs : List.{u} α) => @List.cons.{u} α x List_id_xs)

noncomputable def List_id._sunfold.{u} {α : Type u} (xs : List.{u} α) : List.{u} α :=
  annotate% `sunfoldMatch
  @List.casesOn.{u + 1, u} α (fun (_xs : List.{u} α) => List.{u} α) xs (annotate% `sunfoldMatchAlt @List.nil.{u} α) (fun (x : α) (xs : List.{u} α) => annotate% `sunfoldMatchAlt @List.cons.{u} α x (@List_id.{u} α xs))

unsafe def List_id._unsafe_rec.{u} {α : Type u} (xs : List.{u} α) : List.{u} α :=
  @List.casesOn.{u + 1, u} α (fun (_xs : List.{u} α) => List.{u} α) xs (@List.nil.{u} α) (fun (x : α) (xs : List.{u} α) => @List.cons.{u} α x (@List_id._unsafe_rec α xs))

-- TODO: lazy

theorem List_id._eq_def.{u} {α : Type u} (xs : List.{u} α) : @List_id.{u} α xs = @List.casesOn.{u + 1, u} α (fun (_xs : List.{u} α) => List.{u} α) xs (@List.nil.{u} α) (fun (x : α) (xs : List.{u} α) => @List.cons.{u} α x (@List_id.{u} α xs)) :=
  @List.casesOn.{0, u} α (fun (xs : List.{u} α) => @List_id.{u} α xs = @List.casesOn.{u + 1, u} α (fun (_xs : List.{u} α) => List.{u} α) xs (@List.nil.{u} α) (fun (x : α) (xs : List.{u} α) => @List.cons.{u} α x (@List_id.{u} α xs))) xs (Eq.refl (@List.nil.{u} α)) (fun (x : α) (xs : List.{u} α) => Eq.refl (@List.cons.{u} α x (@List_id.{u} α xs)))

theorem List_id._eq_1.{u} {α : Type u} : @List_id.{u} α (@List.nil.{u} α) = @List.nil.{u} α := rfl
theorem List_id._eq_2.{u} {α : Type u} (x : α) (xs : List.{u} α) : @List_id.{u} α (@List.cons.{u} α x xs) = @List.cons.{u} α x (@List_id.{u} α xs) := rfl

run_elab
  let .thmInfo thm ← Lean.getConstInfo ``List_id._eq_def
    | throwError "not a theorem"
  Lean.addDecl <| .thmDecl { thm with
    name := `List_id.eq_def
    all := [`List_id.eq_def]
  }
  let .thmInfo thm ← Lean.getConstInfo ``List_id._eq_1
    | throwError "not a theorem"
  Lean.addDecl <| .thmDecl { thm with
    name := `List_id.eq_1
    all := [`List_id.eq_1]
  }
  let .thmInfo thm ← Lean.getConstInfo ``List_id._eq_2
    | throwError "not a theorem"
  Lean.addDecl <| .thmDecl { thm with
    name := `List_id.eq_2
    all := [`List_id.eq_2]
  }

#check List_id.eq_1
#check List_id.eq_2
#check List_id.eq_def

#eval List_id [1, 2, 3, 4]

example : List_id (x :: xs) = sorry := by rw [List_id]; sorry
example : List_id (x :: xs) = sorry := by unfold List_id; sorry
example : List_id (x :: xs) = sorry := by dsimp [List_id]; sorry
example : List_id (x :: xs) = sorry := by simp [List_id]; sorry
