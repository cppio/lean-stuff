instance : LawfulFunctor Option where
  map_const := rfl
  id_map
    | none => rfl
    | some _ => rfl
  comp_map _ _
    | none => rfl
    | some _ => rfl

instance : LawfulApplicative Option where
  seqLeft_eq
    | none, _ => rfl
    | some _, none => rfl
    | some _, some _ => rfl
  seqRight_eq
    | none, _ => rfl
    | some _, none => rfl
    | some _, some _ => rfl
  pure_seq _ _ := rfl
  map_pure _ _ := rfl
  seq_pure
    | none, _ => rfl
    | some _, _ => rfl
  seq_assoc
    | _, _, none => rfl
    | _, none, some _ => rfl
    | none, some _, some _ => rfl
    | some _, some _, some _ => rfl

instance : LawfulMonad Option where
  bind_pure_comp _
    | none => rfl
    | some _ => rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc
    | none, _, _ => rfl
    | some _, _, _ => rfl

