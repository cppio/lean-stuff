attribute [local simp]
  Functor.map Seq.seq SeqLeft.seqLeft SeqRight.seqRight bind
  EStateM.map EStateM.seqRight EStateM.bind

instance : LawfulMonad (EStateM ε σ) where
  map_const := rfl
  id_map _ := by funext _; dsimp; apply Eq.symm; split <;> assumption
  seqLeft_eq _ _ := by funext _; dsimp; split <;> rfl
  seqRight_eq _ _ := by funext _; dsimp; split; split <;> assumption; rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := by
    funext _; dsimp; split
    next h => split at h; rw [h]; cases h
    next h => split at h; rw [h]; cases h; rfl

instance : LawfulMonad (EIO ε) := by unfold EIO; infer_instance

#synth LawfulMonad IO
