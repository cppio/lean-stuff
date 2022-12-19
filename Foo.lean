import Common.Meta
import Lean

attribute [local simp]
  Functor.map SeqLeft.seqLeft SeqRight.seqRight Seq.seq bind
  EStateM.map EStateM.seqRight EStateM.bind

instance : LawfulMonad (EStateM ε σ) where
  map_const := rfl
  id_map _ := by funext _; simp; split <;> simp [*]
  seqLeft_eq _ _ := by funext _; simp; split <;> rfl
  seqRight_eq _ _ := by funext _; simp; split; split <;> assumption; rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := by
    funext _; simp; split
    . split at *; simp [*]; contradiction
    . split at *; simp [*]; injections; simp [*]

instance : LawfulMonad (EIO ε) := instLawfulMonadEStateMInstMonadEStateM
