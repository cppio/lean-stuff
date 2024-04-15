import Common.Meta

opaque {
  def NatM : Type → Type := StateM Nat
  def NatM.run : NatM α → Nat → α × Nat := StateT.run
  unsafe def NatM.modifyGet : (Nat → α × Nat) → NatM α := StateT.modifyGet
  instance : Monad NatM
  instance : LawfulMonad NatM

  def NatM.inc : NatM Unit := modify (· + 1)
}

#eval (NatM.run · 30)
  for _ in [:12] do
    NatM.inc
