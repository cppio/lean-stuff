import Lean

open Lean

elab tk:"trace_env" command:command : command => do
  let before ← getEnv
  Elab.Command.elabCommand command
  let after ← getEnv

  logInfoAt tk <| flip .joinSep Format.line <| after.constants.toList.filter (!before.contains ·.fst) |>.map fun (n, ci) => m!"{n} : {ci.type}"

  let changed := before.extensions.zipWith after.extensions (unsafe ptrEq)
    |>.zipWithIndex.filterMap fun (eq, idx) =>
      if eq then none else some idx

  let persistentExts := (← persistentEnvExtensionsRef.get).foldl (init := mkRBMap Nat Name compare) fun exts ext =>
    exts.insert (unsafe cast lcProof ext.toEnvExtension : EnvExtensionInterfaceUnsafe.Ext (PersistentEnvExtensionState EnvExtensionEntry EnvExtensionState)).idx ext.name

  logInfoAt tk <| flip .joinSep Format.line <| Array.toList <| changed.map fun idx =>
    if let some name := persistentExts.find? idx then
      m!"{name}"
    else
      m!"{idx}"

trace_env
def List_id (xs : List α) : List α :=
  xs.casesOn [] (· :: List_id ·)

#print List_id
#print List_id._sunfold
#print List_id._unsafe_rec

#eval Meta.getEqnsFor? ``List_id
#eval Meta.getUnfoldEqnFor? ``List_id

#print List_id.eq_1
#print List_id.eq_def
