structure ISigma {α : Type u} (β : α → Type v) where
  {fst : α}
  snd : β fst

open Lean

syntax implicitBinders := "{" withoutPosition((binderIdent ppSpace)+ (": " term)?) "}"

macro:35 xs:implicitBinders " × " body:term:35 : term => do
  let combinator := mkCIdentFrom (← getRef) ``ISigma
  let idents := xs.raw[1].getArgs
  let type? := xs.raw[2].getArgs[1]?
  return ⟨← expandExplicitBindersAux combinator idents type? body⟩
