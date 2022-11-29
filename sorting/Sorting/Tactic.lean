import Lean

open Lean

syntax "replace " ident (" : " term)? " := " term : tactic

macro_rules
  | `(tactic| replace $i $[: $t]? := $v) =>
    `(tactic| have $[: $t]? := $v; clear $i; rename _ => $i)

syntax "split " "with " binderIdent : tactic

macro_rules
  | `(tactic| split with $i) =>
    `(tactic| split <;> rename_i $i)
