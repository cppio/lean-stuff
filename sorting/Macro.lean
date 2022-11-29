import Lean

#check do
  let mut i := 1
  for _ in Lean.Loop.mk with h : 0 < i := Nat.lt_succ_self 0 do
    if i ≥ 10 then
      break
    else
      IO.println i
      i := i + 1
      --have := by exact Nat.le_step h
      continue
  --have _ : 0 < i := h
  IO.println i

open Lean

partial def getVars (stx : Syntax) : MacroM (List Ident) :=
  let rec visit : Syntax → StateT (List Ident) MacroM Unit
    | stx@(.ident _ _ _ _) => modify (⟨stx⟩ :: ·)
    | .node _ _ args => args.forM visit
    | _ => return ()
  return (← visit stx []).2

partial def replaceVar (before : Ident) (after : Syntax) : Syntax → Syntax
  | stx@(.ident _ _ _ _) => if stx == before then after else stx
  | .node info kind args => .node info kind <| args.map <| replaceVar before after
  | stx => stx

def getDoSeqElems (doSeq : Syntax) : Array Syntax :=
  if doSeq.getKind == ``Parser.Term.doSeqBracketed then
    doSeq[1].getArgs.map (·[0])
  else if doSeq.getKind == ``Parser.Term.doSeqIndent then
    doSeq[0].getArgs.map (·[0])
  else
    #[]

def mkDoSeq' (doElems : Array (MacroM Syntax)) : MacroM Syntax :=
  return Lean.Elab.Term.Do.mkDoSeq (← doElems.mapM id)

partial def insertBeforeContinue (el : Syntax) : Syntax → MacroM Syntax
  | stx@(.node info kind args) =>
    if kind == ``Lean.Parser.Term.doContinue
    then `(doElem| do $(⟨Lean.Elab.Term.Do.mkDoSeq #[el, stx]⟩))
    else return .node info kind (← args.mapM (insertBeforeContinue el))
  | stx => return stx

syntax "for " Parser.Term.doForDecl,+ "with " ident " : " term " := " term "; do " doSeq : doElem
macro_rules | `(doElem| for $i in $e with $h : $t := $v; do $s) => do
  let [x] := ← getVars t
    | Macro.throwUnsupported
  let s := getDoSeqElems (replaceVar x (← `(x)) s)
  let t' := replaceVar x (← `(x)) t

  let s ← s.mapM <| insertBeforeContinue <| ← `(doElem| h := ⟨x, by assumption⟩)

  let s := s.insertAt 0 <| ← `(doElem| let $h : $(⟨t'⟩) := h.2)
  let s := s.insertAt 0 <| ← `(doElem| let mut x := h.1)

  let s : TSyntax `Lean.Parser.Term.doSeq := ⟨Lean.Elab.Term.Do.mkDoSeq s⟩

  let seq := ⟨← mkDoSeq' #[
    `(doElem| let mut h : { $x // $t } := ⟨$x, $v⟩),
    `(doElem| for $i in $e do $s),
    --`(doElem| $x := h.1)
    return .node1 .none ``Lean.Parser.Term.doReassign <| .node5 .none ``Lean.Parser.Term.letIdDecl x mkNullNode mkNullNode mkNullNode (← `(h.1)),
    `(doElem| let $h : $t := h.2)
  ]⟩
  `(doElem| do $seq)

#check do
  let mut i := 1
  for _ in Lean.Loop.mk with h : 0 < i := Nat.lt_succ_self 0; do
    if i ≥ 10 then
      break
    else
      IO.println i
      i := i + 1
      have := by exact Nat.le_step h
      continue
  have _ : 0 < i := h
  IO.println i
