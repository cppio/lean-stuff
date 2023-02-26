import Lean

def List.findIdx? (p : α → Bool) : List α → (start : Nat := 0) → Option Nat
| [], _ => none
| a :: l, i => if p a then some i else findIdx? p l (i + 1)

def List.indexOf? [BEq α] (a : α) : List α → Option Nat := findIdx? (a == ·)

open Lean

partial def parseLevel : Syntax.Level → Option Level
  | `(level| ($l)) => parseLevel l
  | `(level| max $l $ls*) => return (← ls.mapM parseLevel).foldr .max <| ← parseLevel l
  | `(level| imax $l $ls*) => return (← ls.mapM parseLevel).foldr .imax <| ← parseLevel l
  | `(level| $n:num) => return .addOffset .zero n.getNat
  | `(level| $i:ident) => return .param i.getId
  | `(level| $l + $n) => return (← parseLevel l).addOffset n.getNat
  | _ => none

partial def parseTerm (bs : List Name) : Syntax.Term → Option Expr
  | `(term| ($t)) => parseTerm bs t
  | `(term| $i:ident) => return match bs.indexOf? i.getId with | some b => .bvar b | _ => .const i.getId []
  | `(term| $i:ident.{$l,*}) => return .const i.getId <| ← l.getElems.toList.mapM parseLevel
  | `(term| $f $a*) => return (← a.mapM (parseTerm bs)).foldl .app <| ← parseTerm bs f
  | `(term| Prop) => return .sort .zero
  | `(term| Sort) => return .sort .zero
  | `(term| Sort $u) => return .sort <| ← parseLevel u
  | `(term| Type) => return .sort <| .succ .zero
  | `(term| Type $u) => return .sort <| .succ <| ← parseLevel u
  | `(term| $l → $r) => return .forallE .anonymous (← parseTerm bs l) (← parseTerm (.anonymous :: bs) r) .default
  | `(term| ($i:ident : $l) → $r) => return .forallE i.getId (← parseTerm bs l) (← parseTerm (i.getId :: bs) r) .default
  | `(term| {$i:ident : $l} → $r) => return .forallE i.getId (← parseTerm bs l) (← parseTerm (i.getId :: bs) r) .implicit
  | `(term| fun (_ : $t) => $b) => return .lam .anonymous (← parseTerm bs t) (← parseTerm (.anonymous :: bs) b) .default
  | `(term| fun ($i:ident : $t) => $b) => return .lam i.getId (← parseTerm bs t) (← parseTerm (i.getId :: bs) b) .default
  | `(term| fun {$i:ident : $t} => $b) => return .lam i.getId (← parseTerm bs t) (← parseTerm (i.getId :: bs) b) .implicit
  | `(term| ($e : $t:ident).$n:fieldIdx) => return .proj t.getId n.raw.isFieldIdx?.get!.pred (← parseTerm bs e)
  | _ => none

elab tk:"#parse " t:term : command =>
  logInfoAt tk (parseTerm [] t)

open Elab

syntax "#def " ident (".{" ident,+ "}")? " : " term " := " term : command

elab_rules : command
  | `(#def $n $[.{$ls,*}]? : $t := $v) => Command.liftTermElabM do
    let name := n.getId
    let levelParams :=
      match ls with
      | some ls => ls.getElems.map Syntax.getId |>.toList
      | _ => []
    let some type := parseTerm [] t
      | throwUnsupportedSyntax
    let some value := parseTerm [] v
      | throwUnsupportedSyntax
    addAndCompile <| .defnDecl {
      name
      levelParams
      type
      value
      hints := .abbrev
      safety := .safe
    }
