import Lean

/-
syntax "level% " level : term
macro_rules
  | `(level% ($l)) => `(level% $l)
  | `(level% $i:ident) => `(Lean.Level.param $(Lean.quote i.getId))
  | `(level% $n:num) => `(Lean.Level.ofNat $n)
  | `(level% $l + $n) => `(Lean.Level.addOffset (level% $l) $n)
  | `(level% imax $l $l') => `(Lean.Level.imax (level% $l) (level% $l'))
-/

partial def elabLevel : Lean.TSyntax `level → Lean.CoreM Lean.Level
  | `(level| ($l)) => elabLevel l
  | `(level| $i:ident) => return .param i.getId
  | `(level| $n:num) => return .ofNat n.getNat
  | `(level| $l + $n) => return .addOffset (← elabLevel l) n.getNat
  | `(level| imax $l $l') => return .imax (←elabLevel l) (← elabLevel l')
  | _ => Lean.Elab.throwUnsupportedSyntax

partial def elabExpr : Lean.TSyntax `term → Lean.CoreM Lean.Expr
  | `(($t)) => elabExpr t
  | `($i:ident) => return .const i.getId []
  | `(@$i:ident) => return .const i.getId []
  | `($i:ident.{$l,*}) => return .const i.getId (← l.getElems.toList.mapM elabLevel)
  | `(@$i:ident.{$l,*}) => return .const i.getId (← l.getElems.toList.mapM elabLevel)
  | `(Sort $l) => return .sort (← elabLevel l)
  | `(Type $l) => return .sort (.succ (← elabLevel l))
  | `($t $ts*) => return Lean.mkAppN (← elabExpr t) (← ts.mapM elabExpr)
  | _ => Lean.Elab.throwUnsupportedSyntax

syntax "rdef " ident (".{" ident,+ "}")? " : " term " := " term : command

open Lean Elab Command in
elab_rules : command | `(rdef $name $[.{ $levelParams?,* }]? : $type := $value) => do
  let levelParams :=
    if let some levelParams := levelParams?
    then levelParams.getElems.toList.map (·.getId)
    else []
  liftCoreM <| addDecl <| .defnDecl {
    name := name.getId
    levelParams
    type := ← liftCoreM <| elabExpr type
    value := ← liftCoreM <| elabExpr value
    hints := .abbrev
    safety := .safe
  }

rdef bug.{u} : @Eq.{imax 1 u + 2} (Type (imax 1 u)) (Sort (imax 1 u)) (Type (imax 1 u)) := @rfl.{imax 1 u + 2} (Type (imax 1 u)) (Sort (imax 1 u))
