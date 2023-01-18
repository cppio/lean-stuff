import Bindgen.Types
import Lean.Parser.Command

open Lean

declare_syntax_cat cTypeAtom (behavior := symbol)

syntax "void" : cTypeAtom
syntax "char" : cTypeAtom
syntax "int" : cTypeAtom
syntax "int32_t" : cTypeAtom
syntax "double" : cTypeAtom

syntax cType_to_Type_mode := &"lean " <|> &"arg " <|> &"ret "

syntax "cTypeAtom_to_Type% " cType_to_Type_mode cTypeAtom : term

macro_rules
  | `(cTypeAtom_to_Type% lean void) => ``(Unit)
  | `(cTypeAtom_to_Type% arg void) => ``(Prop)
  | `(cTypeAtom_to_Type% ret void) => ``(USize)
  | `(cTypeAtom_to_Type% $_ char) => ``(UInt8)
  | `(cTypeAtom_to_Type% $_ int) => ``(UInt32)
  | `(cTypeAtom_to_Type% $_ int32_t) => ``(UInt32)
  | `(cTypeAtom_to_Type% $_ double) => ``(Float)

syntax "cTypeAtom_to_arg% " cTypeAtom term : term

macro_rules
  | `(cTypeAtom_to_arg% void $_) => ``(True)
  | `(cTypeAtom_to_arg% char $x) => ``($x)
  | `(cTypeAtom_to_arg% int $x) => ``($x)
  | `(cTypeAtom_to_arg% int32_t $x) => ``($x)
  | `(cTypeAtom_to_arg% double $x) => ``($x)

syntax "cTypeAtom_of_ret% " cTypeAtom term : term

macro_rules
  | `(cTypeAtom_of_ret% void $x) => ``(seq $x ())
  | `(cTypeAtom_of_ret% char $x) => ``($x)
  | `(cTypeAtom_of_ret% int $x) => ``($x)
  | `(cTypeAtom_of_ret% int32_t $x) => ``($x)
  | `(cTypeAtom_of_ret% double $x) => ``($x)

syntax cType := &"const "? cTypeAtom " *"?

macro "cType_to_Type% " mode:cType_to_Type_mode ty:cType : term =>
  match ty with
  | `(cType| $[const]? $ty) => ``(cTypeAtom_to_Type% $mode $ty)
  | `(cType| $[const]? $_ *) => ``(Pointer)
  | _ => throw .unsupportedSyntax

macro "cType_to_arg% " ty:cType x:term : term =>
  match ty with
  | `(cType| $[const]? $ty) => ``(cTypeAtom_to_arg% $ty $x)
  | `(cType| $[const]? $_ *) => ``($x)
  | _ => throw .unsupportedSyntax

macro "cType_of_ret% " ty:cType x:term : term =>
  match ty with
  | `(cType| $[const]? $ty) => ``(cTypeAtom_of_ret% $ty $x)
  | `(cType| $[const]? $_ *) => ``($x)
  | _ => throw .unsupportedSyntax

syntax safe := "safe "

open Parser

syntax (Command.visibility)? (safe)? "extern \"C\" {" ppIndent(ppLine cType ident "(" (cType (ident)?),+ ");")* ppLine "}" : command

macro_rules
  | `($[$vis]? $[$safety]? extern "C" { $[$rets $fns($[$argss $(namess)?],*);]* }) =>
    return mkNullNode <| ← (rets.zip <| fns.zip <| argss.zip namess).mapM λ (ret, fn, args, names) => do
      let names ← names.mapM λ | some name => return name | _ => withFreshMacroScope `(x)
      let extern := Syntax.mkStrLit fn.getId.toString
      let safety ← match safety with | none => pure <| some <| ← `(Command.unsafe| unsafe) | _ => pure none
      let imp := mkIdent <| ← Macro.addMacroScope fn.getId
      let impArgs ← (args.zip names).mapM λ (arg, name) => `(cType_to_arg% $arg $name)
      `(@[never_extract, extern $extern:str] private $[$safety:unsafe]? opaque $imp:ident $[($names : cType_to_Type% arg $args)]* : cType_to_Type% ret $ret
        @[always_inline] $(vis)? $[$safety:unsafe]? def $fn $[($names : cType_to_Type% lean $args)]* : cType_to_Type% lean $ret := cType_of_ret% $ret ($imp $impArgs*))

syntax (Command.visibility)? «safe» "opaque "declId declSig declVal : command

macro_rules
  | `($[$vis]? safe opaque $name:ident $bind* $ty:typeSpec $val) => do
    let imp := mkIdent <| ← Macro.addMacroScope <| name.getId.str "imp"
    `(private unsafe def $imp $bind* $ty:typeSpec $val
      @[implemented_by $imp] $(vis)? opaque $name $bind* $ty:typeSpec)
