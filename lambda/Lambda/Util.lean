import Lean.Elab.Notation

open Lean Parser

private def tempKind : SyntaxNodeKind := decl_name%

private def usingNotationFn (f : ParserFn) : ParserFn | c, s => Id.run do
  let prec := s.stxStack.get! 4 |>.toNat
  let items := s.stxStack.get! 5 |>.getArgs.map fun item =>
    match item.isStrLit? with
    | some sym => Sum.inl sym
    | none => Sum.inr item[2].toNat
  let itemParser
    | .inl sym => sym
    | .inr prec => termParser prec
  let some item := items[0]?
    | s.mkErrorAt "notation item" (s.stxStack.get! 6 |>.getPos?.getD s.pos)
  let (leading, parser) ←
    if let .inr lhsPrec := item then
      let some item := items[1]?
        | return s.mkErrorAt "notation item" (s.stxStack.get! 6 |>.getPos?.getD s.pos)
      (false, trailingNode tempKind prec lhsPrec <| items.foldl (· >> itemParser ·) (itemParser item) 2)
    else
      (true, leadingNode tempKind prec <| items.foldl (· >> itemParser ·) (itemParser item) 1)
  adaptUncacheableContextFn (fun c => { c with
    tokens := (parser.info.collectTokens []).foldl (fun tokens token => tokens.insert token token) c.tokens
    env := parserExtension.addEntry c.env <| .parser `term .anonymous leading parser (eval_prio default)
  }) f c s

private def usingMixfixFn (f : ParserFn) : ParserFn | c, s => Id.run do
  let kind := s.stxStack.get! 2
  let prec := s.stxStack.get! 4 |>.toNat
  let sym := s.stxStack.get! 5 |>.isStrLit?.getD ""
  let (leading, parser) :=
    match kind with
    | `(Command.mixfixKind| prefix) => (true, leadingNode tempKind prec (sym >> termParser prec))
    | `(Command.mixfixKind| infix) => (false, trailingNode tempKind prec (prec + 1) (sym >> termParser (prec + 1)))
    | `(Command.mixfixKind| infixl) => (false, trailingNode tempKind prec prec (sym >> termParser (prec + 1)))
    | `(Command.mixfixKind| infixr) => (false, trailingNode tempKind prec (prec + 1) (sym >> termParser prec))
    | `(Command.mixfixKind| postfix) => (false, trailingNode tempKind prec prec (sym))
    | _ => unreachable!
  adaptUncacheableContextFn (fun c => { c with
    tokens := (parser.info.collectTokens []).foldl (fun tokens token => tokens.insert token token) c.tokens
    env := parserExtension.addEntry c.env <| .parser `term .anonymous leading parser (eval_prio default)
  }) f c s

@[command_parser]
def usingNotation : Parser := leading_parser
  "using" >> Term.attrKind >> "notation" >> ":" >> numLitNoAntiquot
    >> manyNoAntiquot (strLitNoAntiquot <|> identNoAntiquot >> ":" >> numLitNoAntiquot)
    >> darrow >> termParser >> withFn usingNotationFn commandParser

@[command_parser]
def usingMixfix : Parser := leading_parser
  "using" >> Term.attrKind >> Command.mixfixKind >> ":" >> numLitNoAntiquot
    >> strLitNoAntiquot
    >> darrow >> termParser >> withFn usingMixfixFn commandParser

private partial def antiquote (vars : Array Name) : Syntax → Syntax
  | stx@(.ident _ _ id _) => if vars.any (· == id) then Syntax.mkAntiquotNode `term stx (isPseudoKind := true) else stx
  | .node i k args => .node i k (args.map (antiquote vars))
  | stx => stx

open Elab Command

@[command_elab usingNotation]
private def usingNotationElab : CommandElab | stx => do
  let attrKind : TSyntax ``Term.attrKind := ⟨stx[1]⟩
  let prec : NumLit := ⟨stx[4]⟩
  let items ← stx[5] |>.getArgs.mapM fun item =>
    if item.isOfKind strLitKind
    then `(Command.notationItem| $(⟨item⟩):str)
    else `(Command.notationItem| $(⟨item[0]⟩):ident:$(⟨item[2]⟩))
  let rhs : Term := ⟨stx[7]⟩
  let cmd : Command := ⟨stx[8]⟩

  let vars := stx[5] |>.getArgs.filterMap fun item =>
    if item.isOfKind strLitKind
    then none
    else item[0].getId
  let macroLHS := ⟨mkNode tempKind <| ← liftMacroM <| items.mapM expandNotationItemIntoPattern⟩
  let macroRHS := ⟨antiquote vars rhs⟩

  modifyEnv fun env =>
    let env := parserExtension.addLocalEntry (parserExtension.pushScope env) (.kind tempKind)
    macroAttribute.ext.pushScope env
  withScope (fun scope => { scope with opts := scope.opts.setBool `hygiene false }) do
    elabCommand <| ← `(local macro_rules | `($macroLHS) => `($macroRHS))
  modifyEnv parserExtension.popScope
  elabCommand cmd
  modifyEnv macroAttribute.ext.popScope
  elabCommand <| ← `($attrKind:attrKind notation:$prec $items:notationItem* => $rhs)

@[macro usingMixfix]
private def usingMixfixMacro : Macro | stx => do
  let kind := stx[2]
  let prec := stx[4]
  let sym := stx[5]
  let prec1 := Syntax.mkNatLit (prec.toNat + 1)
  let lhs := mkIdent <| ← Macro.addMacroScope `lhs
  let rhs := mkIdent <| ← Macro.addMacroScope `rhs
  let (items, args) :=
    match kind with
    | `(Command.mixfixKind| prefix) => (#[sym, mkNullNode #[rhs, .missing, prec]], #[rhs])
    | `(Command.mixfixKind| infix) => (#[mkNullNode #[lhs, .missing, prec1], sym, mkNullNode #[rhs, .missing, prec1]], #[lhs, rhs])
    | `(Command.mixfixKind| infixl) => (#[mkNullNode #[lhs, .missing, prec], sym, mkNullNode #[rhs, .missing, prec1]], #[lhs, rhs])
    | `(Command.mixfixKind| infixr) => (#[mkNullNode #[lhs, .missing, prec1], sym, mkNullNode #[rhs, .missing, prec]], #[lhs, rhs])
    | `(Command.mixfixKind| postfix) => (#[mkNullNode #[lhs, .missing, prec], sym], #[lhs])
    | _ => unreachable!
  let stx := stx.setArg 5 (mkNullNode items)
  let stx := stx.setArg 7 (Syntax.mkApp ⟨stx[7]⟩ args)
  return stx.setKind ``usingNotation
