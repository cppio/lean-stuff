import Lean

open Lean

private def joinMapM [Monad m] (xs : Array α) (f : α → m MessageData) : m MessageData :=
  match xs.back? with
  | none => return .nil
  | some back => do
    xs.foldrM (λ x msg => return (← f x) ++ Format.line ++ msg) (← f back) (xs.size - 1)

private def joinMap (xs : Array α) (f : α → MessageData) : MessageData :=
  Id.run <| joinMapM xs f

private def nameCmp (n₁ : Name) (n₂ : Name) : Ordering :=
  cmp n₁.components n₂.components
where
  cmp
  | [], [] => .eq
  | [], _  => .lt
  | _,  [] => .gt
  | n₁ :: l₁, n₂ :: l₂ =>
    match n₁.cmp n₂ with
    | .eq => cmp l₁ l₂
    | ord => ord

elab tk:"#print prefix " i:ident : command => do
  let i := i.getId
  let cs := (← getEnv).constants.fold (fun cs name info =>
    if i.isPrefixOf name || i.isPrefixOf (privateToUserName? name |>.getD .anonymous) then cs.push info else cs) #[]
  let cs := cs.qsort (nameCmp ·.name ·.name == .lt)
  logInfoAt tk <| joinMap cs fun info => info.name ++ " : " ++ info.type

private def modifyLocalDecl [Monad m] (lctx : LocalContext) (e : Expr) (f : LocalDecl → m LocalDecl) : m LocalContext :=
  match lctx with
  | { fvarIdToDecl := map, decls := decls } =>
    match lctx.findFVar? e with
    | none      => return lctx
    | some decl => do
      let decl ← f decl
      return { fvarIdToDecl := map.insert decl.fvarId decl
               decls        := decls.set decl.index decl }

def Lean.Level.names : Level → List Name
  | zero => []
  | succ u => u.names
  | max u v => u.names ++ v.names
  | imax u v => u.names ++ v.names
  | param name => [name]
  | mvar mvarId => [mvarId.name]

def Lean.Expr.names : Expr → List Name
  | bvar _ => []
  | fvar fvarId => [fvarId.name]
  | mvar mvarId => [mvarId.name]
  | sort u => u.names
  | const declName us => declName :: us.bind Level.names
  | app fn arg => fn.names ++ arg.names
  | lam binderName binderType body _ => binderName :: binderType.names ++ body.names
  | forallE binderName binderType body _ => binderName :: binderType.names ++ body.names
  | letE declName type value body _ => declName :: type.names ++ value.names ++ body.names
  | lit _ => []
  | mdata _ expr => expr.names
  | proj typeName _ struct => typeName :: struct.names

elab tk:"#check_hyg " id:ident : command => do
  let c ← Lean.resolveGlobalConstNoOverload id
  let decl ← Lean.getConstInfo c
  let names := decl.type.names.filter Lean.Name.hasNum
  if !names.isEmpty then
    Lean.logErrorAt tk m!"found {names} in {decl.type}"

open Meta

elab "opaque_def% " i:ident : term => do
  let .opaqueInfo info ← getConstInfo <| ← resolveGlobalConstNoOverload i
    | throwError "'{i}' is not an opaque definition"
  let levels ← mkFreshLevelMVars info.levelParams.length
  let eq ← mkEq (.const info.name levels) (info.value.instantiateLevelParams info.levelParams levels)
  return .app (.const ``lcProof []) eq

opaque UnsafeMarker : Prop := True
unsafe def UnsafeMarker.mk : UnsafeMarker := cast (opaque_def% UnsafeMarker).symm ⟨⟩

private partial def reduceStar (e : Expr) : MetaM Expr :=
  let rec visit (e : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache e fun _ => withIncRecDepth do
      let e ← whnf e
      match e with
      | .app .. =>
        let f     ← visit e.getAppFn
        let mut args  := e.getAppArgs
        for i in [:args.size] do
          args ← args.modifyM i visit
        return mkAppN f args
      | .lam ..        => lambdaTelescope e fun xs b => do
        let mut lctx ← getLCtx
        for x in xs do
          lctx ← modifyLocalDecl lctx x λ e => return e.setType (← visit e.type)
        withLCtx lctx (← getLocalInstances) do
          return (← mkLambdaFVars xs (← visit b)).eta
      | .forallE ..    => forallTelescope e fun xs b => do
        let mut lctx ← getLCtx
        for x in xs do
          lctx ← modifyLocalDecl lctx x λ e => return e.setType (← visit e.type)
        withLCtx lctx (← getLocalInstances) do
          mkForallFVars xs (← visit b)
      | .proj n i s .. => return mkProj n i (← visit s)
      | _                  => return e
  withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) <|
    withTransparency .all <|
      visit e |>.run

open Elab

elab tk:"#reduce*" term:term : command =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => Term.withDeclName `_reduceStar do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    logInfoAt tk (← reduceStar e)

elab "reduce% " term:term : term <= type? => do
  let e ← Term.elabTerm term type?
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  reduceStar e

elab tk:"#print instances " t:term : command => Command.runTermElabM fun _ => do
  let t ← `($t ..)
  let e ← Term.elabType t
  let insts ← SynthInstance.getInstances e
  logInfoAt tk <| ← joinMapM insts λ inst => return inst.val ++ " : " ++ (← inferType inst.val)

elab tk:"#time " c:command : command => do
  let start ← IO.monoMsNow
  Command.elabCommand c
  logInfoAt tk m!"time: {(← IO.monoMsNow) - start} ms"

open Parser

macro:max lhs:ident ".0" "." rhs:ident : term => return mkIdent (lhs.getId.num 0 |>.appendCore rhs.getId)

macro:max lhs:name ".0" "." rhs:ident : term => `($(Syntax.mkNameLit s!"`{lhs.getName}.0.{rhs.getId}"):name)

macro:max lhs:Term.doubleQuotedName ".0" "." rhs:ident : term =>
  let lhs : Ident := ⟨lhs.raw[2]⟩
  `(``$(mkIdent (lhs.getId.num 0 |>.appendCore rhs.getId)))

syntax "opaque {" (ppLine (Command.unsafe)? ("def " <|> "instance ") (ident)? bracketedBinder* " : " term (" := " term)?)* ppLine "}" : command

macro_rules
  | `(opaque { $[$[$unsafes]? $kinds $(names)? $binds* : $tys $[:= $vals]?]* }) => do
    let inferInstance ← ``(inferInstance)
    let vals ← (unsafes.zip vals).mapM λ (safety, val?) =>
      let val := val?.getD inferInstance
      if safety.isSome then ``(λ _ ↦ $val) else return val

    let inst ← Macro.addMacroScope "inst"
    let fields := names.mapIdx λ idx name? => mkIdent <| toString <| match name? with | some name => name.getId | none => inst.num idx

    let nameFields : NameMap _ := .fromArray (cmp := _) <| (names.zip fields).filterMap λ | (some name, field) => some (name.getId, field.raw) | _ => none
    let fieldTys ← (unsafes.zip tys).mapM λ (safety, ty) =>
      let ty := ⟨Id.run <| ty.raw.replaceM (nameFields.find? ·.getId)⟩
      if safety.isSome then ``(UnsafeMarker → $ty) else return ty

    let defs := mkNullNode <| ← (unsafes.zip <| kinds.zip <| names.zip <| binds.zip <| fields.zip tys).mapM λ (safety, kind, name?, binds, field, ty) => do
      let ty ← ``(∀ $binds*, $ty)
      let val ← if safety.isSome then `(Imp.$field .mk) else `(Imp.$field)
      match kind.raw[0].isToken "instance", name? with
      | false, some name => `($[$safety:unsafe]? def $name : $ty := $val)
      | true,  some name => `($[$safety:unsafe]? instance $name:ident : $ty := $val)
      | true,  none      => `($[$safety:unsafe]? instance : $ty := $val)
      | false, none      => throw .unsupportedSyntax

    `(private structure Sig where $[$fields:ident $binds:bracketedBinder* : $fieldTys]*
      private def Impl : Sig where $[$fields $binds:bracketedBinder* := $vals]*
      private opaque Imp : Sig := Impl
      $(⟨defs⟩):command)

syntax (name := rawDef) "#def " ident (".{" ident,+ "}")? " : " term " := " term : command

elab "#del" table:("leadingParser" <|> "trailingParser") cat:ident tk:ident idx:num : command => do
  let env ← getEnv
  let state := parserExtension.getState env
  let .some category := state.categories.find? cat.getId
    | throwErrorAt cat "unknown category"
  let .some parsers :=
      match table.raw.getKind with
      | `token.leadingParser => category.tables.leadingTable.find? tk.getId
      | _ => category.tables.trailingTable.find? tk.getId
    | throwErrorAt tk "unknown token"
  if idx.getNat >= parsers.length then
    throwErrorAt idx "invalid index"
  let parsers := parsers.eraseIdx idx.getNat
  let category :=
    match table.raw.getKind with
    | `token.leadingParser => { category with tables.leadingTable := RBMap.insert category.tables.leadingTable tk.getId parsers }
    | _ => { category with tables.trailingTable := RBMap.insert category.tables.trailingTable tk.getId parsers }
  let state := { state with categories := state.categories.insert cat.getId category }
  setEnv <| parserExtension.modifyState env fun _ => state

open Elab.Term Command

@[command_elab rawDef]
unsafe def rawDefElab : CommandElab
  | `(rawDef| #def $n $[.{$ls?,*}]? : $t := $v) => liftTermElabM do
    let name := n.getId
    let levelParams :=
      match ls? with
      | some ls => ls.getElems.map TSyntax.getId |>.toList
      | _ => []
    let type ← evalTerm Expr (.const ``Expr []) t
    let value ← evalTerm Expr (.const ``Expr []) v
    addAndCompile <| .defnDecl {
      name
      levelParams
      type
      value
      hints := .abbrev
      safety := .safe
    }
  | _ => throwUnsupportedSyntax

elab "#print nontriv eqns " id:ident : command => liftTermElabM do
  let n ← resolveGlobalConstNoOverload id
  let some eqns ← getEqnsFor? n
    | return
  for eqn in eqns do
    if !(← isRflTheorem eqn) then
      logInfo (privateToUserName? eqn |>.getD eqn)

syntax (name := annotate) "annotate% " name term : term
@[term_elab annotate]
def elabAnnotate : TermElab
  | `(annotate% $name $t), expectedType? => return mkAnnotation name.getName <| ← elabTerm t expectedType?
  | _, _ => throwUnsupportedSyntax
