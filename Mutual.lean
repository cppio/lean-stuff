import Common.Meta

open Lean Meta Elab Term

instance : Inhabited (Subarray α) := ⟨#[][:0]⟩

private def addPreDefinitionsStructural (preDefs : Array PreDefinition) : TermElabM Unit := withLCtx {} {} do
  let preDefsOrig := preDefs
  let preDefs ← preDefs.mapM fun preDef =>
    lambdaTelescope preDef.value fun xs value => do
      logInfoAt preDef.ref m!"{preDef.declName} : {preDef.type} | {xs} => {value}"
      let value ← withOptions (smartUnfolding.set · false) <| unfoldDefinition value
      let casesOn := value.getAppFn.constName
      if !isCasesOnRecursor (← getEnv) casesOn then
        throwErrorAt preDef.ref "unsupported: not casesOn"
      let levels := value.getAppFn.constLevels!
      let args := value.getAppArgs
      let motive := args[0]!
      let major := args[1]!
      let minors := args[2:]
      if xs != #[major] || (← major.fvarId!.getDecl).binderInfo != .default || motive.containsFVar major.fvarId! || minors.any (·.containsFVar major.fvarId!) then
        throwErrorAt preDef.ref "unsupported: more than one argument"
      return (← getConstInfoRec (mkRecName casesOn.getPrefix), preDef, levels, motive, minors)

  let rv := preDefs[0]!.fst
  if rv.numParams != 0 || rv.numIndices != 0 then
    throwError "unsupported: params or indices"
  if preDefs.size != rv.all.length then
    throwError "invalid majors"
  let preDefs := preDefs.foldl (fun preDefs (rv, preDef) => preDefs.insert rv.name.getPrefix (rv, preDef)) (mkNameMap _)
  let .some preDefs := rv.all.toArray.mapM preDefs.find?
    | throwError "invalid majors"
  let fns := preDefs.map fun (_, preDef, _) => preDef.declName

  let motives := preDefs.map fun (_, _, _, motive, _) => motive
  let minors ← preDefs.concatMapM fun (rv, preDef, _, _, minors) => do
    if rv.rules.length != minors.size then
      throwErrorAt preDef.ref "unsupported"
    minors.toArray.zip rv.rules.toArray |>.mapM fun (minor, rule) => do
      let ihs ← lambdaTelescope rule.rhs fun xs rhs => do
        forallTelescope (← inferType rhs.getAppFn) fun args _ =>
          args[rule.nfields:].toArray.mapIdx (·.val + rule.nfields, ·) |>.foldlM (init := mkHashMap) fun ihs (idx, ih) => do
            let ty ← inferType ih
            let motive := ty.getAppFn
            let #[field] := ty.getAppArgs
              | throwErrorAt preDef.ref "unsupported"
            let .some motiveIdx := xs.findIdx? (· == motive)
              | throwErrorAt preDef.ref "unsupported"
            let .some fieldIdx := args.findIdx? (· == field)
              | throwErrorAt preDef.ref "unsupported"
            return ihs.insert motiveIdx <| (ihs.findD motiveIdx mkHashMap).insert fieldIdx idx
      lambdaTelescope (rule.rhs.beta motives) fun _ rhs => do
        forallTelescope (← inferType rhs.getAppFn) fun args _ => do
          let minor := minor.beta args[:rule.nfields] |>.headBeta
          let minor ← transform minor (post := fun e =>
            match fns.findIdx? e.isAppOf with
            | .none => return .done e
            | .some idx => do
              let recArgs := e.getAppArgs
              let arg := recArgs[0]!
              let .some argIdx := args.findIdx? (· == arg)
                | throwErrorAt preDef.ref "invalid rec app"
              let .some fields := ihs.find? idx
                | throwErrorAt preDef.ref "invalid rec app"
              let .some ih := fields.find? argIdx
                | throwErrorAt preDef.ref "invalid rec app"
              return .done (mkAppN args[ih]! recArgs[1:])
          ) (skipConstInApp := true)
          mkLambdaFVars args minor

  for (rv, preDef, levels, _) in preDefs do
    addNonRec { preDef with value := mkAppN (mkAppN (.const rv.name levels) motives) minors } false

  addAndCompilePartialRec preDefsOrig

  for (_, preDef, _) in preDefs do
    Structural.registerEqnsInfo preDef 0

    addNonRec { preDef with
      declName := mkSmartUnfoldingNameFor preDef.declName
      modifiers := {}
    }

    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

syntax "#structural" : command

elab_rules : command
  | `(mutual #structural%$tk $ds* end) => withRef tk do
    let views ← ds.mapM fun d : Syntax => do Command.mkDefView (← elabModifiers d[0]) d[1]
    Command.runTermElabM fun vars => do
    -- copied from Lean/Elab/MutualDef.lean
    let scopeLevelNames ← getLevelNames
    let headers ← _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.elabHeaders views
    let headers ← _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.levelMVarToParamHeaders views headers
    let allUserLevelNames := _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.getAllUserLevelNames headers
    _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.withFunLocalDecls headers fun funFVars => do
      for view in views, funFVar in funFVars do
        addLocalVarInfo view.declId funFVar
      let values ←
        try
          let values ← _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.elabFunValues headers
          Term.synthesizeSyntheticMVarsNoPostponing
          values.mapM (instantiateMVars ·)
        catch ex =>
          logException ex
          headers.mapM fun header => mkSorry header.type (synthetic := true)
      let headers ← headers.mapM _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.instantiateMVarsAtHeader
      let letRecsToLift ← getLetRecsToLift
      let letRecsToLift ← letRecsToLift.mapM _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.instantiateMVarsAtLetRecToLift
      _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.checkLetRecsToLiftTypes funFVars letRecsToLift
      _private.Lean.Elab.MutualDef.0.Lean.Elab.Term.withUsed vars headers values letRecsToLift fun vars => do
        let preDefs ← MutualClosure.main vars headers funFVars values letRecsToLift
        for preDef in preDefs do
          trace[Elab.definition] "{preDef.declName} : {preDef.type} :=\n{preDef.value}"
        let preDefs ← withLevelNames allUserLevelNames <| levelMVarToParamPreDecls preDefs
        let preDefs ← instantiateMVarsAtPreDecls preDefs
        let preDefs ← fixLevelParams preDefs scopeLevelNames allUserLevelNames
        for preDef in preDefs do
          trace[Elab.definition] "after eraseAuxDiscr, {preDef.declName} : {preDef.type} :=\n{preDef.value}"
        checkForHiddenUnivLevels allUserLevelNames preDefs
        addPreDefinitionsStructural preDefs
        elabMutualDef.processDeriving views headers
