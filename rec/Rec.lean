import Rec.Util
import Lean

inductive Ordinal
  | zero : Ordinal
  | succ : Ordinal → Ordinal
  | limit : (Nat → Ordinal) → Ordinal

inductive Fin2 : Nat → Type
  | zero : Fin2 .zero
  | succ : Fin2 n → Fin2 n.succ

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α .zero
  | cons : α → Vec α n → Vec α n.succ

inductive Tree (α : Type u)
  | leaf : α → Tree α
  | inner : List (Tree α) → Tree α

mutual

inductive Tree' (α : Type u)
  | leaf : α → Tree' α
  | inner : List' α → Tree' α
  | inner' : Vec (Tree' α) n → Tree' α

inductive List' (α : Type u)
  | nil : List' α
  | cons : Tree' α → List' α → List' α
  | mk : Option (Tree' α × List' α) → List' α

end

deriving instance Repr for Lean.ConstantVal
deriving instance Repr for Lean.InductiveVal
deriving instance Repr for Lean.ConstructorVal
deriving instance Repr for Lean.RecursorRule
deriving instance Repr for Lean.RecursorVal

namespace Lean.Expr

variable (map : NameMap Name) in
def replaceConsts (e : Expr) : Expr :=
  match e with
  | const n us      => const (map.findD n n) us
  | forallE _ d b _ => e.updateForallE! d.replaceConsts b.replaceConsts
  | lam _ d b _     => e.updateLambdaE! d.replaceConsts b.replaceConsts
  | mdata _ b       => e.updateMData! b.replaceConsts
  | letE _ t v b _  => e.updateLet! t.replaceConsts v.replaceConsts b.replaceConsts
  | app f a         => e.updateApp! f.replaceConsts a.replaceConsts
  | proj _ _ b      => e.updateProj! b.replaceConsts
  | _               => e

def replaceConst (old new : Name) : Expr → Expr :=
  replaceConsts <| .insert .empty old new

def getLambdaBody : Expr → Expr
  | lam _ _ b _ => getLambdaBody b
  | e => e

end Lean.Expr

def Lean.Meta.mkFunExts (e : Expr) : MetaM Expr :=
  do forallTelescope (← inferType e) λ xs _ =>
      xs.foldrM (λ x e => do mkFunExt (← mkLambdaFVars #[x] e)) (mkAppN e xs)

open Lean Meta Elab in
def compileRec (rv : RecursorVal) : TermElabM Unit := do
  unless rv.numMotives == 1 do
    throwError "mutual/nested inductives unsupported"
  let levels := rv.levelParams.map .param
  let name ← mkFreshUserName rv.name
  addAndCompile <| .mutualDefnDecl [{ rv with
    name
    value := ← forallTelescope rv.type λ xs body => do
      let major ← inferType xs[rv.getMajorIdx]!
      let val := .const (mkCasesOnName major.getAppFn.constName!) levels
      let val := mkAppN val xs[:rv.numParams]
      let val := .app val <| ← mkLambdaFVars xs[rv.getFirstIndexIdx:] body
      let val := mkAppN val xs[rv.getFirstIndexIdx:]
      let val := mkAppN val <| rv.rules.toArray.map λ rule =>
        .beta (rule.rhs.replaceConst rv.name name) xs[:rv.getFirstIndexIdx]
      mkLambdaFVars xs val
    hints := .abbrev
    safety := .partial
  }]
  let old := .const rv.name levels
  let new := .const name levels
  let name ← mkFreshUserName <| rv.name.str "eq"
  addDecl <| .mutualDefnDecl [{
    name
    levelParams := rv.levelParams
    type := ← mkEq old new
    value := ← forallTelescope rv.type λ xs _ => do
      let pf := .const rv.name (.zero :: levels.tail!)
      let pf := mkAppN pf xs[:rv.numParams]
      let old := mkAppN old xs
      let new := mkAppN new xs
      let motive ← mkLambdaFVars xs[rv.getFirstIndexIdx:] <| ← mkEq old new
      let pf := .app pf motive
      let pf := mkAppN pf <| ← rv.rules.toArray.zip xs[rv.getFirstMinorIdx:] |>.mapM λ (rule, minor) => do
        forallTelescope ((← inferType minor).replaceFVar xs[rv.numParams]! motive) λ ys _ => do
          let minor := mkAppN minor ys[:rule.nfields]
          let pf' ← mkEqRefl minor
          let pf' ← ys[rule.nfields:].foldlM (λ pf' y => do mkCongr pf' (← mkFunExts y)) pf'
          mkLambdaFVars ys pf'
      let pf := mkAppN pf xs[rv.getFirstIndexIdx:]
      xs.foldrM (λ x pf => do mkFunExt (← mkLambdaFVars #[x] pf)) pf
    hints := .opaque
    safety := .partial
  }]
  Compiler.CSimp.add name .global

open Lean Meta Elab Command in 
elab "#compile " i:ident : command => liftTermElabM <| withRef i do
  let i := i.getId
  _ ← getConstInfoInduct i
  compileRec <| ← getConstInfoRec <| mkRecName i

#compile Nat
#compile List
/-
#compile Fin2
--#compile Vec
--#compile Ordinal
-/

open Lean in
partial def getMutualRecs (name : Name) : CoreM (NameMap RecursorVal) :=
  let rec visit name recs := do
    if recs.contains name then return recs
    let info ← getConstInfoRec name
    let mut recs := recs.insert name info
    for rule in info.rules do
      for e in rule.rhs.getLambdaBody.getAppArgs[rule.nfields:] do
        recs ← visit e.getLambdaBody.getAppFn.constName! recs
    return recs
  visit name .empty

-- C - indices → major → Sort u
-- minors - one for each constructor, cnstrargs → ihs → motive indices (cnstr cnstrargs)
-- indices - one for each index
-- major - Ind params indices

-- order of motives is .all and then the nested ones

-- Cs - motives, one for each indtype
-- minors - concatenation of minors for each indtype
-- recty - params → Cs → minors → indices → major → motive indices major
-- rules - params → Cs → minors → cnstrargs → minor cnstrargs ihs
--            ih is lambda xs => rec params Cs minors cnstr_indices (arg xs)

/- Remark `rec_fvars` free variables represent the recursor:
   - Type parameters `As` (size == `num_params`)
   - Motives `Cs`         (size == `num_motives`)
   - Minor premises       (size == `num_minors`)
   - Indices              (size == `num_indices`)
   - Major premise        (size == 1)
   The new `cases_on` recursor will have
   - Type parameters `As` (size == `num_params`)
   - Motive C[i]          (size == 1)
   - Minor premises C[i]  (size == number of constructors of the main type)
   - Indices              (size == `num_indices`)
   - Major premise        (size == 1)
-/

-- casesOn - params → main motive → indices → major → main minors → rec_type

open Lean Meta Elab in
def compileMutualRecs (name : Name) : TermElabM Unit := do
  let rvs ← getMutualRecs name
  let names ← rvs.mapM λ name _ => applyVisibility .private <| name.appendAfter "'"
  addAndCompile <| .mutualDefnDecl (← rvs.foldM (λ defs name rv =>
    return {
      name := names.find! name
      levelParams := rv.levelParams
      type := rv.type
      value := dbgTraceVal <| ← forallTelescope rv.type λ xs body => do
        let major ← inferType xs[rv.getMajorIdx]!
        let motiveLevel := (← inferType body).sortLevel!
        let levels := motiveLevel :: major.getAppFn.constLevels!
        let val := .const (mkCasesOnName major.getAppFn.constName!) levels
        logInfo m!"{val} <- {major}"
        let val := mkAppN val major.getAppArgs[:major.getAppNumArgs - rv.numIndices]
        let val := .app val <| ← mkLambdaFVars xs[rv.getFirstIndexIdx:] body
        let val := mkAppN val xs[rv.getFirstIndexIdx:]
        let val := mkAppN val <| rv.rules.toArray.map λ rule =>
          .beta (rule.rhs.replaceConsts names) xs[:rv.getFirstIndexIdx]
        mkLambdaFVars xs val
      hints := .abbrev
      safety := .partial
    } :: defs
  ) [])
  let rvs := rvs.map λ name rv =>
    let levels := rv.levelParams.map .param
    (rv, levels, .const name levels, .const (names.find! name) levels)
  let motives ← rvs.mapM λ _ (rv, _, old, new) =>
    forallTelescope rv.type λ xs _ => do
      mkLambdaFVars xs <| ← mkEq (mkAppN old xs) (mkAppN new xs)
  let recs := Id.run do
    let mut recs : Array (Option Name) := .mkArray rvs.size none
    for (name, (rv, _)) in rvs do
      recs := recs.set! (rv.type.getForallBinderNames.length - 1 - rv.numParams - rv.type.getForallBody.getAppFn.bvarIdx!) name
    return recs.map Option.get!
  let motives := recs.map motives.find!
  let rules ← recs.foldlM (λ rules name => do
    let (rv, _) := rvs.find! name
    return rules.appendList <| rv.rules.map λ rule => (rule)
  ) #[]
  for (_, (rv, levels, old, new)) in rvs do
    let name ← applyVisibility .private <| rv.name.appendAfter "_eq'"
    addDecl <| .mutualDefnDecl [{
      name
      type := ← mkEq old new
      levelParams := rv.levelParams
      value := ← forallTelescope rv.type λ xs body => do
        let motives := motives.map (·.beta xs[:rv.getFirstIndexIdx])
        let motiveLevel := (← inferType body).sortLevel!
        let levels :=
          if motiveLevel.isZero
          then levels
          else .zero :: levels.tail!
        let pf := .const rv.name levels
        let pf := mkAppN pf xs[:rv.numParams]
        let pf := mkAppN pf motives
        let pf := mkAppN pf <| ← (rules.zip xs[rv.getFirstMinorIdx:].toArray).mapM λ (rule, minor) => do
          let minorTy ← inferType minor
          let minorTy ← forallTelescope rv.type λ xs' _ =>
            let minorTy := minorTy.replaceFVars xs[rv.numParams:rv.getFirstIndexIdx] xs'[rv.numParams:rv.getFirstIndexIdx]
            return motives.zip xs'[rv.numParams:rv.getFirstIndexIdx].toArray |>.foldl (λ minorTy (t, f) => minorTy.replaceFVar f t) minorTy -- TODO remove foldl
          forallTelescope minorTy λ ys _ => do
            let pf' ← mkEqRefl <| mkAppN minor ys[:rule.nfields]
            let pf' ← ys[rule.nfields:].foldlM (λ pf' y => do mkCongr pf' (← mkFunExts y)) pf'
            mkLambdaFVars ys pf'
        let pf := mkAppN pf xs[rv.getFirstIndexIdx:]
        xs.foldrM (λ x pf => do mkFunExt (← mkLambdaFVars #[x] pf)) pf
      hints := .opaque
      safety := .partial
    }]
    Compiler.CSimp.add name .global

open Lean Meta Elab Command in 
elab "#compile mutual " i:ident : command => liftTermElabM <| withRef i do
  let i := i.getId
  _ ← getConstInfoInduct i
  compileMutualRecs <| mkRecName i

/-
inductive Foo (α β : Type)
inductive Bar : Nat → Type
  | mk : Foo (Bar 0) PUnit → Bar 0
  | mk' : (Nat → Foo (Bar 1) PEmpty) → Bar 1

inductive Baz : ∀ {α}, α → Sort _
  | mk : Baz @Bar.rec

inductive Test (α : Type) : Nat → Nat → Type
  | mk : Vec (Test α m m) m → Test α m n

inductive Simple
  | mk : (Unit → Unit → Simple) → Simple

/-
inductive Wtf
  | mk : (Unit → Nat → Wtf) → Wtf
  -/
  -/

inductive Foo : Nat → Type 1
  | mk : List (Foo n) → Foo n
  --| inc : Foo n → Foo n.succ

#check Foo.rec
#check Foo.rec_1
set_option pp.all true
#compile mutual Foo
