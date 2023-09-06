import Mathlib.Data.Nat.Basic

open Lean

abbrev CommandMacroM := StateT (Array Command) MacroM

def CommandMacroM.push (c : CommandMacroM Command) : CommandMacroM Unit :=
  do modify (·.push <| ← c)

def CommandMacroM.run (x : CommandMacroM Unit) : MacroM Command := do
  let (_, cs) ← x #[]
  return ⟨mkNullNode cs⟩

section

open Parser Term

instance : Coe (TSyntax ``hole) Term := ⟨(⟨·⟩)⟩

def mkHole : TSyntax ``hole :=
  mkNode ``hole #[.atom .none "_"]

structure BinderView where
  id : Ident
  type : Term
  info : BinderInfo := .default

def BinderView.toImplicit (binder : BinderView) : BinderView :=
  if binder.info == .default
  then { binder with info := .implicit }
  else binder

def BinderView.toBinder (binder : BinderView) : MacroM (TSyntax ``bracketedBinder) :=
  match binder.info with
  | .default        => `(bracketedBinderF| ($binder.id : $binder.type))
  | .implicit       => `(bracketedBinderF| {$binder.id : $binder.type})
  | .strictImplicit => `(bracketedBinderF| ⦃$binder.id : $binder.type⦄)
  | .instImplicit   => `(bracketedBinderF| [$binder.id : $binder.type])

def mkFreshId [Monad m] [MonadQuotation m] (n := `x) : m Ident :=
  return mkIdent <| ← withFreshMacroScope <| MonadQuotation.addMacroScope n

def getOrFresh : Option Ident → MacroM Ident
  | some id => return id
  | none => mkFreshId

def getOrFreshHole : TSyntax [identKind, ``hole] → MacroM Ident
  | `(Term.ident| $id:ident) => return id
  | _ => mkFreshId

def BinderView.fromBinder (stx : TSyntax [identKind, ``hole, ``bracketedBinder]) (defaultType? : Option Term := none) : MacroM (Array BinderView) :=
  match stx with
  | `(Term.ident| $id:ident)
  | `(hole| $id:hole) => return #[{ id := ← getOrFreshHole id, type := defaultType?.getD mkHole }]
  | `(bracketedBinderF| ($args* $[: $type?]? $[$_]?)) => common args type? .default
  | `(bracketedBinderF| ⦃$args* $[: $type?]?⦄) => common args type? .strictImplicit
  | `(bracketedBinderF| {$args* $[: $type?]?}) => common args type? .implicit
  | `(bracketedBinderF| [$[$id? :]? $type]) => return #[{ id := ← getOrFresh id?, type, info := .instImplicit }]
  | _ => throw <| .error stx "invalid binder"
where
  common args type? info := do
    unless defaultType?.isNone do throw <| .error stx "invalid binder"
    args.mapM λ arg => return { id := ← getOrFreshHole arg, type := type?.getD mkHole, info }

def BinderView.fromBinders (stx : TSyntaxArray [identKind, ``hole, ``bracketedBinder]) (defaultType? : Option Term := none) : MacroM (Array BinderView) :=
  return .flatten <| ← stx.mapM (fromBinder · defaultType?)

end

partial def splitArrows (t : Term) (args : Array BinderView := #[]) : MacroM (Array BinderView × Term) :=
  match t with
  | `($type → $ret) => do splitArrows ret <| args.push { id := ← mkFreshId, type }
  | `($arg:bracketedBinder → $ret) => do splitArrows ret <| args.append <| ← BinderView.fromBinder arg
  | `(∀ $arg* $[: $type?]?, $ret) => do splitArrows ret <| args.append <| ← BinderView.fromBinders arg type?
  | ret => return (args, ret)

def joinArrows (args : Array BinderView) : Term → MacroM Term :=
  go args.toListRev
where
  go
  | [], ret => return ret
  | arg :: args, ret => do go args <| ← `($(← arg.toBinder):bracketedBinder → $ret)

partial def splitApp : Term → Term × Array Term
  | `($fn $args*) => let (fn', args') := splitApp fn; (fn', args' ++ args)
  | `(($t)) => splitApp t
  | t => (t, #[])

partial def getAppHeadId : Term → Option Ident
  | `($t $_*) => getAppHeadId t
  | `(($t)) => getAppHeadId t
  | `($id:ident)
  | `(@$id:ident) => some id
  | _ => none

def appHeadMatches (t : Term) (name : Name) : Bool :=
  match getAppHeadId t with
  | some id => id.getId.isSuffixOf name
  | none => false

syntax (name := coinductive) "coinductive " declId optDeclSig ("\n| " Parser.rawIdent optDeclSig)* : command

structure CtorView where
  id : Ident
  args : Array (BinderView × Bool)

structure CoInductiveView where
  id : Ident
  levels : Array Ident
  binders : TSyntaxArray ``Parser.Term.bracketedBinder
  implicitBinders : TSyntaxArray ``Parser.Term.bracketedBinder
  params : Array Ident
  type : Term
  ctors : Array CtorView
  ctorIds : Array Ident

def CoInductiveView.ofSyntax : Syntax → MacroM CoInductiveView
  | `(coinductive $id$[.{$levels?,*}]? $binders* $[: $type?]? $[| $ctorIds $ctorBinders* $[: $ctorTypes?]?]*) => do
    let binderViews ← BinderView.fromBinders binders
    let params := binderViews.map BinderView.id
    let ty ← `(@$id $params*)
    return {
      id
      levels := match levels? with | some levels => levels.getElems | none => #[]
      binders := ← binderViews.mapM BinderView.toBinder
      implicitBinders := ← binderViews.mapM (·.toImplicit.toBinder)
      params
      type := ←
        match type? with
        | none => `(Type _)
        | some type => do
          unless type matches `(Type $_) do throw <| .error type "unsupported type"
          pure type
      ctors := ← (ctorIds.zip <| ctorBinders.zip ctorTypes?).mapM λ (ctorId, ctorBinders, ctorType?) => do
        let (args, retTy) := ←
          match ctorType? with
          | some ctorType => splitArrows ctorType
          | none => pure (#[], ty)
        unless appHeadMatches retTy id.getId do throw <| .error retTy "unexpected return type"
        let ctorBinderViews ← BinderView.fromBinders ctorBinders
        return {
          id := ctorId
          args := ctorBinderViews ++ args |>.map λ arg =>
            if appHeadMatches arg.type id.getId
            then ({ arg with type := ty }, true)
            else (arg, false)
        }
      ctorIds
    }
  | _ => Macro.throwUnsupported

def defineCoInductive (view : CoInductiveView) : CommandMacroM Unit := do
  let Approx := mkIdent <| view.id.getId ++ `Approx
  let «⋯» := mkIdent `«⋯»
  let type ← `(@$Approx $view.params* ℓ)
  let binders ← view.ctors.mapM λ ctor =>
    ctor.args.mapM λ
      | (arg, false) => arg.toBinder
      | (arg, true) => { arg with type }.toBinder
  let type ← `(@$Approx $view.params* (Nat.succ ℓ))
  let types := view.ctors.map λ _ => type
  CommandMacroM.push `(
    inductive $Approx.{$view.levels,*} $view.binders* : Nat → $view.type
      | $«⋯»:ident : @$Approx $view.params* Nat.zero
    $[| $view.ctorIds:ident {ℓ : Nat} $binders* : $types]*
  )

  let Agree := mkIdent <| Approx.getId ++ `Agree
  let type₁ ← `(@$Approx $view.params* ℓ₁)
  let type₂ ← `(@$Approx $view.params* ℓ₂)
  let (binders, types) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.args.mapM λ
      | (arg, false) => return (#[← arg.toBinder], arg.id, arg.id)
      | (arg, true) => do
        let x₁ ← mkFreshId arg.id.getId
        let x₂ ← mkFreshId arg.id.getId
        let ih ← mkFreshId arg.id.getId
        return (
          #[
            ← { arg with id := x₁, type := type₁ }.toBinder,
            ← { arg with id := x₂, type := type₂ }.toBinder,
            ← BinderView.toBinder { id := ih, type := ← `(@$Agree $view.params* ℓ₁ ℓ₂ $x₁ $x₂) }
          ],
          x₁,
          x₂
        )
    let (args₁, args₂) := args.unzip
    return (
      binders.flatten,
      ← `(@$Agree $view.params* (Nat.succ ℓ₁) (Nat.succ ℓ₂) (@$ctor.id $view.params* ℓ₁ $args₁*) (@$ctor.id $view.params* ℓ₂ $args₂*))
    )
  CommandMacroM.push `(
    inductive $Agree.{$view.levels,*} $view.implicitBinders* : {ℓ₁ ℓ₂ : Nat} → @$Approx $view.params* ℓ₁ → @$Approx $view.params* ℓ₂ → Prop
      | $«⋯»:ident {ℓ₂ : Nat} {x : @$Approx $view.params* ℓ₂} : @$Agree $view.params* Nat.zero ℓ₂ (@$«⋯» $view.params*) x
    $[| $view.ctorIds:ident {ℓ₁ ℓ₂ : Nat} $binders* : $types]*
  )

  let Pattern := mkIdent <| view.id.getId ++ `Pattern
  let type ← `(α)
  let binders ← view.ctors.mapM λ ctor =>
    ctor.args.mapM λ
      | (arg, false) => arg.toBinder
      | (arg, true) => { arg with type }.toBinder
  let type ← `(@$Pattern $view.params* α)
  let types := view.ctors.map λ _ => type
  CommandMacroM.push `(
    inductive $Pattern.{u, $view.levels,*} $view.binders* (α : Type u)
    $[| $view.ctorIds:ident $binders* : $types]*
  )

  let map := mkIdent <| Pattern.getId ++ `map
  let mapApprox := mkIdent <| Pattern.getId ++ `mapApprox
  let mapAgree := mkIdent <| Pattern.getId ++ `mapAgree
  let (binders, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.args.mapM λ
      | (arg, false) => return (arg.id, arg.id, #[arg.id])
      | (arg, true) =>
        return (
          arg.id,
          ← `(f $arg.id),
          #[← `(f $arg.id), ← `(g $arg.id), ← `(h $arg.id)]
        )
    let (args₁, args₃) := args.unzip
    let approxCtor := mkIdent <| Approx.getId ++ ctor.id.getId
    let agreeCtor := mkIdent <| Agree.getId ++ ctor.id.getId
    return (
      ← `(@$ctor.id $view.params* α $binders*),
      ← `(@$ctor.id $view.params* β $args₁*),
      ← `(@$approxCtor $view.params* ℓ $args₁*),
      ← `(@$agreeCtor $view.params* ℓ₁ ℓ₂ $args₃.flatten*)
    )
  let (args₁, args) := args.unzip
  let (args₂, args₃) := args.unzip
  CommandMacroM.push `(
    def $map.{u, v, $view.levels,*} $view.implicitBinders* {α : Type u} {β : Type v} (f : α → β) : @$Pattern $view.params* α → @$Pattern $view.params* β
    $[| $binders => $args₁]*
    def $mapApprox.{u, $view.levels,*} $view.implicitBinders* {α : Type u} {ℓ : Nat} (f : α → @$Approx $view.params* ℓ) : @$Pattern $view.params* α → @$Approx $view.params* (Nat.succ ℓ)
    $[| $binders => $args₂]*
    theorem $mapAgree.{u, $view.levels,*} $view.implicitBinders* {α : Type u} {ℓ₁ ℓ₂ : Nat} {f : α → @$Approx $view.params* ℓ₁} {g : α → @$Approx $view.params* ℓ₂} (h : (x : α) → @$Agree $view.params* ℓ₁ ℓ₂ (f x) (g x)) : {x : @$Pattern $view.params* α} → @$Agree $view.params* (Nat.succ ℓ₁) (Nat.succ ℓ₂) (@$mapApprox $view.params* α ℓ₁ f x) (@$mapApprox $view.params* α ℓ₂ g x)
    $[| $binders => $args₃]*
  )

  let corec := mkIdent <| view.id.getId ++ `corec
  let «approx⋯» := mkIdent <| Approx.getId ++ «⋯».getId
  let «agree⋯» := mkIdent <| Agree.getId ++ «⋯».getId
  CommandMacroM.push `(
    def $view.id.{$view.levels,*} $view.binders* := { f : (ℓ : Nat) → @$Approx $view.params* ℓ // (ℓ : Nat) → @$Agree $view.params* ℓ (Nat.succ ℓ) (f ℓ) (f (Nat.succ ℓ)) }
    def $corec.{u, $view.levels,*} $view.implicitBinders* {σ : Type u} (f : σ → @$Pattern $view.params* σ) (s : σ) : @$view.id $view.params* where
      val ℓ := @Nat.rec (λ ℓ => σ → @$Approx $view.params* ℓ) (λ _ => @$«approx⋯» $view.params*) (λ ℓ ih s => @$mapApprox $view.params* σ ℓ ih (f s)) ℓ s
      property ℓ := Nat.rec (λ _ => @$«agree⋯» $view.params* (Nat.succ Nat.zero) _) (λ ℓ ih s => @$mapAgree $view.params* σ ℓ (Nat.succ ℓ) _ _ ih (f s)) ℓ s
  )

  let wrappers ← CommandMacroM.run do
    for ctor in view.ctors do
      let (binders, args) := Array.unzip <| ← ctor.args.mapM λ
        | (arg, false) => return (← arg.toBinder, (arg.id : Term), #[(arg.id : Term)])
        | (arg, true) =>
          return (
            ← arg.toBinder,
            ← `(Subtype.val $(arg.id) ℓ),
            #[← `(Subtype.val $(arg.id) ℓ), ← `(Subtype.val $(arg.id) (Nat.succ ℓ)), ← `(Subtype.property $(arg.id) ℓ)]
          )
      let (args₁, args₂) := args.unzip
      let approxCtor := mkIdent <| Approx.getId ++ ctor.id.getId
      let agreeCtor := mkIdent <| Agree.getId ++ ctor.id.getId
      CommandMacroM.push `(
        def $ctor.id.{$view.levels,*} $view.implicitBinders* $binders* : @$view.id $view.params* where
          val
          | Nat.zero => @$«approx⋯» $view.params*
          | Nat.succ ℓ => @$approxCtor $view.params* ℓ $args₁*
          property
          | Nat.zero => @$«agree⋯» $view.params* (Nat.succ Nat.zero) _
          | Nat.succ ℓ => @$agreeCtor $view.params* ℓ (Nat.succ ℓ) $args₂.flatten*
      )
  CommandMacroM.push `(
    namespace $view.id
    $wrappers
    end $view.id
  )

  let refl := mkIdent <| Agree.getId ++ `refl
  let (binders, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.args.mapM λ
      | (arg, false) => return (arg.id, #[arg.id])
      | (arg, true) => return (arg.id, #[arg.id, arg.id, ← `(@$refl $view.params* ℓ $arg.id)])
    let approxCtor := mkIdent <| Approx.getId ++ ctor.id.getId
    let agreeCtor := mkIdent <| Agree.getId ++ ctor.id.getId
    return (← `(@$approxCtor $view.params* ℓ $binders*), ← `(@$agreeCtor $view.params* ℓ ℓ $args.flatten*))
  CommandMacroM.push `(
    theorem $refl.{$view.levels,*} $view.implicitBinders* {ℓ : Nat} : (x : @$Approx $view.params* ℓ) → @$Agree $view.params* ℓ ℓ x x
      | @$«approx⋯» $view.params* => @$«⋯» $view.params* Nat.zero (@$«approx⋯» $view.params*)
    $[| $binders => $args]*
  )

  let trans := mkIdent <| Agree.getId ++ `trans
  let (binders₁, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders₁, args) := Array.unzip <| ← ctor.args.mapM λ
      | (_, false) => return (#[], #[], #[])
      | (_, true) => do
        let x₁ := mkIdent <| ← Elab.Term.mkFreshBinderName
        let x₂ := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (#[x₁], #[x₂], #[← `($trans $x₁ $x₂)])
    let (binders₂, args) := args.unzip
    return (← `(.$ctor.id $binders₁.flatten*), ← `(.$ctor.id $binders₂.flatten*), ← `(.$ctor.id $args.flatten*))
  let (binders₂, args) := args.unzip
  CommandMacroM.push `(
    theorem $trans.{$view.levels,*} $view.implicitBinders* {ℓ ℓ' : Nat} {x₁ : @$Approx $view.params* ℓ} {x₂ : @$Approx $view.params* (Nat.succ ℓ)} {x₃ : @$Approx $view.params* ℓ'} : @$Agree $view.params* ℓ (Nat.succ ℓ) x₁ x₂ → @$Agree $view.params* (Nat.succ ℓ) ℓ' x₂ x₃ → @$Agree $view.params* ℓ ℓ' x₁ x₃
      | @$«⋯» $view.params* (Nat.succ Nat.zero) _, _ => @$«⋯» $view.params* ℓ' x₃
    --$[| $binders₁, $binders₂ => $args]*
      | _, _ => sorry
  )

  /-
  let property := mkIdent <| view.id.getId ++ `property
  CommandMacroM.push `(
    theorem $property {$view.params*} (x : @$view.id $view.params*) ⦃ℓ₁ ℓ₂⦄ (h : ℓ₁ ≤ ℓ₂) : $Agree (x.val ℓ₁) (x.val ℓ₂) := by
      have ⟨ℓ, h⟩ := Nat.exists_eq_add_of_le h
      cases h
      exact ℓ.rec (λ _ => $refl) (λ ℓ ih ℓ₁ => $trans (Subtype.property x ℓ₁) (ℓ₁.succ_add ℓ ▸ ih _ :)) ℓ₁
  )

  let cases := mkIdent <| view.id.getId ++ `cases
  let (args, minors) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let args ← ctor.argTypes.mapM λ _ => return mkIdent <| ← Elab.Term.mkFreshBinderName
    return (args, ← `(Parser.Term.bracketedBinderF| ($ctor.id : ∀ $args:ident*, motive ($ctor.id $args*))))
  let arms ← (view.ctors.zip args).mapIdxM λ i (ctor, args) => do
    let otherCtors := ctors.eraseIdx i
    let rhs ←
      `(have : x = .$ctor.id $args* := Subtype.eq <| funext λ
          | .zero => match x.val .zero with | .«⋯» => rfl
          | .succ ℓ =>
            have := h ▸ $property x ℓ.zero_lt_succ
            match h' : x.val ℓ.succ with
          $[| .$otherCtors .. => by cases h' ▸ this]*
            | .$ctor.id .. => by
              cases h' ▸ this
              congr
              all_goals
                dsimp only []
                split <;> rename_i h'' <;> cases h' ▸ h''
                rfl
        this ▸ $ctor.id $args*)
    let ihs := args.zip ctor.argTypes |>.filterMap λ | (_, _, false) => none | (arg, _, true) => some arg
    ihs.foldrM (init := rhs) λ arg rhs =>
      `(let $arg := {
          val := λ ℓ =>
            match h' : x.val ℓ.succ with
          $[| .$otherCtors .. => nomatch (h' ▸ h ▸ x.property ℓ.zero_lt_succ :)]*
            | .$ctor.id $args* => $arg
          property := λ ℓ =>
            match h₁ : x.val ℓ.succ with
          $[| .$otherCtors .. => nomatch (h₁ ▸ h ▸ x.property ℓ.zero_lt_succ :)]*
            | .$ctor.id .. =>
              match h₂ : x.val ℓ.succ.succ with
            $[| .$otherCtors .. => nomatch (h₂ ▸ h ▸ x.property ℓ.succ.zero_lt_succ :)]*
              | .$ctor.id .. => by
                dsimp only []
                split <;> rename_i h₁' <;> cases h₁ ▸ h₁'
                split <;> rename_i h₂' <;> cases h₂ ▸ h₂'
                match h₁ ▸ h₂ ▸ x.property ℓ.succ.le_succ with
                | .$ctor.id $ihs:ident* => exact $arg
        }
        $rhs)
  CommandMacroM.push `(
    @[elab_as_elim]
    def $cases.{u} {$view.params*} {motive : @$view.id $view.params* → Sort u} $minors* x : motive x :=
      match h : x.val (.succ .zero) with
      $[| .$ctors $args* => $arms]*
  )

  let fold := mkIdent <| view.id.getId ++ `fold
  let (ctors', args') := (ctors, args)
  CommandMacroM.push `(
    def $fold {$view.params*} : @$Pattern $view.params* (@$view.id $view.params*) → @$view.id $view.params*
    $[| .$ctors $args* => $ctors' $args'*]*
  )

  let unfold := mkIdent <| view.id.getId ++ `unfold
  let unfold_fold := mkIdent <| unfold.getId ++ `fold
  let fold_unfold := mkIdent <| fold.getId ++ `unfold
  let unfold_inj := mkIdent <| unfold.getId ++ `inj
  let unfold_corec := mkIdent <| unfold.getId ++ `corec
  let args ← view.ctors.mapM λ ctor => do
    let args ← ctor.argTypes.mapM λ _ => return mkIdent <| ← Elab.Term.mkFreshBinderName
    `(λ $args* => rfl)
  CommandMacroM.push `(
    def $unfold {$view.params*} : @$view.id $view.params* → @$Pattern $view.params* (@$view.id $view.params*) :=
      $cases $(← ctors.mapM λ ctor => `(.$ctor))*
    @[simp]
    theorem $unfold_fold {$view.params*} : ∀ x, @$unfold $view.params* (@$fold $view.params* x) = x
    $[| .$ctors .. => rfl]*
    @[simp]
    theorem $fold_unfold {$view.params*} : ∀ x, @$fold $view.params* (@$unfold $view.params* x) = x :=
      @$cases $view.params* _ $args*
    theorem $unfold_inj {$view.params* x y} (h : @$unfold $view.params* x = @$unfold $view.params* y) : x = y :=
      @$fold_unfold $view.params* x ▸ @$fold_unfold $view.params* y ▸ congrArg (@$fold $view.params*) h
    @[simp]
    theorem $unfold_corec {$view.params* σ} f u : @$unfold $view.params* (@$corec $view.params* σ f u) = (f u).map (@$corec $view.params* σ f) := by
      cases h : f u
      all_goals
        dsimp only [$map:ident, $mapApprox:ident, $unfold:ident, $cases:ident, $corec:ident]
        try split <;> rename_i h' <;> cases h ▸ h'
        refine (eq_rec_constant ..).trans ?_
        congr
      all_goals simp [h]
      all_goals
        funext ℓ
        split <;> rename_i h' <;> cases h ▸ h'
        rfl
  )

  let theorems ← CommandMacroM.run do
    for ctor in view.ctors do
      let args ← ctor.argTypes.mapM λ _ => return mkIdent <| ← Elab.Term.mkFreshBinderName
      CommandMacroM.push `(
        @[simp]
        theorem $ctor.id {$view.params*} {motive} $ctors* $args* : @$cases $view.params* motive $ctors* (.$ctor.id $args*) = $ctor.id $args* := rfl
      )
  CommandMacroM.push `(
    namespace $cases
    $theorems
    end $cases
  )

  let theorems ← CommandMacroM.run do
    for ctor in view.ctors do
      let args ← ctor.argTypes.mapM λ _ => return mkIdent <| ← Elab.Term.mkFreshBinderName
      CommandMacroM.push `(
        @[simp]
        theorem $ctor.id {$view.params*} $args* : @$unfold $view.params* ($ctor.id $args*) = .$ctor.id $args* := rfl
      )
  CommandMacroM.push `(
    namespace $unfold
    $theorems
    end $unfold
  )

  let codef := mkIdent <| view.id.getId ++ `codef
  CommandMacroM.push `(
    def $codef {$view.params* σ} (f : σ → @$Pattern $view.params* (σ ⊕ @$view.id $view.params*) ⊕ @$view.id $view.params*) (s : σ) : @$view.id $view.params* :=
      @$corec $view.params* (σ ⊕ @$view.id $view.params*) (λ
        | .inl s =>
          match f s with
          | .inl x => x
          | .inr x => x.unfold.map .inr
        | .inr x => x.unfold.map .inr
      ) (.inl s)
  )

  let unfold_codef := mkIdent <| unfold.getId ++ `codef
  CommandMacroM.push `(
    @[simp]
    theorem $unfold_codef {$view.params* σ} f s : @$unfold $view.params* (@$codef $view.params* σ f s) =
      match f s with
      | .inl x =>
        x.map λ
          | .inl s => @$codef $view.params* σ f s
          | .inr x => x
      | .inr x => x.unfold
    := by
      have : ∀ x, @$corec $view.params* (σ ⊕ @$view.id $view.params*)
        (λ | .inl s =>
             match f s with
             | .inl x => x
             | .inr x => x.unfold.map .inr
           | .inr x => x.unfold.map .inr)
        (.inr x) = x
      := by
        intro x
        apply Subtype.eq
        funext ℓ
        dsimp [$corec:ident]
        induction ℓ generalizing x with
        | zero => cases x.val .zero; rfl
        | succ ℓ ih =>
          dsimp
          cases h : @$unfold $view.params* x
          all_goals
            rw [$map:ident, $mapApprox:ident]
            simp [ih]
            exact @$fold_unfold $view.params* x ▸ congrArg (@$fold $view.params*) h ▸ rfl
      rw [$codef:ident]
      simp
      cases f s with
      | inl =>
        congr
        funext x
        cases x with
        | inl => rfl
        | inr x => exact this x
      | inr x =>
        dsimp
        generalize @$unfold $view.params* x = x
        cases x
        all_goals
          dsimp [$map:ident]
          congr
        all_goals
          apply this
  )
  -/

/-
def defineCoInductiveImpl (view : CoInductiveView) : CommandMacroM Unit := do
  let ctors := view.ctors.map (·.id)

  let Impl := mkIdent <| view.id.getId ++ `Impl
  let Impl' := mkIdent <| view.id.getId ++ `Impl'
  let types ← view.ctors.mapM λ ctor => do
    let args ← ctor.argTypes.mapM λ
      | (arg, false) => return arg
      | (_, true) => `(Thunk (@$Impl' $view.params*))
    joinArrows args.toList <| ← `(@$Impl' $view.params*)
  CommandMacroM.push `(
    unsafe inductive $Impl'.{$view.levels,*} $view.binders*
    $[| $ctors:ident : $types]*
    unsafe def $Impl.{$view.levels,*} $view.binders* := Thunk (@$Impl' $view.params*)
  )

  let Pattern := mkIdent <| Impl.getId ++ `Pattern
  let orig_Pattern := mkIdent <| view.id.getId ++ `Pattern
  CommandMacroM.push `(
    def $Pattern := @$orig_Pattern
  )

  let corec := mkIdent <| Impl.getId ++ `corec
  let (binders, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.argTypes.mapM λ
      | (_, false) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, x)
      | (_, true) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, ← `($corec f $x))
    return (binders, ← `(.$ctor.id $args*))
  CommandMacroM.push `(
    unsafe def $corec {$view.params* σ} (f : σ → @$Pattern $view.params* σ) (s : σ) : @$Impl $view.params* := Thunk.mk λ _ =>
      match f s with
      $[| .$ctors $binders* => $args]*
  )

  let wrappers ← CommandMacroM.run do
    for ctor in view.ctors do
      let (types, args) := Array.unzip <| ← ctor.argTypes.mapM λ
        | (arg, false) => return (arg, mkIdent <| ← Elab.Term.mkFreshBinderName)
        | (_, true) => return (← `(@$Impl $view.params*), mkIdent <| ← Elab.Term.mkFreshBinderName)
      let type ← joinArrows types.toList <| ← `(@$Impl $view.params*)
      CommandMacroM.push `(
        unsafe def $ctor.id {$view.params*} : $type := λ $args:ident* =>
          Thunk.pure (.$ctor.id $args*)
      )
  CommandMacroM.push `(
    namespace $Impl
    $wrappers
    end $Impl
  )

  let cases := mkIdent <| Impl.getId ++ `cases
  let (args, minors) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let args ← ctor.argTypes.mapM λ _ => return mkIdent <| ← Elab.Term.mkFreshBinderName
    return (args, ← `(Parser.Term.bracketedBinderF| ($ctor.id : ∀ $args:ident*, motive ($ctor.id $args*))))
  let (ctors', args') := (ctors, args)
  CommandMacroM.push `(
    @[elab_as_elim]
    unsafe def $cases.{u} {$view.params*} {motive : @$Impl $view.params* → Sort u} $minors* x : motive x :=
      (id rfl : Thunk.pure (Thunk.get x) = x) ▸
      match Thunk.get x with
      $[| .$ctors $args* => $ctors' $args'*]*
  )

  let fold := mkIdent <| Impl.getId ++ `fold
  CommandMacroM.push `(
    unsafe def $fold {$view.params*} : @$Pattern $view.params* (@$Impl $view.params*) → @$Impl $view.params*
    $[| .$ctors $args* => $ctors' $args'*]*
  )

  let unfold := mkIdent <| Impl.getId ++ `unfold
  CommandMacroM.push `(
    unsafe def $unfold {$view.params*} : @$Impl $view.params* → @$Pattern $view.params* (@$Impl $view.params*) :=
      $cases $(← ctors.mapM λ ctor => `(.$ctor))*
  )

  let codef := mkIdent <| Impl.getId ++ `codef
  let (binders, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.argTypes.mapM λ
      | (_, false) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, x)
      | (_, true) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, ← `($(x).casesOn ($codef f) id))
    return (binders, ← `(.$ctor.id $args*))
  CommandMacroM.push `(
    unsafe def $codef {$view.params* σ} (f : σ → @$Pattern $view.params* (σ ⊕ @$Impl $view.params*) ⊕ @$Impl $view.params*) (s : σ) : @$Impl $view.params* := Thunk.mk λ _ =>
      match f s with
      | .inl x =>
        match x with
        $[| .$ctors $binders* => $args]*
      | .inr x => Thunk.get x
  )
--/

@[macro «coinductive»]
def expandCoInductive : Macro := λ stx => CommandMacroM.run do
  let view ← CoInductiveView.ofSyntax stx
  defineCoInductive view
  --defineCoInductiveImpl view

set_option autoImplicit false

set_option pp.explicit true
set_option trace.Elab.command true

coinductive List'.{u} (α : Type u)
  | mk {n} (l : List α) : l.length = n → List' α

coinductive CoNat
  | zero
  | succ (n : CoNat)

coinductive CoList.{u} (α : Type u)
  | nil : CoList α
  | cons : α → CoList α → CoList α

#print CoList.Approx.Agree.trans
theorem CoList.Approx.Agree.trans'.{u} {α : Type u} {ℓ ℓ' : Nat} {x₁ : @CoList.Approx α ℓ} {x₂ : @CoList.Approx α (Nat.succ ℓ)} {x₃ : @CoList.Approx α ℓ'} : @CoList.Approx.Agree α ℓ (Nat.succ ℓ) x₁ x₂ → @CoList.Approx.Agree α (Nat.succ ℓ) ℓ' x₂ x₃ → @CoList.Approx.Agree α ℓ ℓ' x₁ x₃
  | @Agree.«⋯» α (Nat.succ Nat.zero) _, _ => @Agree.«⋯» α ℓ' x₃
  | _, _ => sorry

#print CoList.Approx.Agree.trans'

coinductive Tree.{u} (α : Type u) : Type u
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α
  | node' : Tree α → Tree α → Tree α

/-
def CoNat.ofNat₁ : Nat → CoNat
  | .zero => .zero
  | .succ n => .succ (ofNat₁ n)

def CoNat.ofNat₂ : Nat → CoNat :=
  corec λ | .zero => .zero | .succ n => .succ n

theorem CoNat.ofNat₁_eq_ofNat₂ : ofNat₁ n = ofNat₂ n := by
  apply Subtype.eq
  funext ℓ
  induction n generalizing ℓ with
  | zero => cases ℓ <;> rfl
  | succ d ih =>
    cases ℓ with
    | zero => rfl
    | succ ℓ => exact congrArg _ <| ih ℓ

def CoNat.add (a b : CoNat) : CoNat :=
  corec (λ (a, b) =>
    match b.unfold with
    | .zero =>
      match a.unfold with
      | .zero => .zero
      | .succ a => .succ (a, b)
    | .succ b => .succ (a, b)
  ) (a, b)

theorem CoNat.add_zero : add a zero = a := by
  apply Subtype.eq
  funext ℓ
  dsimp [add, corec]
  induction ℓ with
  | zero => cases a.val .zero; rfl
  | succ ℓ ih =>
    dsimp [add, corec, zero, succ]
    sorry

def CoNat.toNat : Nat → CoNat → Option Nat
  | .zero, _ => none
  | .succ m, n =>
    match n.unfold with
    | .zero => some .zero
    | .succ n => n.toNat m |>.map .succ

theorem CoNat.add_ofNat₁ : add (ofNat₁ a) (ofNat₁ b) = ofNat₁ (a + b) := by
  apply Subtype.eq
  funext ℓ
  induction b generalizing ℓ with
  | zero =>
    dsimp only [ofNat₁, ofNat₂, corec, zero, succ, add]
    dsimp
    induction ℓ with
    | zero =>
      dsimp
      sorry
    | succ ℓ ih =>
      sorry
  | succ b ih =>
    sorry

theorem CoNat.add_ofNat₂ : add (ofNat₂ a) (ofNat₂ b) = ofNat₂ (a + b) := by
  apply Subtype.eq
  funext ℓ
  induction b generalizing ℓ with
  | zero =>
    dsimp only [ofNat₁, ofNat₂, corec, zero, succ, add]
    dsimp
    induction ℓ with
    | zero => rfl
    | succ ℓ ih =>
      dsimp
      sorry
  | succ b ih =>
    sorry

open TSyntax.Compat in
variable (n : Name) in
partial def replaceGuardedCalls (ctx : Bool) : Syntax → MacroM (Bool × Syntax)
  | `($f $as*) => do
    let (bf, f) ← replaceGuardedCalls ctx f
    let (bas, as) := Array.unzip <| ← as.mapM <| replaceGuardedCalls true
    if f.isIdent && f.getId.isSuffixOf n then
      if bas.any id then throw <| .error f "nested recursive unsupported"
      unless ctx do throw <| .error f "unguarded recursive call"
      return (true, ← `(.inl ⟨$as,*, ()⟩))
    if bas.any id then
      unless f.isIdent do throw <| .error f "not a constructor"
      let f := mkIdent f.getId.getString
      return (bf, ← `(.inl (.$f $as*)))
    return (bf, ← `($f $as*))
  | `(($t)) => do
    let (bt, t) ← replaceGuardedCalls ctx t
    return (bt, ← `(($t)))
  | stx =>
    match stx with
    | .node info kind args => return (false, .node info kind <| ← args.mapM λ arg => return (← replaceGuardedCalls false arg).snd)
    | stx => return (false, stx)

def matchAlts := Lean.Parser.Term.matchAlts

syntax (Parser.Command.unsafe)? "codef " ident bracketedBinder* " : " term matchAlts : command

macro_rules
  | `($[$safety:unsafe]? codef $n $b* : $t $[| $l,* => $rs]*) => do
    let (args, retTy) := splitDepArrows t
    let Pattern ← `($(mkIdent <| (appHead retTy).raw.getId ++ `Pattern) $(appTail retTy)*)
    let (args, tys) := args.unzip
    let ty ← `(Σ' $[($args : $tys)]*, Unit)
    let rs' : Array Term ← rs.mapM λ r => return ⟨(← replaceGuardedCalls n.getId false r.raw).snd⟩
    let xs ← args.mapM λ _ => return mkIdent <| ← Elab.Term.mkFreshBinderName
    `($[$safety:unsafe]? def $n $b* : $t := @λ $xs* =>
        have : Coe $retTy ($ty ⊕ $retTy) := ⟨.inr⟩
        have : Coe $retTy ($Pattern ($ty ⊕ $retTy) ⊕ $retTy) := ⟨.inr⟩
        .codef (λ ⟨$xs,*, _⟩ => match $[$xs:ident],* with $[| $l,* => $rs']*) (⟨$xs,*, ()⟩ : $ty))

-- TODO: generated codef def lemma

coinductive Stream'
  | cons : Nat → Stream' → Stream'

def cases {motive : Thunk (α ⊕ β) → Sort u} (inl : ∀ x, motive (.pure (.inl x))) (inr : ∀ y, motive (.pure (.inr y))) t : motive t :=
  (id rfl : .pure t.get = t) ▸
  match t.get with
  | .inl x => inl x
  | .inr x => inr x

def Stream'.nth (n : Nat) (s : Stream') : Nat :=
  let ⟨hd, tl⟩ := s.unfold
  match n with
  | .zero => hd
  | .succ n => nth n tl

unsafe def Stream'.Impl.nth (n : Nat) (s : Stream'.Impl) : Nat :=
  let ⟨hd, tl⟩ := s.unfold
  match n with
  | .zero => hd
  | .succ n => nth n tl

codef fib : Nat → Nat → Stream'
  | a, b => Stream'.cons (dbgTraceVal a) (fib b (a + b))

#eval (fib 0 1).nth 6

unsafe codef fib' : Nat → Nat → Stream'.Impl
  | a, b => Stream'.Impl.cons (dbgTraceVal a) (fib' b (a + b))

#eval (fib' 0 1).nth 6

theorem fib_def a b : fib a b = match a, b with | a, b => Stream'.cons a (fib b (a + b)) := by
  apply Stream'.unfold.inj
  rw [fib, Stream'.unfold.codef]
  rfl

codef count : Nat → Stream'
  | n => Stream'.cons n (count n.succ)

theorem count_def : count n = .cons n (count n.succ) :=
  Stream'.unfold.inj <| by rw [count]; apply Stream'.unfold.codef

coinductive Partial (α : Type u) : Type u
  | pure : α → Partial α
  | delay : Partial α → Partial α

coinductive Tree (α : Type u) : Type u
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α
  | node' : Tree α → Tree α → Tree α

codef Partial.bind (f : α → Partial β) : Partial α → Partial β
  | x =>
    match x.unfold with
    | .pure x => f x
    | .delay x => delay (bind x)

theorem Partial.bind.def (f : α → Partial β) x : bind f x = match x with | x => match x.unfold with | .pure x => f x | .delay x => delay (bind f x) := by
  apply unfold.inj
  rw [bind, unfold.codef]
  dsimp
  cases unfold x
  all_goals rfl

instance : Monad Partial where
  pure := .pure
  bind x := x.bind

codef Tree.ofCoList : CoList α → Tree α
  | x =>
    match x.unfold with
    | .nil => @node' α leaf leaf
    | .cons hd tl => node hd (@leaf α) (ofCoList tl)

example : Partial.pure x >>= f = f x := by
  dsimp [pure, bind]
  rw [Partial.bind.def]
  rfl

example : Partial.delay x >>= f = Partial.delay (x >>= f) := by
  dsimp [pure, bind]
  rw [Partial.bind.def]
  rfl

instance : LawfulMonad Partial where
  map_const := rfl
  id_map x := by
    apply Subtype.eq
    funext ℓ
    simp [Functor.map, Partial.corec]
    induction ℓ generalizing x with
    | zero => cases x.val 0; simp
    | succ ℓ ih =>
      simp
      split
      next h =>
        simp [Partial.cases] at h
        split at h
        . cases h
        . cases h
      next A x' h =>
        clear A
        cases x' with
        | inl x' =>
          simp [ih]
          sorry
        | inr x' =>
          simp
          sorry
  seqLeft_eq _ _ := sorry
  seqRight_eq _ _ := sorry
  pure_seq _ _ := sorry
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind x f := by
    dsimp only [pure, bind]
    rw [Partial.corec'_yield]
    dsimp
  bind_assoc _ _ _ := sorry

--#check Partial.corec
-/
