import Mathlib.Data.Nat.Basic

syntax (name := coinductive) "coinductive " declId bracketedBinder* (" : " term)? (ppLine "| " ident " : " term)* : command

open Lean

abbrev CommandMacroM := StateT (Array Command) MacroM

def CommandMacroM.push (c : CommandMacroM Command) : CommandMacroM Unit :=
  do modify (·.push (← c))

def CommandMacroM.run (x : CommandMacroM Unit) : MacroM Command := do
  let (_, cs) ← x #[]
  return ⟨mkNullNode cs⟩

partial def splitArrows (t : Term) (args : Array Term := #[]) : Array Term × Term :=
  match t with
  | `($arg → $ret) => splitArrows ret (args.push arg)
  | _ => (args, t)

partial def joinArrows : List Term → Term → MacroM Term
  | [], r => return r
  | l :: ls, r => do `($l → $(← joinArrows ls r))

partial def appHead : Term → Term
  | `($fn $_) => appHead fn
  | t => t

structure CtorView where
  id : Ident
  argTypes : Array (Term × Bool)
  retType : Term

structure CoInductiveView where
  id : Ident
  levels : Array Ident
  binders : TSyntaxArray ``Parser.Term.bracketedBinder
  params : Array Ident
  type : Term
  ctors : Array CtorView

def CoInductiveView.ofSyntax : Syntax → MacroM CoInductiveView
  | `(coinductive $id$[.{$levels?,*}]? $binders* $[: $type?]? $[| $ids : $types]*) => do
    let params := binders.map Elab.Command.getBracketedBinderIds |>.flatten.map mkIdent
    let ty ← `(@$id $params*)
    return {
      id
      levels := match levels? with | some levels => levels.getElems | none => #[]
      binders
      params
      type := type?.getD <| ← `(Type _)
      ctors := ids.zipWith types λ ctorId type =>
        let (argTypes, _) := splitArrows type
        let argTypes := argTypes.map λ argType =>
          if (appHead argType).raw.matchesIdent id.getId
          then (ty, true)
          else (argType, false)
        { id := ctorId, argTypes, retType := ty }
    }
  | _ => Macro.throwUnsupported

@[macro «coinductive»]
def expandCoInductive : Macro := λ stx => CommandMacroM.run do
  let view ← CoInductiveView.ofSyntax stx
  let ctors := view.ctors.map (·.id)

  let Approx := mkIdent <| view.id.getId ++ `Approx
  let «⋯» := mkIdent `«⋯»
  let types ← view.ctors.mapM λ ctor => do
    let args ← ctor.argTypes.mapM λ
      | (arg, false) => return arg
      | (_, true) => `(@$Approx $view.params* ℓ)
    joinArrows args.toList (← `(@$Approx $view.params* (.succ ℓ)))
  CommandMacroM.push `(
    inductive $Approx.{$view.levels,*} $view.binders* : Nat → $view.type
      | $«⋯»:ident : @$Approx $view.params* .zero
    $[| $ctors:ident {ℓ} : $types]*
  )

  let Agree := mkIdent <| view.id.getId ++ `Agree
  let (binders, types) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.argTypes.mapM λ
      | (_, false) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (#[x], #[], x, x)
      | (_, true) => do
        let x₁ := mkIdent <| ← Elab.Term.mkFreshBinderName
        let x₂ := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (#[x₁, x₂], #[← `($Agree $x₁ $x₂)], x₁, x₂)
    let (ihs, args) := args.unzip
    let (args₁, args₂) := args.unzip
    return (binders.flatten, ← joinArrows ihs.flatten.toList <| ← `($Agree (.$ctor.id $args₁*) (.$ctor.id $args₂*)))
  CommandMacroM.push `(
    inductive $Agree {$view.params*} : ∀ {ℓ₁ ℓ₂}, @$Approx $view.params* ℓ₁ → @$Approx $view.params* ℓ₂ → Prop
      | $«⋯»:ident {x} : $Agree .«⋯» x
    $[| $ctors:ident {$binders*} : $types]*
  )

  let Pattern := mkIdent <| view.id.getId ++ `Pattern
  let types ← view.ctors.mapM λ ctor => do
    let args ← ctor.argTypes.mapM λ
      | (arg, false) => return arg
      | (_, true) => `(α)
    joinArrows args.toList (← `(@$Pattern $view.params* α))
  CommandMacroM.push `(
    inductive $Pattern.{u, $view.levels,*} $view.binders* (α : Type u)
    $[| $ctors:ident : $types]*
  )

  let map := mkIdent <| Pattern.getId ++ `map
  let mapApprox := mkIdent <| Pattern.getId ++ `mapApprox
  let mapAgree := mkIdent <| Pattern.getId ++ `mapAgree
  let (binders, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.argTypes.mapM λ
      | (_, false) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, x, #[])
      | (_, true) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, ← `(f $x), #[← `(h $x)])
    let (args₁, args₂) := args.unzip
    return (← `($ctor.id $binders*), ← `(.$ctor.id $args₁*), ← `(.$ctor.id $args₂.flatten*))
  let (args₁, args₂) := args.unzip
  CommandMacroM.push `(
    @[simp]
    def $map {$view.params* α β} (f : α → β) : @$Pattern $view.params* α → @$Pattern $view.params* β
    $[| $binders => $args₁]*
    @[simp]
    def $mapApprox {$view.params* α ℓ} (f : α → @$Approx $view.params* ℓ) : @$Pattern $view.params* α → @$Approx $view.params* ℓ.succ
    $[| $binders => $args₁]*
    theorem $mapAgree {$view.params* α ℓ₁ ℓ₂} {f : α → @$Approx $view.params* ℓ₁} {g : α → @$Approx $view.params* ℓ₂} {x} (h : ∀ x, $Agree (f x) (g x)) : $Agree ($mapApprox f x) ($mapApprox g x) :=
      match x with
      $[| $binders => $args₂]*
  )

  let corec := mkIdent <| view.id.getId ++ `corec
  CommandMacroM.push `(
    def $view.id.{$view.levels,*} $view.binders* := { f : ∀ ℓ, @$Approx $view.params* ℓ // ∀ ℓ, $Agree (f ℓ) (f ℓ.succ) }
    def $corec {$view.params* α} (f : α → @$Pattern $view.params* α) (x : α) : @$view.id $view.params* where
      val ℓ := ℓ.rec (λ _ => .«⋯») (λ _ ih x => $mapApprox ih (f x)) x
      property ℓ := ℓ.rec (λ _ => .«⋯») (λ _ ih _ => $mapAgree ih) x
  )

  let wrappers ← CommandMacroM.run do
    for ctor in view.ctors do
      let (binders, args) := Array.unzip <| ← ctor.argTypes.mapM λ
        | (_, false) => do
          let x := mkIdent <| ← Elab.Term.mkFreshBinderName
          return (x, x, #[])
        | (_, true) => do
          let x := mkIdent <| ← Elab.Term.mkFreshBinderName
          return (x, ← `($(x).val ℓ), #[← `($(x).property ℓ)])
      let (args₁, args₂) := args.unzip
      let type ← joinArrows (ctor.argTypes.map (·.fst)).toList ctor.retType
      CommandMacroM.push `(
        def $ctor.id {$view.params*} : $type := λ $binders* => {
          val := λ | .zero => .«⋯» | .succ ℓ => .$ctor.id $args₁*
          property := λ | .zero => .«⋯» | .succ ℓ => .$ctor.id $args₂.flatten*
        }
      )
  CommandMacroM.push `(
    namespace $view.id
    $wrappers
    end $view.id
  )

  let refl := mkIdent <| Agree.getId ++ `refl
  let (binders, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders, args) := Array.unzip <| ← ctor.argTypes.mapM λ
      | (_, false) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, #[])
      | (_, true) => do
        let x := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (x, #[← `($refl)])
    return (← `(.$ctor.id $binders*), ← `(.$ctor.id $args.flatten*))
  CommandMacroM.push `(
    theorem $refl {$view.params* ℓ} : ∀ {x : @$Approx $view.params* ℓ}, $Agree x x
      | .«⋯» => .«⋯»
      $[| $binders => $args]*
  )

  let trans := mkIdent <| Agree.getId ++ `trans
  let (binders₁, args) := Array.unzip <| ← view.ctors.mapM λ ctor => do
    let (binders₁, args) := Array.unzip <| ← ctor.argTypes.mapM λ
      | (_, false) => return (#[], #[], #[])
      | (_, true) => do
        let x₁ := mkIdent <| ← Elab.Term.mkFreshBinderName
        let x₂ := mkIdent <| ← Elab.Term.mkFreshBinderName
        return (#[x₁], #[x₂], #[← `($trans $x₁ $x₂)])
    let (binders₂, args) := args.unzip
    return (← `(.$ctor.id $binders₁.flatten*), ← `(.$ctor.id $binders₂.flatten*), ← `(.$ctor.id $args.flatten*))
  let (binders₂, args) := args.unzip
  CommandMacroM.push `(
    theorem $trans {$view.params* ℓ ℓ'} {x₁ : @$Approx $view.params* ℓ} {x₂ : @$Approx $view.params* ℓ.succ} {x₃ : @$Approx $view.params* ℓ'} : $Agree x₁ x₂ → $Agree x₂ x₃ → $Agree x₁ x₃
      | .«⋯», _ => .«⋯»
    $[| $binders₁, $binders₂ => $args]*
  )

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

  let unfold := mkIdent <| view.id.getId ++ `unfold
  CommandMacroM.push `(
    def $unfold {$view.params*} : @$view.id $view.params* → @$Pattern $view.params* (@$view.id $view.params*) :=
      $cases $(← ctors.mapM λ ctor => `(.$ctor))*
  )

coinductive CoNat
  | zero : CoNat
  | succ : CoNat → CoNat

coinductive CoList (α : Type u)
  | nil : CoList
  | cons : α → CoList → CoList

@[simp]
theorem CoNat.cases_zero zero succ : @cases motive zero succ .zero = zero := rfl

@[simp]
theorem CoNat.cases_succ zero succ n : @cases motive zero succ (.succ n) = succ n := rfl

@[simp]
theorem CoNat.unfold_zero : unfold zero = .zero := rfl

@[simp]
theorem CoNat.unfold_succ n : unfold (succ n) = .succ n := rfl

@[simp]
theorem CoList.cases_nil nil cons : @cases α motive nil cons .nil = nil := rfl

@[simp]
theorem CoList.cases_cons nil cons x xs : @cases α motive nil cons (.cons x xs) = cons x xs := rfl

@[simp]
theorem CoList.unfold_nil : @unfold α nil = .nil := rfl

@[simp]
theorem CoList.unfold_cons x xs : @unfold α (cons x xs) = .cons x xs := rfl

@[simp]
theorem CoNat.unfold_corec f x : unfold (@corec α f x) = (f x).map (corec f) := by
  unfold Pattern.map
  split <;> rename_i h
    <;> simp [unfold, cases, corec]
    <;> split <;> rename_i h' <;> cases h ▸ h'
    <;> congr
  funext ℓ
  split <;> rename_i h' <;> cases h ▸ h'
  rfl

@[simp]
theorem CoList.unfold_corec : unfold (corec f x) = (f x).map (corec f) := by
  unfold Pattern.map
  split <;> rename_i h
    <;> simp [unfold, cases, corec]
    <;> split <;> rename_i h' <;> cases h ▸ h'
    <;> congr
  funext ℓ
  split <;> rename_i h' <;> cases h ▸ h'
  rfl

theorem dcongrArg.{u, v} {α : Sort u} {β : α → Sort v} {a₁ a₂ : α} (f : ∀ x, β x) (h : a₁ = a₂) : HEq (f a₁) (f a₂) :=
  by cases h; rfl

theorem CoNat.cases_corec zero succ f x : @cases motive zero succ (@corec α f x) = match h : f x with | .zero => (Subtype.eq <| funext λ | .zero => rfl | .succ ℓ => by simp [corec, h, CoNat.zero] : corec f x = .zero) ▸ zero | .succ x' => (Subtype.eq <| funext λ | .zero => rfl | .succ ℓ => by simp [corec, h, CoNat.succ]: corec f x = .succ (corec f x')) ▸ succ (corec f x') := by
  split
    <;> rename_i h
    <;> simp [cases, corec]
    <;> split <;> rename_i h' <;> cases h ▸ h'
  . rfl
  . rename_i x'
    generalize hA : succ _ = A
    generalize hB : succ _ = B
    sorry

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
  sorry

/-
inductive CoNat'
  | zero : CoNat'
  | succ' : Thunk CoNat' → CoNat'
  deriving Inhabited

def CoNat'.succ (n : CoNat') : CoNat' :=
  succ' n

def CoNat'.cases {motive : CoNat' → Sort u} (zero : motive zero) (succ : ∀ n, motive (succ n)) n : motive n :=
  match n with
  | .zero => zero
  | .succ' n => succ n.get

partial def CoNat'.corec (f : α → Option α) (x : α) : CoNat' :=
  match f x with
  | none => zero
  | some x => succ' (corec f x)

structure Hide (α : Type u) where
  x : α

instance : Repr (Hide α) where
  reprPrec _ _ := "⟨hidden⟩"

#eval 2 + 2
#eval Hide.mk (CoNat'.corec some ())
#eval 2 + 2
-/
