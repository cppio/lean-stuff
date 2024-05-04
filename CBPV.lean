import Common.Meta

partial def rename (names : Lean.HashMap Lean.Name Lean.Ident) : Lean.Syntax → Lean.Syntax
  | .node info kind args => .node info kind <| args.map <| rename names
  | stx@(.ident _ _ name _) =>
    if let some id := names.find? name then
      id
    else
      stx
  | stx => stx

partial def replaceRecCalls (fns : Lean.HashMap Lean.Name (Lean.HashMap Lean.Name Lean.Ident)) : Lean.Macro
  | .node info kind args => do
    if kind == ``Lean.Parser.Term.app then
      if let #[f, .node .none `null as] := args then
        if let some a := as.get? 0 then
          if let some aps := fns.find? f.getId then
            if let some ap := aps.find? a.getId
            then return Lean.Syntax.mkApp ap <| .mk <| ← (as.extract 1 as.size).mapM (replaceRecCalls fns)
            else Lean.Macro.throwErrorAt f "invalid recursive call"
    return .node info kind <| ← args.mapM (replaceRecCalls fns)
  | stx =>
    if fns.contains stx.getId
    then Lean.Macro.throwErrorAt stx "invalid recursive call"
    else return stx

def notEnd := Lean.Parser.notSymbol "end"
syntax "mutual" "rec" (notEnd command)+ "end" : command

initialize Lean.Meta.registerGetUnfoldEqnFn fun declName => Lean.Elab.Eqns.getUnfoldFor? declName fun _ => none

abbrev matchAlt := Lean.Parser.Term.matchAlt

def parseArm : Lean.TSyntax ``Lean.Parser.Term.matchAlt → Lean.MacroM (Lean.Ident × Array Lean.Ident × Lean.Term)
  | `(matchAlt| | .$ctor $args:ident* => $rhs) => return (ctor, args, rhs)
  | `(matchAlt| | .$ctor              => $rhs) => return (ctor, #[],  rhs)
  | stx                                        => Lean.Macro.throwErrorAt stx "invalid arm"

def processRecArgs (fnP fnN : Lean.Ident) : (Lean.Ident × Array Lean.Ident × Lean.Term) × Array (Option Lean.Ident) → Lean.MacroM Lean.Term
  | ((_, args, rhs), fns) => do
  let args_fns := args.zipWith fns fun arg fn => (arg, fn.map fun fn => (fn, Lean.mkIdent <| toString <| fn.getId ++ arg.getId))
  let fnArgs := args_fns.filterMap (·.2.map (·.2))
  `(fun $args* $fnArgs:ident* => $(⟨← replaceRecCalls (.ofList [
    (fnP.getId, .ofList <| Array.toList <| args_fns.filterMap fun (arg, fn) => if fn.map (·.1) == fnP then (arg.getId, fn.get!.2) else none),
    (fnN.getId, .ofList <| Array.toList <| args_fns.filterMap fun (arg, fn) => if fn.map (·.1) == fnN then (arg.getId, fn.get!.2) else none)
  ]) rhs⟩))

mutual

inductive TypP
  | void
  | unit
  | sum  (A₁ A₂ : TypP)
  | prod (A₁ A₂ : TypP)
  | U    (X : TypN)

inductive TypN
  | unit
  | prod (X₁ X₂ : TypN)
  | arr  (A : TypP) (X : TypN)
  | F    (A : TypP)

end

macro_rules
  | `(
    mutual rec

    $[@[$attrP,*]]?
    def $fnP:ident : ($A:ident : TypP) → $motiveP
      $altP:matchAlt*

    $[@[$attrN,*]]?
    def $fnN:ident : ($X:ident : TypN) → $motiveN
      $altN:matchAlt*

    end
  ) => do
  let armP ← altP.mapM parseArm
  let armN ← altN.mapM parseArm

  let #[`void, `unit, `sum, `prod, `U] := armP.map fun (ctor, _) => ctor.getId
    | Lean.Macro.throwError "invalid arms"

  let #[`unit, `prod, `arr, `F] := armN.map fun (ctor, _) => ctor.getId
    | Lean.Macro.throwError "invalid arms"

  let recArgs := #[← `(fun $A => $motiveP), ← `(fun $X => $motiveN)]
    ++ (← armP.zip #[
      #[],
      #[],
      #[some fnP, fnP],
      #[fnP, fnP],
      #[fnN]
    ] |>.mapM <| processRecArgs fnP fnN)
    ++ (← armN.zip #[
      #[],
      #[some fnN, fnN],
      #[fnP, fnN],
      #[fnP]
    ] |>.mapM <| processRecArgs fnP fnN)

  let fnP_imp := Lean.mkIdent <| fnP.getId.str "_unsafe_rec_"
  let fnN_imp := Lean.mkIdent <| fnN.getId.str "_unsafe_rec_"
  let imps := .ofList [(fnP.getId, fnP_imp), (fnN.getId, fnN_imp)]

  let fnP_eqs := armP.map fun (ctor, _, _) => Lean.mkIdent <| fnP.getId.str s!"_eq_{ctor.getId}"
  let fnN_eqs := armN.map fun (ctor, _, _) => Lean.mkIdent <| fnN.getId.str s!"_eq_{ctor.getId}"

  let registerEqnThms := Lean.mkCIdent <| (`_private.Lean.Meta.Eqns).num 0 ++ `Lean.Meta.registerEqnThms

  let fnP_unfold := Lean.mkIdent <| fnP.getId.str "_unfold"
  let fnN_unfold := Lean.mkIdent <| fnN.getId.str "_unfold"

  `(
    mutual

    unsafe def $fnP_imp : ($A : TypP) → $motiveP
      $(altP.map fun alt => ⟨rename imps alt⟩):matchAlt*

    unsafe def $fnN_imp : ($X : TypN) → $motiveN
      $(altN.map fun alt => ⟨rename imps alt⟩):matchAlt*

    end

    @[implemented_by $fnP_imp]
    def $fnP : ($A : TypP) → $motiveP :=
      @TypP.rec $recArgs*

    @[implemented_by $fnN_imp]
    def $fnN : ($X : TypN) → $motiveN :=
      @TypN.rec $recArgs*

    def $(Lean.mkIdent <| Lean.Meta.mkSmartUnfoldingNameFor fnP.getId) ($A : TypP) : $motiveP :=
      annotate% `sunfoldMatch
      match $A:ident with
      $(← armP.mapM fun (ctor, args, rhs) => return ⟨← `(matchAlt| | .$ctor $args* => annotate% `sunfoldMatchAlt $rhs)⟩):matchAlt*

    def $(Lean.mkIdent <| Lean.Meta.mkSmartUnfoldingNameFor fnN.getId) ($X : TypN) : $motiveN :=
      annotate% `sunfoldMatch
      match $X:ident with
      $(← armN.mapM fun (ctor, args, rhs) => return ⟨← `(matchAlt| | .$ctor $args* => annotate% `sunfoldMatchAlt $rhs)⟩):matchAlt*

    $(⟨Lean.mkNullNode <| ← (fnP_eqs.zip armP).mapM fun (fnP_eq, ctor, args, rhs) => `(private theorem $fnP_eq {$args*} : $fnP (.$ctor $args*) = $rhs := rfl)⟩):command
    $(⟨Lean.mkNullNode <| ← (fnN_eqs.zip armN).mapM fun (fnN_eq, ctor, args, rhs) => `(private theorem $fnN_eq {$args*} : $fnN (.$ctor $args*) = $rhs := rfl)⟩):command

    run_elab $registerEqnThms:ident ``$fnP #[$[``$fnP_eqs],*]
    run_elab $registerEqnThms:ident ``$fnN #[$[``$fnN_eqs],*]

    def $fnP_unfold ($A : TypP) : $fnP $A = match $A:ident with $altP:matchAlt* :=
      match $A:ident with
      $(← armP.mapM fun (ctor, args, _) => return ⟨← `(matchAlt| | .$ctor $args* => rfl)⟩):matchAlt*

    def $fnN_unfold ($X : TypN) : $fnN $X = match $X:ident with $altN:matchAlt* :=
      match $X:ident with
      $(← armN.mapM fun (ctor, args, _) => return ⟨← `(matchAlt| | .$ctor $args* => rfl)⟩):matchAlt*

    run_elab Lean.modifyEnv fun env => Lean.Elab.Eqns.unfoldEqnExt.modifyState env fun s => { s with map := s.map.insert ``$fnP ``$fnP_unfold }
    run_elab Lean.modifyEnv fun env => Lean.Elab.Eqns.unfoldEqnExt.modifyState env fun s => { s with map := s.map.insert ``$fnN ``$fnN_unfold }

    attribute [$(attrP.getD ⟨#[]⟩),*] $fnP
    attribute [$(attrN.getD ⟨#[]⟩),*] $fnN
  )

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : TypP)

inductive Var (A : TypP) : (Γ : Ctx) → Type
  | zero               : Var A (.cons Γ A)
  | succ (x : Var A Γ) : Var A (.cons Γ A')

mutual

inductive ExpP : (Γ : Ctx) → (A : TypP) → Type
  | var  (x : Var A Γ)                     : ExpP Γ A
  | triv                                   : ExpP Γ .unit
  | inl  (V : ExpP Γ A₁)                   : ExpP Γ (.sum A₁ A₂)
  | inr  (V : ExpP Γ A₂)                   : ExpP Γ (.sum A₁ A₂)
  | pair (V₁ : ExpP Γ A₁) (V₂ : ExpP Γ A₂) : ExpP Γ (.prod A₁ A₂)
  | susp (C : ExpN Γ X)                    : ExpP Γ (.U X)

inductive ExpN : (Γ : Ctx) → (X : TypN) → Type
  | abort (V : ExpP Γ .void)                                                            : ExpN Γ X
  | check (V : ExpP Γ .unit) (C : ExpN Γ X)                                             : ExpN Γ X
  | case  (V : ExpP Γ (.sum A₁ A₂)) (C₁ : ExpN (Γ.cons A₁) X) (C₂ : ExpN (Γ.cons A₂) X) : ExpN Γ X
  | split (V : ExpP Γ (.prod A₁ A₂)) (C : ExpN (Γ.cons A₁ |>.cons A₂) X)                : ExpN Γ X
  | force (V : ExpP Γ (.U X))                                                           : ExpN Γ X

  | triv                                               : ExpN Γ .unit
  | pair  (C₁ : ExpN Γ X₁) (C₂ : ExpN Γ X₂)            : ExpN Γ (.prod X₁ X₂)
  | prl   (C : ExpN Γ (.prod X₁ X₂))                   : ExpN Γ X₁
  | prr   (C : ExpN Γ (.prod X₁ X₂))                   : ExpN Γ X₂
  | lam   (C : ExpN (Γ.cons A) X)                      : ExpN Γ (.arr A X)
  | ap    (C : ExpN Γ (.arr A X)) (V : ExpP Γ A)       : ExpN Γ X
  | ret   (V : ExpP Γ A)                               : ExpN Γ (.F A)
  | bind  (C : ExpN Γ (.F A)) (C₁ : ExpN (Γ.cons A) X) : ExpN Γ X

end

macro_rules
  | `(
    mutual rec

    $[@[$attrP,*]]?
    def $fnP:ident : ($V:ident : ExpP $ΓP:ident $A:ident) → $motiveP
      $altP:matchAlt*

    $[@[$attrN,*]]?
    def $fnN:ident : ($C:ident : ExpN $ΓN:ident $X:ident) → $motiveN
      $altN:matchAlt*

    end
  ) => do
  let armP ← altP.mapM parseArm
  let armN ← altN.mapM parseArm

  let #[`var, `triv, `inl, `inr, `pair, `susp] := armP.map fun (ctor, _) => ctor.getId
    | Lean.Macro.throwError "invalid arms"

  let #[`abort, `check, `case, `split, `force, `triv, `pair, `prl, `prr, `lam, `ap, `ret, `bind] := armN.map fun (ctor, _) => ctor.getId
    | Lean.Macro.throwError "invalid arms"

  let recArgs := #[← `(fun $ΓP $A $V => $motiveP), ← `(fun $ΓN $X $C => $motiveN)]
    ++ (← armP.zip #[
      #[none],
      #[],
      #[fnP],
      #[fnP],
      #[fnP, fnP],
      #[fnN]
    ] |>.mapM <| processRecArgs fnP fnN)
    ++ (← armN.zip #[
      #[some fnP],
      #[fnP, fnN],
      #[fnP, fnN, fnN],
      #[fnP, fnN],
      #[fnP],
      #[],
      #[fnN, fnN],
      #[fnN],
      #[fnN],
      #[fnN],
      #[fnN, fnP],
      #[fnP],
      #[fnN, fnN]
    ] |>.mapM <| processRecArgs fnP fnN)

  let fnP_imp := Lean.mkIdent <| fnP.getId.str "_unsafe_rec_"
  let fnN_imp := Lean.mkIdent <| fnN.getId.str "_unsafe_rec_"
  let imps := .ofList [(fnP.getId, fnP_imp), (fnN.getId, fnN_imp)]

  let fnP_eqs := armP.map fun (ctor, _, _) => Lean.mkIdent <| fnP.getId.str s!"_eq_{ctor.getId}"
  let fnN_eqs := armN.map fun (ctor, _, _) => Lean.mkIdent <| fnN.getId.str s!"_eq_{ctor.getId}"

  let registerEqnThms := Lean.mkCIdent <| (`_private.Lean.Meta.Eqns).num 0 ++ `Lean.Meta.registerEqnThms

  let fnP_unfold := Lean.mkIdent <| fnP.getId.str "_unfold"
  let fnN_unfold := Lean.mkIdent <| fnN.getId.str "_unfold"

  `(
    mutual

    unsafe def $fnP_imp {$ΓP $A} : ($V : ExpP $ΓP $A) → $motiveP
      $(altP.map fun alt => ⟨rename imps alt⟩):matchAlt*

    unsafe def $fnN_imp {$ΓN $X} : ($C : ExpN $ΓN $X) → $motiveN
      $(altN.map fun alt => ⟨rename imps alt⟩):matchAlt*

    end

    @[implemented_by $fnP_imp]
    def $fnP : ∀ {$ΓP $A}, ($V : ExpP $ΓP $A) → $motiveP :=
      @ExpP.rec $recArgs*

    @[implemented_by $fnN_imp]
    def $fnN : ∀ {$ΓN $X}, ($C : ExpN $ΓN $X) → $motiveN :=
      @ExpN.rec $recArgs*

    def $(Lean.mkIdent <| Lean.Meta.mkSmartUnfoldingNameFor fnP.getId) {$ΓP $A} ($V : ExpP $ΓP $A) : $motiveP :=
      annotate% `sunfoldMatch
      match $V:ident with
      $(← armP.mapM fun (ctor, args, rhs) => return ⟨← `(matchAlt| | .$ctor $args* => annotate% `sunfoldMatchAlt $rhs)⟩):matchAlt*

    def $(Lean.mkIdent <| Lean.Meta.mkSmartUnfoldingNameFor fnN.getId) {$ΓN $X} ($C : ExpN $ΓN $X) : $motiveN :=
      annotate% `sunfoldMatch
      match $C:ident with
      $(← armN.mapM fun (ctor, args, rhs) => return ⟨← `(matchAlt| | .$ctor $args* => annotate% `sunfoldMatchAlt $rhs)⟩):matchAlt*

    /-
    $(⟨Lean.mkNullNode <| ← (fnP_eqs.zip armP).mapM fun (fnP_eq, ctor, args, rhs) => `(private theorem $fnP_eq {$args*} : $fnP (.$ctor $args*) = $rhs := rfl)⟩):command
    $(⟨Lean.mkNullNode <| ← (fnN_eqs.zip armN).mapM fun (fnN_eq, ctor, args, rhs) => `(private theorem $fnN_eq {$args*} : $fnN (.$ctor $args*) = $rhs := rfl)⟩):command

    run_elab $registerEqnThms:ident ``$fnP #[$[``$fnP_eqs],*]
    run_elab $registerEqnThms:ident ``$fnN #[$[``$fnN_eqs],*]
    -/

    def $fnP_unfold {$ΓP $A} ($V : ExpP $ΓP $A) : @$fnP $ΓP $A $V = match $V:ident with $altP:matchAlt* :=
      match $V:ident with
      $(← armP.mapM fun (ctor, args, _) => return ⟨← `(matchAlt| | .$ctor $args* => rfl)⟩):matchAlt*

    def $fnN_unfold {$ΓN $X} ($C : ExpN $ΓN $X) : @$fnN $ΓN $X $C = match $C:ident with $altN:matchAlt* :=
      match $C:ident with
      $(← armN.mapM fun (ctor, args, _) => return ⟨← `(matchAlt| | .$ctor $args* => rfl)⟩):matchAlt*

    run_elab Lean.modifyEnv fun env => Lean.Elab.Eqns.unfoldEqnExt.modifyState env fun s => { s with map := s.map.insert ``$fnP ``$fnP_unfold }
    run_elab Lean.modifyEnv fun env => Lean.Elab.Eqns.unfoldEqnExt.modifyState env fun s => { s with map := s.map.insert ``$fnN ``$fnN_unfold }

    attribute [$(attrP.getD ⟨#[]⟩),*] $fnP
    attribute [$(attrN.getD ⟨#[]⟩),*] $fnN
  )

def Renaming (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → Var A Γ

namespace Renaming

@[simp]
def cons (γ : Renaming Γ Γ') : Renaming (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .zero
  | _, .succ x => .succ (γ x)

mutual rec

@[simp]
def renameP : (V : ExpP Γ' A) → ∀ {Γ}, (γ : Renaming Γ Γ') → ExpP Γ A
  | .var x      => fun γ => .var (γ x)
  | .triv       => fun _ => .triv
  | .inl V      => fun γ => .inl (renameP V γ)
  | .inr V      => fun γ => .inr (renameP V γ)
  | .pair V₁ V₂ => fun γ => .pair (renameP V₁ γ) (renameP V₂ γ)
  | .susp C     => fun γ => .susp (renameN C γ)

@[simp]
def renameN : (C : ExpN Γ' X) → ∀ {Γ}, (γ : Renaming Γ Γ') → ExpN Γ X
  | .abort V      => fun γ => .abort (renameP V γ)
  | .check V C    => fun γ => .check (renameP V γ) (renameN C γ)
  | .case V C₁ C₂ => fun γ => .case (renameP V γ) (renameN C₁ γ.cons) (renameN C₂ γ.cons)
  | .split V C    => fun γ => .split (renameP V γ) (renameN C γ.cons.cons)
  | .force V      => fun γ => .force (renameP V γ)

  | .triv       => fun _ => .triv
  | .pair C₁ C₂ => fun γ => .pair (renameN C₁ γ) (renameN C₂ γ)
  | .prl C      => fun γ => .prl (renameN C γ)
  | .prr C      => fun γ => .prr (renameN C γ)
  | .lam C      => fun γ => .lam (renameN C γ.cons)
  | .ap C V     => fun γ => .ap (renameN C γ) (renameP V γ)
  | .ret V      => fun γ => .ret (renameP V γ)
  | .bind C C₁  => fun γ => .bind (renameN C γ) (renameN C₁ γ.cons)

end

end Renaming

/-
set_option autoImplicit false

private theorem Renaming.renameP._eq_var {A Γ' x} : @Eq (haveI V := @ExpP.var A Γ' x; haveI Γ' := Γ'; haveI A := A; ∀ {Γ}, (γ : Renaming Γ Γ') → ExpP Γ A) (@Renaming.renameP _ _ (@ExpP.var A Γ' x)) (fun γ => .var (γ x)) := rfl
private theorem Renaming.renameP._eq_triv {Γ'} : @Eq (haveI V := @ExpP.triv Γ'; haveI Γ' := Γ'; haveI A := .unit; ∀ {Γ}, (γ : Renaming Γ Γ') → ExpP Γ A) (@Renaming.renameP _ _ (@ExpP.triv Γ')) (fun _ => .triv) := rfl
private theorem Renaming.renameP._eq_inl {Γ' A₁ A₂ V} : @Eq (haveI V := @ExpP.inl Γ' A₁ A₂ V; haveI Γ' := Γ'; haveI A := TypP.sum A₁ A₂; ∀ {Γ}, (γ : Renaming Γ Γ') → ExpP Γ A) (@Renaming.renameP _ _ (@ExpP.inl Γ' A₁ A₂ V)) (fun γ => .inl (renameP V γ)) := rfl
private theorem Renaming.renameP._eq_inr {Γ' A₂ A₁ V} : @Eq (haveI V := @ExpP.inr Γ' A₂ A₁ V; haveI Γ' := Γ'; haveI A := TypP.sum A₁ A₂; ∀ {Γ}, (γ : Renaming Γ Γ') → ExpP Γ A) (@Renaming.renameP _ _ (@ExpP.inr Γ' A₂ A₁ V)) (fun γ => .inr (renameP V γ)) := rfl

#check ExpP.var
#check ExpP.triv
#check ExpP.inl
#check ExpP.inr
#check ExpP.pair
#check ExpP.susp

#check ExpN.abort
#check ExpN.check
#check ExpN.case
#check ExpN.split
#check ExpN.force

#check ExpN.triv
#check ExpN.pair
#check ExpN.prl
#check ExpN.prr
#check ExpN.lam
#check ExpN.ap
#check ExpN.ret
#check ExpN.bind
-/

@[simp]
def ExpP.weaken (V : ExpP Γ A) : ExpP (Γ.cons A') A :=
  Renaming.renameP V fun _ => .succ

def Subst (Γ Γ' : Ctx) : Type :=
  ∀ {{A}}, (x : Var A Γ') → ExpP Γ A

namespace Subst

@[simp]
def cons (γ : Subst Γ Γ') : Subst (Γ.cons A) (Γ'.cons A)
  | _, .zero   => .var .zero
  | _, .succ x => .weaken (γ x)

mutual rec

@[simp]
def substP : (V : ExpP Γ' A) → ∀ {Γ}, (γ : Subst Γ Γ') → ExpP Γ A
  | .var x      => fun γ => γ x
  | .triv       => fun _ => .triv
  | .inl V      => fun γ => .inl (substP V γ)
  | .inr V      => fun γ => .inr (substP V γ)
  | .pair V₁ V₂ => fun γ => .pair (substP V₁ γ) (substP V₂ γ)
  | .susp C     => fun γ => .susp (substN C γ)

@[simp]
def substN : (C : ExpN Γ' X) → ∀ {Γ}, (γ : Subst Γ Γ') → ExpN Γ X
  | .abort V      => fun γ => .abort (substP V γ)
  | .check V C    => fun γ => .check (substP V γ) (substN C γ)
  | .case V C₁ C₂ => fun γ => .case (substP V γ) (substN C₁ γ.cons) (substN C₂ γ.cons)
  | .split V C    => fun γ => .split (substP V γ) (substN C γ.cons.cons)
  | .force V      => fun γ => .force (substP V γ)

  | .triv       => fun _ => .triv
  | .pair C₁ C₂ => fun γ => .pair (substN C₁ γ) (substN C₂ γ)
  | .prl C      => fun γ => .prl (substN C γ)
  | .prr C      => fun γ => .prr (substN C γ)
  | .lam C      => fun γ => .lam (substN C γ.cons)
  | .ap C V     => fun γ => .ap (substN C γ) (substP V γ)
  | .ret V      => fun γ => .ret (substP V γ)
  | .bind C C₁  => fun γ => .bind (substN C γ) (substN C₁ γ.cons)

end

@[simp]
def extend (γ : Subst Γ Γ') (V : ExpP Γ A) : Subst Γ (Γ'.cons A)
  | _, .zero   => V
  | _, .succ x => γ x

end Subst

@[simp]
def ExpN.subst (C : ExpN (Γ.cons A) X) (V : ExpP Γ A) : ExpN Γ X :=
  Subst.extend (fun _ => .var) V |>.substN C

@[simp]
def ExpN.subst₂ (C : ExpN (Γ.cons A₁ |>.cons A₂) X) (V₁ : ExpP Γ A₁) (V₂ : ExpP Γ A₂) : ExpN Γ X :=
  Subst.extend (fun _ => .var) V₁ |>.extend V₂ |>.substN C

section

local macro "lemma" M:ident γ:ident γTy:ident γFnP:ident γFnN:ident γ':ident γ'Ty:ident γ'FnP:ident γ'FnN:ident fnP:ident fnN:ident arg:term : tactic =>
  `(tactic| (
    apply $(M).rec
      (motive_1 := fun Γ'' A V => ∀ {Γ Γ'}, ($γ : $γTy Γ Γ') → ($γ' : $γ'Ty Γ' Γ'') → $γ.$γFnP ($γ'.$γ'FnP V) = $fnP V $arg)
      (motive_2 := fun Γ'' X C => ∀ {Γ Γ'}, ($γ : $γTy Γ Γ') → ($γ' : $γ'Ty Γ' Γ'') → $γ.$γFnN ($γ'.$γ'FnN C) = $fnN C $arg)
      <;> intros
      <;> intro _ _ _ _
      <;> simp [*]
      <;> (try constructor)
      <;> congr
      <;> funext _ x
      <;> cases x
      <;> simp
    cases ‹_›
      <;> simp
  ))

@[simp]
theorem Renaming.renameP_renameP (γ : Renaming Γ Γ') (γ' : Renaming Γ' Γ'') : γ.renameP (γ'.renameP V) = renameP V (fun A x => γ (γ' x)) :=
  by lemma V γ Renaming renameP renameN γ' Renaming renameP renameN renameP renameN fun A x => γ (γ' x)

@[simp]
theorem Subst.substP_renameP (γ : Subst Γ Γ') (γ' : Renaming Γ' Γ'') : γ.substP (γ'.renameP V) = substP V (fun A x => γ (γ' x)) :=
  by lemma V γ Subst substP substN γ' Renaming renameP renameN substP substN fun A x => γ (γ' x)

@[simp]
theorem Subst.renameP_substP (γ : Renaming Γ Γ') (γ' : Subst Γ' Γ'') : γ.renameP (γ'.substP V) = substP V (fun A x => γ.renameP (γ' x)) :=
  by lemma V γ Renaming renameP renameN γ' Subst substP substN substP substN fun A x => γ.renameP (γ' x)

@[simp]
theorem Subst.substN_substN (γ : Subst Γ Γ') (γ' : Subst Γ' Γ'') : γ.substN (γ'.substN C) = substN C (fun A x => γ.substP (γ' x)) :=
  by lemma C γ Subst substP substN γ' Subst substP substN substP substN fun A x => γ.substP (γ' x)

end

@[simp]
theorem Subst.cons_var : cons (Γ := Γ) (A := A) (fun _ => .var) = fun _ => .var := by
  funext _ x
  cases x
    <;> simp

@[simp]
theorem Subst.substP_var : substP V (fun _ => .var) = V := by
  apply V.rec
    (motive_1 := fun Γ A V => substP V (fun _ => .var) = V)
    (motive_2 := fun Γ X C => substN C (fun _ => .var) = C)
    <;> intros
    <;> simp [*]

macro "subst" : tactic => `(tactic| (simp; congr; funext _ x; cases x <;> simp; first | done | cases ‹_› <;> simp))

inductive Steps : (C C' : ExpN .nil X) → Type
  | prl  (s : Steps C C') : Steps (.prl C)     (.prl C')
  | prr  (s : Steps C C') : Steps (.prr C)     (.prr C')
  | ap   (s : Steps C C') : Steps (.ap C V)    (.ap C' V)
  | bind (s : Steps C C') : Steps (.bind C C₁) (.bind C' C₁)

  | check_triv : Steps (.check .triv C)         C
  | case_inl   : Steps (.case (.inl V) C₁ C₂)   (C₁.subst V)
  | case_inr   : Steps (.case (.inr V) C₁ C₂)   (C₂.subst V)
  | split_pair : Steps (.split (.pair V₁ V₂) C) (C.subst₂ V₁ V₂)
  | force_susp : Steps (.force (.susp C))       C

  | prl_pair   : Steps (.prl (.pair C₁ C₂))     C₁
  | prr_pair   : Steps (.prr (.pair C₁ C₂))     C₂
  | ap_lam     : Steps (.ap (.lam C) V)         (C.subst V)
  | bind_ret   : Steps (.bind (.ret V) C)       (C.subst V)

inductive Reduces : (C C' : ExpN .nil A) → Type
  | refl                                       : Reduces C C
  | step (s : Steps C C') (r : Reduces C' C'') : Reduces C C''

namespace Reduces

def trans : (r : Reduces C C') → (r' : Reduces C' C'') → Reduces C C''
  | .refl,     r' => r'
  | .step s r, r' => .step s (r.trans r')

def comp {F : (C : ExpN .nil X) → ExpN .nil Y} (f : ∀ {C C'}, (s : Steps C C') → Steps (F C) (F C')) : (r : Reduces C C') → Reduces (F C) (F C')
  | .refl     => .refl
  | .step s r => .step (f s) (r.comp f)

end Reduces

mutual rec

def HTP : (A : TypP) → (V : ExpP .nil A) → Type
  | .void       => nofun
  | .unit       => fun | .triv => Unit
  | .sum  A₁ A₂ => fun | .inl V => HTP A₁ V
                       | .inr V => HTP A₂ V
  | .prod A₁ A₂ => fun | .pair V₁ V₂ => HTP A₁ V₁ × HTP A₂ V₂
  | .U X        => fun | .susp C => HTN X C

def HTN : (X : TypN) → (C : ExpN .nil X) → Type
  | .unit       => fun _ => Unit
  | .prod X₁ X₂ => fun C => HTN X₁ (.prl C) × HTN X₂ (.prr C)
  | .arr A X    => fun C => ∀ {V}, HTP A V → HTN X (.ap C V)
  | .F A        => fun C => Σ V, HTP A V × Reduces C (.ret V)

end

def HTN.expand : ∀ {X C₁ C₂}, (r₁ : Reduces C₁ C₂) → (ht₂ : HTN X C₂) → HTN X C₁
  | .unit,       _, _, _,  ()          => ()
  | .prod X₁ X₂, _, _, r₁, (ht₁, ht₂)  => (expand (.comp .prl r₁) ht₁, expand (.comp .prr r₁) ht₂)
  | .arr A X,    _, _, r₁, ht          => fun ht₁ => expand (.comp .ap r₁) (ht ht₁)
  | .F A,        _, _, r₁, ⟨_, ht, r₂⟩ => ⟨_, ht, r₁.trans r₂⟩

def HTSubst (γ : Subst .nil Γ) : Type :=
  ∀ {{A}} x, HTP A (γ x)

def HTSubst.extend (ht_γ : HTSubst γ) (ht : HTP A M) : HTSubst (γ.extend M)
  | _, .zero   => ht
  | _, .succ x => ht_γ x

def HTP' Γ A (V : ExpP Γ A) : Type :=
  ∀ {γ}, (ht_γ : HTSubst γ) → HTP A (γ.substP V)

def HTN' Γ X (C : ExpN Γ X) : Type :=
  ∀ {γ}, (ht_γ : HTSubst γ) → HTN X (γ.substN C)

mutual rec

def ftlrP : (V : ExpP Γ A) → HTP' Γ A V
  | .var x      => fun ht_γ => ht_γ x
  | .triv       => fun ht_γ => ()
  | .inl V      => fun ht_γ => ftlrP V ht_γ
  | .inr V      => fun ht_γ => ftlrP V ht_γ
  | .pair V₁ V₂ => fun ht_γ => (ftlrP V₁ ht_γ, ftlrP V₂ ht_γ)
  | .susp C     => fun ht_γ => ftlrN C ht_γ

def ftlrN : (C : ExpN Γ X) → HTN' Γ X C
  | .abort V      => fun ht_γ => nomatch Subst.substP V _, ftlrP V ht_γ
  | .check V C    => fun ht_γ => show HTN _ (.check ..) from
                                 match Subst.substP V _, ftlrP V ht_γ with
                                 | .triv, ht => .expand (.step .check_triv .refl) (ftlrN C ht_γ)
  | .case V C₁ C₂ => fun ht_γ => show HTN _ (.case ..) from
                                 match Subst.substP V _, ftlrP V ht_γ with
                                 | .inl V, ht => .expand (.step .case_inl .refl) <| cast (by subst) <| ftlrN C₁ (ht_γ.extend ht)
                                 | .inr V, ht => .expand (.step .case_inr .refl) <| cast (by subst) <| ftlrN C₂ (ht_γ.extend ht)
  | .split V C    => fun ht_γ => show HTN _ (.split ..) from
                                 match Subst.substP V _, ftlrP V ht_γ with
                                 | .pair V₁ V₂, (ht₁, ht₂) => .expand (.step .split_pair .refl) <| cast (by subst) <| ftlrN C (ht_γ.extend ht₁ |>.extend ht₂)
  | .force V      => fun ht_γ => show HTN _ (.force ..) from
                                 match Subst.substP V _, ftlrP V ht_γ with
                                 | .susp C, ht => .expand (.step .force_susp .refl) ht

  | .triv       => fun ht_γ => ()
  | .pair C₁ C₂ => fun ht_γ => (HTN.expand (.step .prl_pair .refl) <| ftlrN C₁ ht_γ, HTN.expand (.step .prr_pair .refl) <| ftlrN C₂ ht_γ)
  | .prl C      => fun ht_γ => let (ht₁, ht₂) := ftlrN C ht_γ; ht₁
  | .prr C      => fun ht_γ => let (ht₁, ht₂) := ftlrN C ht_γ; ht₂
  | .lam C      => fun ht_γ => fun ht => HTN.expand (.step .ap_lam .refl) <| cast (by subst) <| ftlrN C (ht_γ.extend ht)
  | .ap C V     => fun ht_γ => ftlrN C ht_γ (ftlrP V ht_γ)
  | .ret V      => fun ht_γ => ⟨_, ftlrP V ht_γ, .refl⟩
  | .bind C C₁  => fun ht_γ => let ⟨_, ht, r⟩ := ftlrN C ht_γ; .expand (.trans (.comp .bind r) (.step .bind_ret .refl)) <| cast (by subst) <| ftlrN C₁ (ht_γ.extend ht)

end
