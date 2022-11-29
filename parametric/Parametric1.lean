import Parametric

class ParaF (ϕ : (Fin2 n → Type u) → Type u) :=
  prop : ∀ α β, (∀ i, α i → β i → Prop) → ϕ α → ϕ β → Prop

attribute [simp] ParaF.prop

instance : ParaF λ α => α i where
  prop _ _ r := r i

instance : @ParaF n λ _ => α where
  prop _ _ _ := Eq

instance [ParaF ϕ] [ParaF φ] : ParaF λ α => ϕ α → φ α where
  prop α β r f g := ∀ x y, ParaF.prop α β r x y → ParaF.prop α β r (f x) (g y)

class ParaT (α : Type u) :=
  prop : α → Prop

attribute [simp] ParaT.prop

instance (ϕ : Type u → Type u) [I : @ParaF 1 λ α => ϕ (α .zero)] : ParaT (∀ α, ϕ α) where
  prop f := ∀ {α β} (r : α → β → Prop), I.prop (λ _ => α) (λ _ => β) (λ _ => r) (f α) (f β)

instance (ϕ : Type u → Type u → Type u) [I : @ParaF 2 λ α => ϕ (α .zero) (α (.succ .zero))] : ParaT (∀ α β, ϕ α β) where
  prop f := ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop), I.prop (Fin2.cases₂' α β) (Fin2.cases₂' α' β') (Fin2.cases₂ r s) (f α β) (f α' β')

def Para (α) [I : ParaT α] := Subtype I.prop

instance [ParaT α] : CoeFun (Para α) λ _ => α where
  coe := Subtype.val

macro_rules | `(tactic| para_step) => `(tactic| destruct Para)

def Para.mk [ParaT α] (x : α) (h : ParaT.prop x := by parametric) : Para α := ⟨x, h⟩

section Nat

example : ParaT.prop (@n : ∀ {α}, α → (α → α) → α) =
  ∀ {α β} (r : α → β → Prop),
    ∀ z z', r z z' →
      ∀ s s', (∀ x x', r x x' → r (s x) (s' x')) →
        r (n z s) (n z' s')
:= rfl

abbrev Nat' := Para (∀ {α}, α → (α → α) → α)

@[simp] def Nat'.zero            : Nat' := .mk λ z _ => z
@[simp] def Nat'.succ (n : Nat') : Nat' := .mk λ z s => s (n z s)

def Nat'.ofNat : Nat → Nat'
  | .zero   => zero
  | .succ n => succ (ofNat n)

example : Nat' ≃ Nat where
  toFun n := n .zero .succ
  invFun := .ofNat
  right_inv n := by
    induction n
    case zero => rfl
    case succ ih => exact congrArg Nat.succ ih
  left_inv | ⟨_, h⟩ => by
    unfold Nat'.ofNat
    dsimp
    split
      <;> rename_i h'
      <;> congr
      <;> funext _ z s
      <;> have := h' ▸ h (λ n x => Nat'.ofNat n z s = x) Nat.zero z rfl Nat.succ s λ _ _ => congrArg s
      <;> exact this

end Nat

section K

example : ParaT.prop (@f : ∀ {α β}, α → β → α) =
  ∀ {α α'} (r : α → α' → Prop),
    ∀ {β β'} (s : β → β' → Prop),
      ∀ x x', r x x' →
        ∀ y y', s y y' →
          r (f x y) (f x' y')
:= rfl

example : Para (∀ {α β}, α → β → α) := .mk λ x _ => x

example (f : Para (∀ {α β}, α → β → α)) : f x y = x :=
  f.2 (λ _ x' => x' = x) (λ _ y' => y' = y) () x rfl () y rfl

end K

section List

inductive List.liftRel (r : α → β → Prop) : List α → List β → Prop
  | nil  : liftRel r [] []
  | cons : r x y → liftRel r xs ys → liftRel r (x :: xs) (y :: ys)

theorem lift_map (g : α → β) : ∀ l, List.liftRel (λ x y => g x = y) l (l.map g)
  | [] => .nil
  | _::l => .cons rfl (lift_map g l)

instance [ParaF ϕ] : ParaF λ α => List (ϕ α) where
  prop α β r := List.liftRel (ParaF.prop α β r)

macro_rules | `(tactic| para_step) => `(tactic| intro (h : List.liftRel _ _ _); induction h)

example : ParaT.prop (@f : ∀ {α β}, (α → β → β) → β → List α → β) =
  ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop),
    ∀ c c', (∀ x x', r x x' → ∀ y y', s y y' → s (c x y) (c' x' y')) →
      ∀ x x', s x x' →
        ∀ l l', List.liftRel r l l' →
          s (f c x l) (f c' x' l')
:= rfl

example : ParaT.prop @List.foldr := by parametric
example : ParaT.prop @List.foldl := by
  intro _ _ _ _ _ _ _ _ _ x x' hx _ _ h
  revert x x' hx
  revert h
  parametric

example (f : Para (∀ {α β}, (α → β → β) → β → List α → β)) (g : α → α') (h : β → β') (c c') (hc : ∀ x y, h (c x y) = c' (g x) (h y)) (x l) : h (f c x l) = f c' (h x) (l.map g) :=
  f.2 (λ x y => g x = y) (λ x y => h x = y) c _ (λ x _ hx y _ hy => hx ▸ hy ▸ hc x y) x _ rfl l _ (lift_map g l)

example : ParaT.prop λ {α β : Type _} x => List.map (λ f : α → β => f x) := by parametric

end List

section Prod

inductive Prod.liftRel (r : α → α' → Prop) (s : β → β' → Prop) : α × β → α' × β' → Prop
  | mk : r x x' → s y y' → liftRel r s (x, y) (x', y')

instance [ParaF ϕ] [ParaF φ] : ParaF.{u} λ α => ϕ α × φ α where
  prop α β r := Prod.liftRel (ParaF.prop α β r) (ParaF.prop α β r)

macro_rules | `(tactic| para_step) => `(tactic| intro (h : Prod.liftRel _ _ _ _); induction h)

example : ParaT.prop (@f : ∀ {α β}, α × β → α) =
  ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop),
    ∀ xy xy', Prod.liftRel r s xy xy' →
      r (f xy) (f xy')
:= rfl

example : ParaT.prop @Prod.fst := by parametric

example : ParaT.prop λ {α β : Type _} (fx : (α → β) × α) => (match fx with | .mk f x => f x : β) := by parametric

end Prod

section Sum

inductive Sum.liftRel (r : α → α' → Prop) (s : β → β' → Prop) : α ⊕ β → α' ⊕ β' → Prop
  | inl : r x x' → liftRel r s (.inl x) (.inl x')
  | inr : s y y' → liftRel r s (.inr y) (.inr y')

instance [ParaF ϕ] [ParaF φ] : ParaF.{u} λ α => ϕ α ⊕ φ α where
  prop α β r := Sum.liftRel (ParaF.prop α β r) (ParaF.prop α β r)

macro_rules | `(tactic| para_step) => `(tactic| intro (h : Sum.liftRel _ _ _ _); induction h)

example : ParaT.prop (@f : ∀ {α β}, α → α ⊕ β) =
  ∀ {α α'} (r : α → α' → Prop) {β β'} (s : β → β' → Prop),
    ∀ x x', r x x' →
      Sum.liftRel r s (f x) (f x')
:= rfl

example : ParaT.prop @Sum.inl := by parametric

example : ParaT.prop λ {α β : Type _} (x : α) (yf : β ⊕ (α → β)) => (match yf with | .inl y => y | .inr f => f x : β) := by parametric

example : ParaT.prop @List.zip := by parametric

end Sum

open Lean Meta Elab Command

def List.alternate : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: alternate ys xs
termination_by _ xs ys => xs.length + ys.length

def mkArr (t₁ t₂ : Expr) : Expr :=
  .forallE .anonymous t₁ t₂ .default

def getForallBinders : Expr → List (Name × Expr)
  | .forallE n t b _ => (n, t) :: getForallBinders b
  | _ => []

def mkForallBinders (b : Expr) (bi : BinderInfo) : List (Name × Expr) → Expr
  | [] => b
  | (n, t) :: bs => .forallE n t (mkForallBinders b bi bs) bi

def liftBindersAlternate (start dec : Nat) : List (Name × Expr) → List (Name × Expr)
  | [] => []
  | (n, t) :: bs => (n, t.liftLooseBVars 0 start) :: liftBindersAlternate (start - dec) dec bs

def mkParaInstance (val : InductiveVal) : CommandElabM Unit := do
  if val.numIndices > 0 then
    throwError "unsupported"
    -- currenlty assumes Type u₁ → Type u₂ → ... → Type (max u₁ u₂ ...)

  /-
  let name := .str val.name "LiftRel"

  let mkName (s : String) (n : Nat) : Name := .str .anonymous (s ++ "_" ++ toString n)

  let us := val.levelParams.enum.map (mkName "u" ·.1.succ)
  let vs := val.levelParams.enum.map (mkName "v" ·.1.succ)

  let levelParams := us.alternate vs

  let mut α : Expr := .const val.name (us.map .param)
  let mut β : Expr := .const val.name (vs.map .param)

  for i in [:val.numParams] do
    let i := val.numParams - i
    α := .app α <| .bvar <| i * 3 - 1
    β := .app β <| .bvar <| i * 3 - 1

  let mkType (type : Expr) (bi : BinderInfo) : Expr := Id.run do
    let mut type := type
    for i in [:val.numParams] do
      let i := val.numParams - i
      type := .forallE `r (mkArr (.bvar 1) <| mkArr (.bvar 1) <| .sort .zero) type bi
      type := .forallE `β (.sort (.succ (.param (mkName "v" i)))) type .implicit
      type := .forallE `α (.sort (.succ (.param (mkName "u" i)))) type .implicit
    return type

  let type := mkType (mkArr α <| mkArr β <| .sort .zero) .default
  
  let ctors ← val.ctors.mapM fun ctor => do
    let ctor ← getConstInfo ctor
    Lean.logInfo m!"{ctor.name}.{ctor.levelParams} : {ctor.type}"
    let type := ctor.type.getForallBodyMaxDepth val.numParams
    let ts := getForallBinders type
    let mut params := #[]
    for i in [:val.numParams * 3] do
      params := params.push <| .bvar <| i + ts.length * 2
    params := params.reverse
    let mut params' := #[]
    for i in [:ts.length] do
      params' := params'.push <| .bvar <| i * 2 + 1
    for i in [:val.numParams] do
      params' := params'.push <| .bvar <| i * 3 + ts.length * 2 + 2
    params := params.push (mkAppN (.const ctor.name (us.map .param)) params'.reverse)
    params' := #[]
    for i in [:ts.length] do
      params' := params'.push <| .bvar <| i * 2
    for i in [:val.numParams] do
      params' := params'.push <| .bvar <| i * 3 + ts.length * 2 + 1
    params := params.push (mkAppN (.const ctor.name (vs.map .param)) params'.reverse)
    Lean.logInfo m!"{ts}"
    let ts := (liftBindersAlternate (val.numParams * 2) 1 ts).alternate (liftBindersAlternate (val.numParams * 2) 1 ts)
    let type := mkType (mkForallBinders (mkAppN (.const name (levelParams.map .param)) params) .implicit ts) .implicit
    let ctor := {
      name := ctor.name.replacePrefix val.name name
      type
    }
    Lean.logInfo m!"{ctor.name} : {ctor.type}"
    return ctor
  -/

  liftCoreM <| addAndCompile <| .defnDecl {
    name := .str val.name "Lift"
    levelParams := []
    type := .const ``Nat []
    value := .const ``Nat.zero []
    hints := .abbrev
    safety := .safe
  }

  /-
  liftCoreM <| addAndCompile <| .inductDecl levelParams (val.numParams * 3) [{
    name
    type
    ctors
  }] false
  -/

elab "#derive_para" names:ident* : command => do
    for name in names do
      withRef name do
        mkParaInstance (← getConstInfoInduct name.getId)

set_option pp.all true in
#derive_para List Prod Sum

instance : ToMessageData ConstantVal where
  toMessageData val := val.name ++ (if val.levelParams.isEmpty then m!" : " else ".{"  ++ .joinSep (val.levelParams.map .ofName) ", " ++ "} : ") ++ val.type

elab "#print inductive " name:ident : command => do
  let info ← getConstInfoInduct name.getId
  let mut m := m!"{info.toConstantVal}{Format.line}  {info.numParams} params {info.numIndices} indices"
  for ctor in info.ctors do
    let ctorInfo ← getConstInfoCtor ctor
    m := m!"{m}{Format.line}{ctorInfo.toConstantVal}{Format.line}  {ctorInfo.numFields} fields"
  Lean.logInfo m

#print List.Lift
#eval List.Lift

#print Prod.mk
#print Prod.liftRel.mk

#print Sum.inl
#print Sum.liftRel.inl

#print Prod.liftRel
#print Prod.LiftRel
