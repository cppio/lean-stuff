import Parametric

inductive Ty (n : Nat)
  | var (a : Fin2 n.succ)
  | arr (x y : Ty n)

def Ty.toType' (α : Fin2 n.succ → Type u) : Ty n → Type u :=
  @rec n _ α λ _ _ x y => x → y

@[simp] theorem Ty.toType'.var : (var a).toType' α = α a := rfl
@[simp] theorem Ty.toType'.arr : (arr x y).toType' α = (x.toType' α → y.toType' α) := rfl

def Ty.toType'' : ∀ {n}, ((Fin2 (.succ n) → Type u) → Type u) → Type (u + 1) :=
  @Nat.rec _ (λ f => ∀ {α}, f λ _ => α) λ _ t f => ∀ {α}, t λ g => f (Fin2.cases α g)

@[simp] theorem Ty.toType''.zero : @toType'' .zero f = ∀ {α}, f λ _ => α := rfl
@[simp] theorem Ty.toType''.succ : @toType'' (.succ n) f = ∀ {α}, toType'' λ g => f (Fin2.cases α g) := rfl

def Ty.toType (x : Ty n) : Type (u + 1) :=
  toType'' x.toType'

@[simp]
def Ty.apply' : ∀ {n : Nat} {f : (Fin2 n.succ → Type u) → Type u} (α : Fin2 n.succ → Type u), toType'' f → f α
  | .zero, _, α, g => (funext (Fin2.cases rfl Fin2.elim) : α = λ _ => α _) ▸ g
  | .succ _, _, α, g => (funext (Fin2.cases rfl λ _ => rfl) : α = Fin2.cases _ _) ▸ apply' (α ∘ .succ) g

def Ty.apply {x : Ty n} (f : x.toType) (α : Fin2 n.succ → Type u) : x.toType' α :=
  apply' α f

def Ty.toProp' {α β : Fin2 n.succ → Type u} (r : ∀ i, α i → β i → Prop) : (x : Ty n) → x.toType' α → x.toType' β → Prop :=
  @rec n _ r λ _ _ xp yp f f' => ∀ z z', xp z z' → yp (f z) (f' z')

@[simp] theorem Ty.toProp'.var : (var a).toProp' r = r a := rfl
@[simp] theorem Ty.toProp'.arr : (arr x y).toProp' r = λ f f' => ∀ z z', x.toProp' r z z' → y.toProp' r (f z) (f' z') := rfl

def Ty.toProp'' : {n : Nat} → ((α β : Fin2 n.succ → Type u) → (r : ∀ i, α i → β i → Prop) → Prop) → Prop :=
  @Nat.rec _
    --(λ f => f Fin2.elim Fin2.elim Fin2.elim)
    (λ f => ∀ {α β} (r : α → β → Prop), f (λ _ => α) (λ _ => β) (λ _ => r))
    λ _ p f => ∀ {α β} (r : α → β → Prop), p λ α' β' g => f (Fin2.cases α α') (Fin2.cases β β') (Fin2.cases r g)

--@[simp] theorem Ty.toProp''.zero : @toProp'' .zero f = f Fin2.elim Fin2.elim Fin2.elim := rfl
@[simp] theorem Ty.toProp''.zero : @toProp'' .zero f = ∀ {α β} (r : α → β → Prop), f (λ _ => α) (λ _ => β) (λ _ => r) := rfl
@[simp] theorem Ty.toProp''.succ : @toProp'' (.succ n) f = ∀ {α β} (r : α → β → Prop), toProp'' λ α' β' g => f (Fin2.cases α α') (Fin2.cases β β') (Fin2.cases r g) := rfl

def Ty.toProp (x : Ty .zero) (f : x.toType) : Prop :=
  ∀ {α β} (r : α → β → Prop), x.toProp' (λ _ => r) f f

def Ty.toProp_new {x : Ty n} (f : x.toType) : Prop :=
  Ty.toProp'' λ α β r => x.toProp' r (x.apply f α) (x.apply f β)

example : (.arr (.var .zero) (.var .zero) : Ty .zero).toProp @f =
  ∀ {α β : Type u} (r : α → β → Prop) (z : α) (z' : β), r z z' →
    r
      (@Eq.rec
        (Fin2 (.succ .zero) → Type u)
        (λ _ => α)
        (λ α' _ => α' .zero → α' .zero)
        (@f α)
        (Fin2.cases α Fin2.elim)
        (funext (Fin2.cases rfl Fin2.elim))
        z)
      (@Eq.rec
        (Fin2 (.succ .zero) → Type u)
        (λ _ => β)
        (λ β' _ => β' .zero → β' .zero)
        (@f β)
        (Fin2.cases β Fin2.elim)
        (funext (Fin2.cases rfl Fin2.elim))
        z')
:= rfl

example : @Ty.toProp_new .zero x @f = Ty.toProp x @f := by
  simp [Ty.toProp_new, Ty.toProp]
  apply forallext; intro α
  apply forallext; intro β
  apply forallext; intro r
  have hα : Fin2.cases α Fin2.elim = λ _ => α := funext (Fin2.cases rfl Fin2.elim)
  have hβ : Fin2.cases β Fin2.elim = λ _ => β := funext (Fin2.cases rfl Fin2.elim)
  apply Eq.trans (
    hα.rec (motive := λ α' hα' =>
        @Ty.toProp' .zero (Fin2.cases α Fin2.elim) (Fin2.cases β Fin2.elim) (Fin2.cases        r  Fin2.elim) x       (hα ▸ @f α) (hβ ▸ @f β)
      = @Ty.toProp' .zero             α'           (Fin2.cases β Fin2.elim) (Fin2.cases (hα' ▸ r) Fin2.elim) x (hα' ▸ hα ▸ @f α) (hβ ▸ @f β)
    ) rfl)
  apply Eq.trans (
    hβ.rec (motive := λ β' hβ' =>
        @Ty.toProp' .zero (λ _ => α) (Fin2.cases β Fin2.elim) (Fin2.cases       (hα ▸ r) Fin2.elim) x (hα ▸ @f α)       (hβ ▸ @f β)
      = @Ty.toProp' .zero (λ _ => α)             β'           (Fin2.cases (hβ' ▸ hα ▸ r) Fin2.elim) x (hα ▸ @f α) (hβ' ▸ hβ ▸ @f β)
    ) rfl)
  congr
  . funext i
    cases i
    case zero =>
      dsimp [Fin2.cases]
      apply Eq.trans
      case h₂ =>
        show hα.rec (motive := λ α' _ => α' .zero → β → Prop) r = r
        exact @Eq.rec (Fin2 (.succ .zero) → Type _) (λ _ => α) (λ α' hα' => @Eq.rec (Fin2 (.succ .zero) → Type _) α' (λ α' _ => α' .zero → β → Prop) ((hα' ▸ rfl : (α → β → Prop) = (α' .zero → β → Prop)).mp _) (λ _ => α) hα'.symm = _) rfl (Fin2.cases α Fin2.elim) hα.symm
      case h₁ =>
        exact @Eq.rec (Fin2 (.succ .zero) → Type _) (λ _ => β) (λ β' hβ' => @Eq.rec (Fin2 (.succ .zero) → Type _) β' (λ β' _ => α → β' .zero → Prop) ((hβ' ▸ rfl : (α → β → Prop) = (α → β' .zero → Prop)).mp _) (λ _ => β) hβ'.symm = _) rfl (Fin2.cases β Fin2.elim) hβ.symm
    case succ i => cases i
  . apply @subst_subst _ x.toType'
  . apply @subst_subst _ x.toType'

class AsTy' (f : Type _ → Type _) :=
  ty : Ty .zero
  pf : f = λ α => ty.toType' λ _ => α

attribute [simp] AsTy'.ty

@[simp]
instance : AsTy' λ α => α where
  ty := .var .zero
  pf := rfl

@[simp]
instance [x : AsTy' f] [y : AsTy' g] : AsTy' λ α => f α → g α where
  ty := .arr x.ty y.ty
  pf := funext λ α => congrArg₂ (·→·) (congrFun x.pf α) (congrFun y.pf α)

class AsTy (α : Type _) :=
  ty : Ty .zero
  pf : α = ty.toType

attribute [simp] AsTy.ty

@[simp]
instance [x : AsTy' f] : AsTy (∀ {α}, f α) where
  ty := x.ty
  pf := by
    show (∀ {α}, f α) = ∀ {α}, (λ α => x.ty.toType' λ _ => α) α
    rw [← x.pf]

@[simp]
def Para (α : Type _) [I : AsTy α] : α → Prop := I.pf ▸ I.ty.toProp
def ParaT (α : Type _) [AsTy α] := Subtype (Para α)

@[simp]
instance [AsTy α] : CoeFun (ParaT α) λ _ => α where
  coe := Subtype.val

macro "parametric" : tactic => `(tactic| (destruct ParaT; repeat (first | intro _ | apply_assumption)))

def ParaT.mk [AsTy α] (x : α) (h : Para α x := by parametric) : ParaT α := ⟨x, h⟩

example : Para (∀ {α}, α) @f =
  ∀ {α β} (r : α → β → Prop),
    r f f
:= rfl

example : ParaT (∀ {α}, α) ≃ Empty where
  toFun f := f.1
  invFun := Empty.rec
  right_inv := Empty.rec
  left_inv f := nomatch (f.1 : Empty)

example : Para (∀ {α}, α → α) @f =
  ∀ {α β} (r : α → β → Prop),
    ∀ x x', r x x' →
      r (f x) (f x')
:= rfl

example : ParaT (∀ {α}, α → α) ≃ Unit where
  toFun _ := ()
  invFun _ := .mk λ x => x
  right_inv _ := rfl
  left_inv | ⟨_, h⟩ => by
    dsimp
    congr
    funext _ x
    exact h (λ () y => x = y) () x rfl

example : Para (∀ {α}, α → α → α) @f =
  ∀ {α β} (r : α → β → Prop),
    ∀ x x', r x x' →
      ∀ y y', r y y' →
        r (f x y) (f x' y')
:= rfl

example : ParaT (∀ {α}, α → α → α) ≃ Bool where
  toFun f := f false true
  invFun
    | false => .mk λ x _ => x
    | true => .mk λ _ y => y
  right_inv
    | false => rfl
    | true => rfl
  left_inv | ⟨f, h⟩ => by
    dsimp
    split
      <;> rename_i h'
      <;> congr
      <;> funext _ x y
      <;> have := h' ▸ h (λ | false => λ z => x = z | true => λ z => y = z) false x rfl true y rfl
      <;> exact this

example : Para (∀ {α}, α → (α → α) → α) @f =
  ∀ {α β} (r : α → β → Prop),
    ∀ z z', r z z' →
      ∀ s s', (∀ n n', r n n' → r (s n) (s' n')) →
        r (f z s) (f z' s')
:= rfl

abbrev Nat' := ParaT (∀ {α}, α → (α → α) → α)

def Nat'.zero : Nat' := .mk λ z _ => z
def Nat'.succ (n : Nat') : Nat' := .mk λ z s => s (n z s)

def Nat'.ofNat : Nat → Nat'
  | .zero => zero
  | .succ n => succ (ofNat n)

def Nat'.toNat (n : Nat') : Nat := n .zero .succ

example : Nat' ≃ Nat where
  toFun := Nat'.toNat
  invFun := .ofNat
  right_inv n := by
    induction n
    case zero => rfl
    case succ ih => exact congrArg Nat.succ ih
  left_inv | ⟨f, h⟩ => by
    unfold Nat'.ofNat Nat'.toNat Nat'.zero Nat'.succ
    dsimp
    split
      <;> rename_i h'
      <;> congr
      <;> funext α z s
      <;> have := h' ▸ h (λ n x => Nat'.ofNat n z s = x) _ z rfl _ s λ _ _ => congrArg s
    case _ => exact this
    case _ n =>
      apply Eq.trans _ this
      clear h' this
      induction n
      case zero => rfl
      case succ ih => exact congrArg s ih

example : Para (∀ {α}, ((α → α) → α) → α) @f =
  ∀ {α β} (r : α → β → Prop) (p : (α → α) → α) (q : (β → β) → β),
    (∀ s t, (∀ x y, r x y → r (s x) (t y)) → r (p s) (q t)) →
      r (f p) (f q)
:= rfl

inductive T' : Nat → Type
  | v : Fin2 n → T' n
  | a : T' n.succ → T' n
  deriving DecidableEq

def T'.succ : T' n → T' n.succ
  | v x => v x.succ
  | a t => a t.succ

def T'.castSucc : T' n → T' n.succ
  | v x => v x.castSucc
  | a t => a t.castSucc

def T'.lift : Nat → T' n → T' n
  | .zero, t => t
  | .succ m, t => a (t.succ.lift m)

def T'.lift' : Nat → T' n → T' n
  | .zero, t => t
  | .succ m, t => a (t.castSucc.lift' m)

abbrev T := T' .zero

def T'.toT : ∀ {n}, T' n → T
  | .zero, t => t
  | .succ _, t => toT (.a t)

abbrev S := ParaT (∀ {α}, ((α → α) → α) → α)

def S.ofT' (g : (α → α) → α) (l : Fin2 n → α) : T' n → α
  | .v x => l x
  | .a t => g λ x => ofT' g (λ | (.zero : Fin2 n.succ) => x | .succ y => l y) t

theorem S.Para_ofT' (r : α → β → Prop) (p : (α → α) → α) (q : (β → β) → β) (h : ∀ s t, (∀ x y, r x y → r (s x) (t y)) → r (p s) (q t)) {l : Fin2 n → α} {l' : Fin2 n → β} (hl : ∀ x, r (l x) (l' x)) : (t : T' n) → r (ofT' p l t) (ofT' q l' t)
  | .v _ => hl _
  | .a _ => h _ _ λ _ _ h' => Para_ofT' _ _ _ h (λ | (.zero : Fin2 n.succ) => h' | .succ _ => hl _) _

def S.ofT (t : T) : S :=
  ⟨λ {_} g => ofT' g (λ (x : Fin2 .zero) => nomatch x) t, λ r p q h => Para_ofT' r p q h (λ (x : Fin2 .zero) => nomatch x) t⟩

def S.toT' (g : Nat × T → Nat × T) : Nat × T :=
  let t := .a (.v .zero)
  let nt := g (.zero, t)
  if nt.2 = (g (.zero, .a (.a (.v .zero)))).2
  then (nt.1.succ, nt.2)
  else (.zero, nt.2.lift nt.1)

def S.toT (s : S) : T :=
  let nt := s S.toT'
  nt.2.lift' nt.1

def S₁₀ := S.ofT <| .a <| .v .zero
def S₂₀ := S.ofT <| .a <| .a <| .v .zero
def S₂₁ := S.ofT <| .a <| .a <| .v <| .succ .zero
def S₃₀ := S.ofT <| .a <| .a <| .a <| .v .zero
def S₃₁ := S.ofT <| .a <| .a <| .a <| .v <| .succ .zero
def S₃₂ := S.ofT <| .a <| .a <| .a <| .v <| .succ <| .succ .zero

#reduce S₁₀.toT
#reduce S₂₀.toT
#reduce S₂₁.toT
#reduce S₃₀.toT
#reduce S₃₁.toT
#reduce S₃₂.toT

#reduce Prod.snd ∘ S.ofT' S.toT' (λ (h : Fin2 .zero) => nomatch h) <| .a <| .v .zero
#reduce Prod.snd ∘ S.ofT' S.toT' (λ | (.zero : Fin2 (.succ .zero)) => sorry) <| .a <| .v .zero

#reduce Prod.snd ∘ S.ofT' S.toT' (λ | (.zero : Fin2 (.succ .zero)) => (_, .a <| .v .zero)) <| .a <| .v (.succ .zero)
#reduce Prod.snd ∘ S.ofT' S.toT' (λ | (.zero : Fin2 (.succ .zero)) => (_, .a <| .a <| .a <| .v <| .succ <| .succ .zero)) <| .a <| .v (.succ .zero)

def foo (l : Fin2 n → Nat × T) : T' n → T
  | .v x => (l x).2
  | .a t => sorry

example (l : Fin2 n → Nat × T) : ∀ t, (S.ofT' S.toT' l t).2 = foo l t
  | .v _ => rfl
  | .a t => by
    unfold S.ofT'
    have := λ x => _example (λ | (.zero : Fin2 n.succ) => x | .succ y => l y) t
    rw [S.toT']
    dsimp
    rw [this, this]
    clear this
    split
    case inl h =>
      simp at *
      sorry
    case inr h =>
      simp at *
      sorry

example : S ≃ T where
  toFun := S.toT
  invFun := .ofT
  right_inv n := by
    induction n
    case zero => rfl
    case succ ih =>
      show (if (S.ofNat _).toNat = (S.ofNat _).toNat then (S.ofNat _).toNat + 1 else 0) = _ + 1
      simp [ih]
  left_inv | ⟨f, h⟩ => by
    unfold S.ofNat
    split
      <;> rename_i h'
      <;> congr
    case _ =>
      dsimp [S.toNat, S.toNat'] at h'
      dsimp at h
      have : f S.toBool' = false := by
        have := h' ▸ @h Nat Bool (λ n b => S.NatToBool' n = b) S.toNat' S.toBool' λ s t hst => foo s t λ x => hst x _ rfl
        exact this.symm
      funext α g
      sorry
      /-
      have := h' ▸ @h Nat α (λ | 0 => λ b => (g λ x => x) = b | _ + 1 => λ _ => True) (λ g => if g 0 = g 1 then g 0 + 1 else 0) g λ s t hst => by
        dsimp [_example.match_2] at hst ⊢
        split
        case inl => trivial
        case inr hr =>
          show _ = _
          have := λ x => hst 1 x trivial
          specialize hst 0 _ rfl
          cases hs₀ : s 0 <;> rw [hs₀] at hr hst <;> cases hs₁ : s 1 <;> rw [hs₁] at hr this
          contradiction
          simp at hst
          sorry
          simp at this
          sorry
          sorry
      exact this
      -/
    case _ =>
      sorry
