import Lean

private def nameCmp' : List Lean.Name → List Lean.Name → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | n₁ :: s₁, n₂ :: s₂ =>
    match n₁.cmp n₂ with
    | .eq => nameCmp' s₁ s₂
    | ord => ord

private def nameCmp (n₁ : Lean.Name) (n₂ : Lean.Name) : Ordering :=
  nameCmp' n₁.components n₂.components

elab "#print prefix" id:ident : command => do
  let cs := (← Lean.getEnv).constants.fold (λ cs name info =>
    if id.getId.isPrefixOf name then cs.push (name, info.type) else cs) #[]
  let cs := cs.qsort λ x y => nameCmp x.1 y.1 == .lt
  Lean.logInfo (.joinSep (cs.map λ (name, type) => name ++ " : " ++ type).toList Lean.Format.line)

theorem congrArg₂ (f : α → β → γ) : a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ :=
  congr ∘ congrArg f

private def Nat.rec'' {motive : Nat → Sort _} (zero : motive .zero) (succ : ∀ n, motive n → motive n.succ) : ∀ n, motive n
  | .zero => zero
  | .succ n => succ n (rec'' zero succ n)

@[implemented_by Nat.rec'']
def Nat.rec' : {motive : Nat → Sort _} → motive .zero → (∀ n, motive n → motive n.succ) → ∀ n, motive n :=
  @Nat.rec

def Nat.lt_or_eq_or_gt : ∀ n m : Nat, n < m ∨ n = m ∨ n > m
  | .zero, .zero => .inr (.inl rfl)
  | .zero, .succ b => .inl (Nat.zero_lt_succ b)
  | .succ a, .zero => .inr (.inr (Nat.zero_lt_succ a))
  | .succ a, .succ b =>
    match lt_or_eq_or_gt a b with
    | .inl h => .inl (Nat.succ_lt_succ h)
    | .inr (.inl h) => .inr (.inl (congrArg succ h))
    | .inr (.inr h) => .inr (.inr (Nat.succ_lt_succ h))

inductive Fin2 : Nat → Type
  | zero : Fin2 (.succ n)
  | succ (i : Fin2 n) : Fin2 n.succ

namespace Fin2

private def impl.rec {motive : ∀ n, Fin2 n → Sort _} (zero : ∀ {n}, motive (.succ n) zero) (succ : ∀ {n} i, motive n i → motive n.succ i.succ) {n} : ∀ i, motive n i
  | .zero => zero
  | .succ i => succ i (rec zero succ i)

attribute [implemented_by impl.rec] rec

private theorem rec.impl {zero succ n} : ∀ {i}, @rec motive @zero @succ n i = impl.rec @zero @succ i
  | .zero => rfl
  | .succ i => congrArg (succ i) impl

private def impl.withSucc {motive : ∀ n, Fin2 n → Sort _} (f : ∀ {n} i, motive (.succ n) i) {n} : ∀ i, motive n i
  | zero => f zero
  | succ i => f i.succ

@[implemented_by impl.withSucc]
protected def withSucc {motive : ∀ n, Fin2 n → Sort _} (f : ∀ {n} i, motive (.succ n) i) : ∀ {n} i, motive n i :=
  @Fin2.rec motive (f zero) λ i _ => f i.succ 

private theorem withSucc.impl : ∀ {i}, @Fin2.withSucc _ @f n i = impl.withSucc @f i
  | zero => rfl
  | succ _ => rfl

private def impl.last : {n : Nat} → Fin2 n.succ
  | .zero => zero
  | .succ _ => succ last

@[implemented_by impl.last]
def last : {n : Nat} → Fin2 n.succ :=
  @Nat.rec _ zero λ _ => succ

private theorem last.impl : ∀ {n}, @last n = @impl.last n
  | .zero => rfl
  | .succ _ => congrArg succ impl

@[simp] theorem last_zero : @last .zero = zero := rfl
@[simp] theorem last_succ : @last (.succ n) = succ last := rfl

private def impl.castSucc : Fin2 n → Fin2 n.succ
  | zero => zero
  | succ i => succ (castSucc i)

@[implemented_by impl.castSucc]
def castSucc : ∀ {n}, Fin2 n → Fin2 n.succ :=
  @rec _ (λ {n} => @zero n.succ) λ _ => succ

private theorem castSucc.impl : {i : Fin2 n} → castSucc i = impl.castSucc i
  | zero => rfl
  | succ _ => congrArg succ impl

@[simp] theorem castSucc_zero : castSucc zero = @zero (.succ n) := rfl
@[simp] theorem castSucc_succ : castSucc (succ i) = succ (castSucc i) := rfl

theorem zero_or_succ : (i : Fin2 (.succ n)) → i = zero ∨ ∃ j, i = succ j
  | .zero => .inl rfl
  | .succ _ => .inr ⟨_, rfl⟩

def last_or_castSucc : ∀ {n} i, i = @last n ⊕' Σ' j, i = castSucc j
  | .zero, .zero => .inl rfl
  | .succ _, .zero => .inr ⟨zero, rfl⟩
  | .succ _, .succ i =>
    match last_or_castSucc i with
    | .inl h => .inl (congrArg succ h)
    | .inr ⟨j, h⟩ => .inr ⟨j.succ, congrArg succ h⟩

private def impl.rec' {motive : ∀ n, Fin2 n → Sort _} (last : ∀ {n}, motive (.succ n) .last) (castSucc : ∀ {n} i, motive n i → motive n.succ i.castSucc) : ∀ {n} i, motive n i
  | .succ .zero, zero => last
  | .succ (.succ _), zero => castSucc zero (rec' last castSucc zero)
  | .succ (.succ _), succ i =>
    match last_or_castSucc i with
    | .inl h => h ▸ last
    | .inr ⟨j, h⟩ => h ▸ castSucc j.succ (rec' last castSucc j.succ)

private def impl.toNat : Fin2 n → Nat
  | zero => .zero
  | succ i => .succ (toNat i)

@[implemented_by impl.toNat]
def toNat : ∀ {n}, Fin2 n → Nat :=
  @rec _ .zero λ _ => .succ

private theorem toNat.impl : {i : Fin2 n} → toNat i = impl.toNat i
  | zero => rfl
  | succ _ => congrArg Nat.succ impl

@[simp] theorem toNat_zero : toNat (@zero n) = .zero := rfl
@[simp] theorem toNat_succ : toNat (succ i) = .succ (toNat i) := rfl

@[simp]
theorem toNat_last : ∀ {n}, (@last n).toNat = n
  | .zero => rfl
  | .succ _ => congrArg Nat.succ toNat_last

@[simp]
theorem toNat_castSucc : {i : Fin2 n} → (castSucc i).toNat = i.toNat
  | zero => rfl
  | succ _ => congrArg Nat.succ toNat_castSucc

theorem toNat.inj : {i j : Fin2 n} → toNat i = toNat j → i = j
  | .zero, .zero, _ => rfl
  | .succ _, .succ _, h => congrArg succ (inj (Nat.succ.inj h))

@[simp]
theorem toNat.injIff : toNat i = toNat j ↔ i = j :=
  ⟨inj, congrArg toNat⟩

theorem lt_toNat : (i : Fin2 n) → toNat i < n
  | .zero => Nat.zero_lt_succ _
  | .succ i => Nat.succ_lt_succ (lt_toNat i)

end Fin2

section

variable (r : α → α → Prop)

class Reflexive : Prop :=
  refl : r x x

class Symmetric : Prop :=
  symm : r x y → r y x

class Transitive : Prop :=
  trans : r x y → r y z → r x z

class Equivalence' extends Reflexive r, Symmetric r, Transitive r : Prop

inductive ReflexiveTransitiveClosure : α → α → Prop
  | base : r x y → ReflexiveTransitiveClosure x y
  | refl : ReflexiveTransitiveClosure x x
  | trans : ReflexiveTransitiveClosure x y → ReflexiveTransitiveClosure y z → ReflexiveTransitiveClosure x z

instance ReflexiveTransitiveClosure.instReflexive : Reflexive (ReflexiveTransitiveClosure r) where
  refl := @refl _ _

instance ReflexiveTransitiveClosure.instTransitive : Transitive (ReflexiveTransitiveClosure r) where
  trans := @trans _ _

inductive EquivalenceClosure : α → α → Prop
  | base : r x y → EquivalenceClosure x y
  | refl : EquivalenceClosure x x
  | symm : EquivalenceClosure x y → EquivalenceClosure y x
  | trans : EquivalenceClosure x y → EquivalenceClosure y z → EquivalenceClosure x z

instance EquivalenceClosure.instEquivalence : Equivalence' (EquivalenceClosure r) where
  refl := @refl _ _
  symm := @symm _ _
  trans := @trans _ _

end
