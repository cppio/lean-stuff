import Common.Meta
import Rec

#compile Nat

def foo.a := "sorry"
private def foo.b := "sorry"

universe u_1 u in
variable {α : Sort u} {r : α → α → Prop} {motive : ∀ x, Acc r x → Sort u_1} (intro : ∀ x h, (∀ y hy, motive y (h y hy)) → motive x (.intro x h)) in
unsafe def Acc.rec' {x} hx : motive x hx :=
  have : ∀ y, r y x → Acc r y := λ y hy => @rec α r (λ x _ => r y x → Acc r y) (λ _ h _ => h y) x hx hy
  intro x this λ y hy => @rec' y (this y hy)

@[csimp]
unsafe def Acc.rec_eq_rec' : @rec = @rec' := by
  funext α r motive intro x hx
  show _ = intro ..
  induction hx with
  | intro x h ih =>
    dsimp
    apply congrArg (intro x h)
    funext y hy
    exact ih y hy

#eval Lean.compileDecls [``WellFounded.fixF, ``WellFounded.fix]

example := @WellFounded.fixF

#check Acc.rec'

#check @Acc.rec = @Acc.rec'

#check Acc.intro
#print Acc
/-
variable {α : Sort u} (r : α → α → Prop)

def wellFounded := ∀ P : α → Prop, (∀ x, (∀ y, r y x → P y) → P x) → ∀ x, P x

def Nat.lt_wellFounded : wellFounded Nat.lt := by
  intro P h
  --suffices ∀
  -/

--#reduce @WellFounded.fix Nat (λ _ => Nat) Nat.lt Nat.lt_wfRel.wf (λ | 0, _ => 0 | 1, _ => 1 | n + 2, fib => fib (n + 1) .refl + fib n (.step .refl))


def Nat.lt_wf : WellFounded Nat.lt :=
  ⟨rec ⟨_, λ x => @Nat.le.rec x.succ (λ y _ => y.rec (Acc Nat.lt x) λ _ _ => True) ⟨⟩ (λ _ _ => ⟨⟩) .zero⟩ λ x ih => ⟨_, λ y h =>
    --@Nat.le.rec y.succ (λ _ _ => Acc Nat.lt y) (sorry) sorry x.succ h
    by cases h with | refl => exact ih | step h => cases ih with | _ A B => exact B y h
  ⟩⟩

set_option pp.all true in
#reduce @Nat.lt_wf

noncomputable def foo {C : Nat → Sort u} : (∀ x, (∀ y, y < x → C y) → C x) → ∀ x, C x :=
  @WellFounded.fix Nat C Nat.lt Nat.lt_wfRel.wf

#reduce @foo

/-
by
  apply WellFounded.intro
  intro n
  induction n with
  | zero      =>
    apply Acc.intro 0
    intro _ h
    apply absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    apply Acc.intro (Nat.succ n)
    intro m h
    have : m = n ∨ m < n := Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)
    match this with
    | Or.inl e => subst e; assumption
    | Or.inr e => exact Acc.inv ih e
    -/

--set_option pp.all true in
--#reduce* @foo.{0}

/-
variable {motive : Nat → Prop}

theorem Nat.induction (zero : motive zero) (succ : ∀ n, motive n → motive (succ n)) : ∀ n, motive n :=
  @rec motive zero succ

--#print Acc
--#print WellFounded

theorem Nat.strongInduction (h : ∀ n, (∀ m, m < n → motive m) → motive n) n : motive n :=
  @rec (λ n => ∀ m, m < n → motive m) (λ _ hm => nomatch hm) (λ n hn m hm => by cases hm with | refl => exact h n hn | step hm => exact hn m hm) n.succ n n.lt_succ_self
  -/

inductive Ordinal
  | zero
  | limit (os : Nat → Ordinal)

universe u in
variable {motive : Ordinal → Sort u} (zero : motive .zero) (limit : ∀ os, (∀ n, motive (os n)) → motive (.limit os)) in
unsafe def Ordinal.rec' : ∀ o, motive o
  | .zero => zero
  | .limit os => limit os λ n => rec' (os n)

@[csimp]
unsafe def Ordinal.rec_eq_rec' : @rec = @rec' := by
  funext motive zero limit o
  induction o with
  | zero => rfl
  | limit os hos => exact congrArg (limit os) (funext hos)

def Ordinal.succ (o : Ordinal) : Ordinal :=
  limit λ _ => o

def Ordinal.add (o : Ordinal) : Ordinal → Ordinal
  | zero => o
  | limit os => limit λ n => add o (os n)

class OrdinalSize (α : Sort u) where
  size : α → Ordinal

instance : OrdinalSize Nat where
  size := Nat.rec .zero λ _ => .succ

def ω : Ordinal :=
  .limit OrdinalSize.size

inductive Ordinal.le : Ordinal → Ordinal → Prop
  | refl : le o o
  | step : le o (os n) → le o (limit os)

inductive Ordinal.le' : Ordinal → Ordinal → Prop
  | zero : le' zero o
  | limit : (∀ n, le' (os n) (os' n)) → le' (limit os) (limit os')

theorem Ordinal.size_le_iff_le {x y : Nat} : le (OrdinalSize.size x) (OrdinalSize.size y) ↔ x ≤ y := by
  constructor
  . generalize hx : OrdinalSize.size x = x'
    generalize hy : OrdinalSize.size y = y'
    intro h
    induction h generalizing y with cases hx
    | refl =>
      have : y = x := by
        induction x generalizing y with
        | zero => cases y with | zero => rfl | succ y => cases hy
        | succ x hx => cases y with | zero => cases hy | succ y => exact congrArg Nat.succ <| hx <| congrFun (limit.inj hy) 0
      cases this
      exact Nat.le.refl
    | step hx' ih => cases y with | zero => cases hy | succ y => exact .step <| ih <| congrFun (limit.inj hy) _
  . intro h
    induction h with
    | refl => exact .refl
    | step _ ih => exact .step (n := 0) ih

/-
inductive Ordinal
  | zero : Ordinal
  | succ : Ordinal → Ordinal
  | limit : (Nat → Ordinal) → Ordinal

universe u in
variable {motive : Ordinal → Sort u} (zero : motive .zero) (succ : ∀ o, motive o → motive o.succ) (limit : ∀ os, (∀ n, motive (os n)) → motive (.limit os)) in
unsafe def Ordinal.rec' : ∀ o, motive o
  | .zero => zero
  | .succ o => succ o (rec' o)
  | .limit os => limit os λ n => rec' (os n)

@[csimp]
unsafe def Ordinal.rec_eq_rec' : @rec = @rec' := by
  funext motive zero succ limit o
  induction o with
  | zero => rfl
  | succ o ho => exact congrArg (succ o) ho
  | limit os hos => exact congrArg (limit os) (funext hos)

inductive Ordinal.lt : Ordinal → Ordinal → Prop
  | zero_succ : lt zero (succ o)
  | zero_limit : lt zero (limit os)
  | succ : lt o o' → lt (succ o) (succ o')
  | limit : (∀ n, lt (os n) (os' n)) → lt (limit os) (limit os')

class OrdinalSize (α : Sort u) where
  size : α → Ordinal

instance : OrdinalSize Nat where
  size := Nat.rec .zero λ _ => .succ

inductive Nat.Le : Nat → Nat → Prop
  | zero : Le zero n
  | succ : Le a b → Le (succ a) (succ b)

example : Nat.Le a b ↔ Nat.le a b := by
  induction a generalizing b with
  | zero => exact ⟨λ _ => b.zero_le, λ _ => .zero⟩
  | succ a ih => exact ⟨λ | .succ h => Nat.succ_le_succ (ih.mp h), λ h => match b with | .succ b => .succ (ih.mpr (Nat.le_of_succ_le_succ h))⟩
-/

def Acc.eta {α : Sort u} {r : α → α → Prop} {x : α} (h : Acc r x) : Acc r x :=
  @Acc.intro α r x (@Acc.rec α r (λ x _ => ∀ y, r y x → Acc r y) (λ _ h _ => h) x h)

unsafe def loop := @Acc.rec Nat Nat.lt (λ _ _ => Nat) λ x _ ih => 1

variable (h : Acc Nat.lt 0)

#eval @loop 0 sorry
#reduce loop h

unsafe def bar : loop h = 1 := calc
  loop h = loop h.eta := rfl
       _ = 1          := rfl
