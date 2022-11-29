import Lean.Elab.Command
import Lean

open Lean

partial def getApp : Term → Term × Array Term
  | `($t $ts*) => let (hd, tl) := getApp t; (hd, tl ++ ts)
  | `(($t)) => getApp t
  | stx => (stx, #[])

partial def cps' (i : Ident) (n : Nat) (a : Array Term → MacroM Term) (stx : Term) : MacroM ((Term → MacroM Term) × Term) :=
  let (hd, tl) := getApp stx
  if hd == i then
    if tl.size < n
    then throw <| .error stx "function not fully applied"
    else do
      let (bs₁, tl₁) ← tl[:n].foldlM (λ (binds, tl) x => do
        let (bind, y) ← cps' i n a x
        return (binds <=< bind, tl.push y)
      ) (pure, .mkEmpty n)
      let tl₁ ← a tl₁
      let (bs₂, tl₂) ← tl[n:].foldlM (λ (binds, tl) x => do
        let (bind, y) ← cps' i n a x
        return (binds <=< bind, tl.push y)
      ) (pure, .mkEmpty (tl.size - n))
      let b ← withFreshMacroScope `(__do_lift)
      return (bs₁ <=< (λ bd => `($tl₁ >>= λ $b => $bd)) <=< bs₂, ← `($b $tl₂*))
  else if let `(← $e) := stx then do
    let (be, e) ← cps' i n a e
    let b ← withFreshMacroScope `(__do_lift)
    return (be <=< (λ bd => `($e >>= λ $b => $bd)), b)
  else if let `(if $c then $t else $e) := stx then do
    let (bc, c) ← cps' i n a c
    let (bt, t) ← cps' i n a t
    let (be, e) ← cps' i n a e
    let t ← bt <| ← `(pure $t)
    let e ← be <| ← `(pure $e)
    let b ← withFreshMacroScope `(__do_lift)
    return (bc <=< λ bd => `((if $c then $t else $e) >>= λ $b => $bd), b)
  else if let `(match $[$d],* with $[| $[$lhs,*]|* => $rhs]*) := stx then do
    let (bd, d) ← d.foldlM (λ (bd, d) arg => do
      let (bind, arg') ← cps' i n a ⟨arg.raw[1]⟩
      return (bd <=< bind, d.push ⟨arg.raw.setArg 1 arg'⟩)
    ) (pure, .mkEmpty d.size)
    let rhs ← rhs.mapM λ rhs => do
      let (brhs, rhs) ← cps' i n a rhs
      brhs <| ← `(pure $rhs)
    let b ← withFreshMacroScope `(__do_lift)
    return (bd <=< λ bd => `((match $[$d],* with $[| $[$lhs,*]|* => $rhs]*) >>= λ $b => $bd), b)
  else do
    let (binds, args) ← stx.raw.getArgs.foldlM (λ (binds, args) arg => do
      let (bind, arg) ← cps' i n a ⟨arg⟩
      return (binds <=< bind, args.push arg.raw)
    ) (pure, .mkEmpty stx.raw.getNumArgs)
    return (binds, ⟨stx.raw.setArgs args⟩)

def cps (i : Ident) (n : Nat) (a : Array Term → MacroM Term := λ a => `($i $a*)) (t : Term) : MacroM Term := do
  let (b, t) ← cps' i n a t
  b <| ← `(pure $t)

/-
macro "cps% " i:ident n:num t:term : term => (cps i n.getNat) t
-/

/-
elab "#cps " i:ident n:num t:term : command => do
  let t' ← Elab.liftMacroM <| (cps i n.getNat) t
  logInfoAt t t'
-/

/-
elab tk:"#expand " t:term : command => do
  let t ← Elab.liftMacroM <| expandMacros t
  logInfoAt tk t
-/

def Function.curry (f : α × β → δ) (x : α) (y : β) : δ := f (x, y)

structure Fix (α : Sort u) (C : α → Type v) [I : WellFoundedRelation α] (m : Type v → Type w) [Monad m] where
  fix : (∀ x, (∀ y, I.rel y x → m (C y)) → m (C x)) → ∀ x, C x

open Lean.Parser in
@[command_parser]
def fdef := leading_parser
  "fdef " >> ident >> " : " >> termParser >> Term.matchAlts

macro_rules
  | `(fdef $n : $t₁ → $t₂ $[| $[$l,*]|* => $r]*) => do
    let ns := r.map λ _ => n
    let rs ← r.mapM <| cps n 1 (λ a => `($n $a* (by decreasing_tactic)))
    let m := mkIdent `m
    let fix := mkIdent `fix
    `(def $n [Monad $m] {$fix : Fix $t₁ (λ _ => $t₂) $m} : $t₁ → $t₂ := $(fix).fix λ
      $[| $[$l,*]|* => λ $ns => $rs]*)

macro_rules
  | `(fdef $n : $t₁ → $t₂ → $t₃ $[| $[$l₁, $l₂]|* => $r]*) => do
    let ns := r.map λ _ => n
    let rs ← r.mapM <| cps n 2 (λ a => `($n ($(a[0]!), $(a[1:]),*) (by decreasing_tactic)))
    let m := mkIdent `m
    let fix := mkIdent `fix
    `(def $n [Monad $m] {$fix : Fix ($t₁ × $t₂) (λ _ => $t₃) $m} : $t₁ → $t₂ → $t₃ := Function.curry <| $(fix).fix λ
      $[| $[($l₁, $l₂)]|* => λ $ns => $rs]*)

private def WellFounded.fix' {α : Sort u} {C : α → Sort v} {r} (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) x : C x :=
  F x λ y _ => fix' hwf F y
termination_by' ⟨r, hwf⟩

@[csimp]
private theorem WellFounded.fix_eq_fix' : @fix = @fix' := by
  funext _ _ _ _ _ _
  unfold WellFounded.fix'
  apply fix_eq

def Fix.basic {α : Sort u} {C : α → Type v} [I : WellFoundedRelation α] : Fix α C Id where
  fix := WellFounded.fix I.wf

def Fix.memo {α : Type u} {β : Type (max u v)} [I : WellFoundedRelation α] [Ord α] : Fix α (λ _ => β) (StateM (Lean.RBMap α β compare)) where
  fix f := StateT.run' (s := .empty) ∘ WellFounded.fix I.wf λ x ih m =>
    match m.find? x with
    | some y => (y, m)
    | none =>
      let (y, m) := f x ih m
      (y, m.insert x y)

def Fix.dbgTrace {α : Type u} {C : α → Type v} [WellFoundedRelation α] {m : Type v → Type w} [Monad m] (fix : Fix α C m) [ToString α] : Fix α C m where
  fix f := fix.fix λ x => dbg_trace s!"f {x}"; f x

fdef fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#eval fib (fix := .dbgTrace .basic) 6
#eval fib (fix := .dbgTrace .memo) 6

instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y :=
    match compare x.1 y.1 with
    | .eq => compare x.2 y.2
    | o => o

fdef ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

#eval ack (fix := .dbgTrace .basic) 2 1
#eval ack (fix := .dbgTrace .memo) 2 1

def le (x y : Nat) : Bool :=
  dbg_trace s!"{x} ≤ {y}"
  x ≤ y

def insert' : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: l =>
    if le x y
    then x :: y :: l
    else y :: insert' x l

fdef insert : Nat → List Nat → List Nat
  | x, [] => [x]
  | x, y :: l =>
    if le x y
    then x :: y :: l
    else y :: insert x l

#eval insert' 2 [1, 3, 4]
#eval insert (fix := .dbgTrace .basic) 2 [1, 3, 4]

open Lean.Parser in
@[command_parser]
def mdef := leading_parser
  "mdef " >> ident >> " : " >> termParser >> Term.matchAlts

macro_rules
  | `(mdef $n : $t₁ → $t₂ $[| $[$l,*]|* => $r]*) => do
    let rs ← r.mapM <| cps n 1
    `(def $n : $t₁ → $t₂ := λ
      $[| $[$l,*]|* => $rs]*)

def mul (x y : Nat) : Nat :=
  dbg_trace s!"{x} * {y}"
  x * y

mdef prod' : List Nat → Option Nat
  | [] => 1
  | x :: l =>
    if x == 0
    then ← none
    else x |> mul <| prod' l

def prod l := prod' l |>.getD 0

#eval prod [1, 2, 3, 4, 5]
#eval prod [0, 2, 3, 4, 5]
#eval prod [1, 2, 3, 4, 0]
