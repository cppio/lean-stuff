import Lean
import Sorting.List
import Sorting.Tactic

class ComparisonSort (f : ∀ {m} [Monad m] {α}, (α → α → m Bool) → List α → m (List α)) where
  perm (le : α → α → Bool) l : List.Perm (f (m := Id) le l) l
  sort (le : α → α → Bool) (hle : ∀ {x y}, ¬le x y → le y x) l : List.Chain (le · ·) (f (m := Id) le l)

section

variable {m} [Monad m] {α} (le : α → α → m Bool)

def insert (x : α) : List α → m (List α)
  | [] => return [x]
  | y :: l => do
    if ← le x y
    then return x :: y :: l
    else return y :: (← insert x l)

def insertionSort : List α → m (List α)
  | [] => return []
  | x :: l => do insert le x (← insertionSort l)

end

instance : ComparisonSort @insertionSort where
  perm le l := by
    induction l <;> simp [insertionSort]
    case cons l ih =>
      apply .trans _ (.cons _ ih)
      clear ih
      generalize insertionSort (m := Id) le l = l
      induction l <;> simp [insert]
      split <;> simp [*]

  sort le hle l := by
    induction l <;> simp [insertionSort]
    case cons l ih =>
      generalize insertionSort (m := Id) le l = l at ih
      induction l <;> simp [insert]
      case cons ih' =>
        split with h
        . simp [h, ih]
        . cases ih <;> simp [insert, hle h] at ih' ⊢
          case cons h₁ h₂ =>
            specialize ih' h₁
            split with h' <;> simp [h'] at ih' <;> simp [hle h, h₂, h', ih']

section

variable [Monad m] {α} (le : α → α → m Bool)

def select (x : α) : List α → m (α × List α)
  | [] => return (x, [])
  | y :: l => do
    if ← le x y
    then do
      let s ← select x l
      return (s.1, y :: s.2)
    else do
      let s ← select y l
      return (s.1, x :: s.2)

def selectionSort' : Nat → List α → m (List α)
  | 0, _ => return []
  | _, [] => return []
  | n + 1, x :: l => do
    let s ← select le x l
    return s.1 :: (← selectionSort' n s.2)

def selectionSort (l : List α) : m (List α) :=
  selectionSort' le l.length l

end

theorem perm_select x l : List.Perm (let s := select (m := Id) le x l; s.1 :: s.2) (x :: l) := by
  induction l generalizing x <;> simp [select]
  split <;> simp [*]

structure TotalPreorder (r : α → α → Prop) where
  trans : r x y → r y z → r x z
  total x y : r x y ∨ r y x
  refl x : r x x := (total x x).elim id id
  ofNot : ¬r x y → r y x := (total y x).elim id ∘ (False.elim ∘ ·)

theorem sort_select (le : α → α → Bool) (hle : TotalPreorder (le · ·)) x l : let s := select (m := Id) le x l; ∀ y, List.Mem y s.2 → le s.1 y := by
  induction l generalizing x <;> simp [select, List.foldr]
  case nil =>
    intro _ h
    cases h
  case cons y l ih =>
    split with h'
    . specialize ih x
      intro
      | _, .tail _ h => exact ih _ h
      | _, .head _ =>
        have := (perm_select (le := le) x l).symm.mem (.head _)
        simp at this ⊢
        generalize hz : (select (m := Id) le x l).fst = z at this
        cases this
        . exact h'
        . cases hz
          apply hle.trans (ih _ _) h'
          assumption
    . specialize ih y
      intro
      | _, .tail _ h => exact ih _ h
      | _, .head _ =>
        have := (perm_select (le := le) y l).symm.mem (.head _)
        simp at this
        generalize hz : (select (m := Id) le y l).fst = z at this
        cases this
        . exact hle.ofNot h'
        . cases hz
          apply hle.trans (ih _ _) (hle.ofNot h')
          assumption

theorem perm_selectionSort (le : α → α → Bool) l : List.Perm (selectionSort (m := Id) le l) l := by
  unfold selectionSort
  generalize hn : l.length = n
  induction n generalizing l <;> cases l <;> cases hn <;> simp [selectionSort']
  case succ ih =>
    exact .trans (.cons _ (ih _ (Nat.succ.inj (perm_select _ _).length))) (perm_select _ _)

instance : ComparisonSort @selectionSort where
  perm := perm_selectionSort

  sort le hle l := by
    unfold selectionSort
    replace hle : TotalPreorder (le · ·) := sorry
    generalize hn : l.length = n
    induction n generalizing l <;> cases l <;> cases hn <;> simp [selectionSort']
    case succ x l ih =>
      specialize ih (select (m := Id) le x l).snd (Nat.succ.inj (perm_select _ _).length)
      simp at ih
      have := sort_select le hle x l
      generalize hL : selectionSort' (m := Id) le (List.length l) (select (m := Id) le x l).2 = L at ih
      cases L with
      | nil => exact .singleton _
      | cons y L =>
        apply .cons (this _ _) ih
        have : List.Mem y (y :: L) := List.Mem.head _
        rw [← hL] at this
        rw [← Nat.succ.inj (perm_select _ _).length] at this
        exact (perm_selectionSort le (select (m := Id) le x l).snd).mem this

def isort [Monad m] (le : α → α → m Bool) : List α → m (List α)
  | [] => return []
  | l@(h :: _) => have := Inhabited.mk h; do
    let mut l := Array.mk l
    let mut i := l.size - 1
    while i > 0 do
      let x := l[i - 1]!
      let mut j := i
      while j < l.size do
        if ← le x l[j]! then break
        l := l.set! (j - 1) l[j]!
        j := j + 1
      l := l.set! (j - 1) x
      i := i - 1
    return l.data

def logLE (x y : Nat) : IO Bool := do
  IO.println s!"{x} ≤ {y}"
  return x ≤ y

#eval insertionSort logLE [1, 2, 3, 4]
#eval insertionSort logLE [4, 3, 2, 1]

#eval isort logLE [1, 2, 3, 4]
#eval isort logLE [4, 3, 2, 1]

class SetElem (cont idx) (elem dom : outParam _) extends GetElem cont idx elem dom where
  setElem (xs : cont) (i : idx) (h : dom xs i) : elem → cont

export SetElem (setElem)

def setElem! [SetElem cont idx elem dom] [Inhabited cont] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem → cont :=
  if h : _ then setElem xs i h else panic! "index out of bounds"

macro "(" x:term " with " "[" i:term "]" " := " v:term ")" : term =>
  `(setElem $x $i (by get_elem_tactic) $v)

macro "(" x:term " with " "[" i:term "]'" h:term " := " v:term ")" : term =>
  `(setElem $x $i $h $v)

macro "(" x:term " with " "[" i:term "]" noWs "!" " := " v:term ")" : term =>
  `(setElem! $x $i $v)

instance : SetElem (Array α) Nat α λ a i => i < a.size where
  setElem xs i h := xs.set ⟨i, h⟩

def FixedArray α n := { a : Array α // a.size = n }

namespace FixedArray

def idx {a : FixedArray α n} (i : Fin n) : Fin a.1.size :=
  ⟨i.1, by rw [a.2]; exact i.2⟩

def get (a : FixedArray α n) (i : Fin n) : α :=
  a.1.get (idx i)

def set (a : FixedArray α n) (i : Fin n) (v : α) : FixedArray α n :=
  ⟨a.1.set (idx i) v, (Array.size_set _ _ _).trans a.2⟩

instance : GetElem (FixedArray α n) (Fin n) α λ _ _ => True where
  getElem a i _ := a.get i

instance : GetElem (FixedArray α n) Nat α λ _ i => i < n where
  getElem a i h := a.get ⟨i, h⟩

instance [Inhabited α] : Inhabited (FixedArray α n) where
  default := ⟨⟨.replicate n default⟩, List.length_replicate n _⟩

instance : SetElem (FixedArray α n) (Fin n) α λ _ _ => True where
  setElem a i _ := a.set i

instance : SetElem (FixedArray α n) Nat α λ _ i => i < n where
  setElem a i h := a.set ⟨i, h⟩

end FixedArray

def runList (f : ∀ n, StateM (FixedArray α n) Unit) (a : List α) : List α :=
  (f a.length ⟨⟨a⟩, rfl⟩).2.1.1

namespace Magic

open Lean

scoped macro (name := m₁) "ℓ" noWs "[" i:term "]" : term => `((← get)[$i])
scoped macro (name := m₂) "ℓ" noWs "[" i:term "]" noWs "!" : term => `((← get)[$i]!)
scoped macro (name := m₃) "ℓ" noWs "[" i:term "]'" h:term : term => `((← get)[$i]'$h)

scoped macro "ℓ" noWs "[" i:term "]" " := " v:term : term => `(modify λ xs => (xs with [$i] := $v))
scoped macro "ℓ" noWs "[" i:term "]" noWs "!" " := " v:term : term => `(modify λ xs => (xs with [$i]! := $v))
scoped macro "ℓ" noWs "[" i:term "]'" h:term " := " v:term : term => `(modify λ xs => (xs with [$i]'$h := $v))

def doMacros : NameSet := .ofList [``m₁, ``m₂, ``m₃]

partial def expandDoMacros (stx : Syntax) : MacroM Syntax :=
  match stx with
  | .node info kind args => do
    if doMacros.contains kind then
      if let some stx := ← expandMacro? stx then
        return ← expandDoMacros stx
    return .node info kind (← args.mapM expandDoMacros)
  | _ => return stx

scoped macro (name := processedDoMacros) "processedDoMacros% " t:term : term => return t

def processDoMacros (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  if stx.raw.getKind == ``processedDoMacros
  then throw .unsupportedSyntax
  else do `(processedDoMacros% $(⟨← expandDoMacros stx⟩))

scoped macro_rules | `(doElem| return $t) => do `(doElem| return $(← processDoMacros t))
-- scoped macro_rules | `(doElem| $t:term) => do `(doElem| $(← processDoMacros t))
scoped macro_rules | `(doElem| $t:term) => return .node1 (← MonadRef.mkInfoFromRefPos) `Lean.Parser.Term.doExpr (← processDoMacros t)
scoped macro_rules | `(doElem| let $i := $t) => do `(doElem| let $i := $(← processDoMacros t))
scoped macro_rules | `(doElem| if $[$h :]? $c then $t $[else $e]?) => do `(doElem| if $[$h :]? $(← processDoMacros c) then $t $[else $e]?)

end Magic

theorem Nat.succ_pred' (h : 0 < n) : n - 1 + 1 = n :=
  succ_pred (ne_of_lt h).symm

theorem Nat.lt_trans' {n m k : Nat} (h₁ : n ≤ m) (h₂ : m < k) : n < k :=
  Nat.le_trans (succ_le_succ h₁) h₂

theorem Nat.pred_lt_of_lt (h : m < n) : m - 1 < n := lt_trans' (pred_le m) h
theorem Nat.pred_lt_of_le (h' : 0 < m) (h : m ≤ n) : m - 1 < n := Nat.le_trans (Nat.le_of_eq (succ_pred' h')) h

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Nat.pred_lt_of_lt; get_elem_tactic_trivial)

open Magic in
def isort' : List Nat → List Nat := runList λ n => do
  let mut i := n - 1
  while 0 < i do
    let x := ℓ[i - 1]!
    let mut j := i
    while h : j < n do
      if x ≤ ℓ[j] then break else
        ℓ[j - 1] := ℓ[j]
        j := j + 1
    ℓ[j - 1]! := x
    i := i - 1

open Magic in
def isort'' : List Nat → List Nat := runList λ n => do
  let mut i : { i // 0 < i → i - 1 < n } := ⟨n - 1, λ h => Nat.le_trans (Nat.pred_lt' h) (Nat.pred_le n)⟩
  while h : 0 < i.1 do
    let x := ℓ[i.1 - 1]'(i.2 h)
    let mut j : { j // 0 < j ∧ j ≤ n } := ⟨i.1, h, Nat.succ_pred' h ▸ i.2 h⟩
    while h : j < n do
      if x ≤ ℓ[j.1] then break else
        ℓ[j.1 - 1] := ℓ[j.1]
        j := ⟨j.1 + 1, Nat.lt.step j.2.1, h⟩
    ℓ[j.1 - 1]'(Nat.pred_lt_of_le j.2.1 j.2.2) := x
    i := ⟨i.1 - 1, λ h => Nat.le_trans (Nat.succ_le_succ (Nat.pred_le (i.1 - 1))) (i.2 (Nat.le_trans h (Nat.pred_le i.1)))⟩

def isortv (l : Array Nat) : Array Nat := Id.run do
  let mut l := l
  let mut i := l.size - 1
  while i > 0 do
    let x := l[i - 1]!
    let mut j := i
    while j < l.size do
      if x ≤ l[j]! then break
      l := l.set! (j - 1) l[j]!
      j := j + 1
    l := l.set! (j - 1) x
    i := i - 1
  return l

/-
open Lean in
partial def canPanic (name : Name) : CoreM (List Name) := do
  let rec visit parent name : StateT (NameMap Name) CoreM Unit := do
    if (← get).contains name then return
    modify (·.insert name parent)
    if let some value := (← getConstInfo name).value? then
      value.getUsedConstants.forM (visit name)
  let parents := (← visit name name .empty).2
  let root := ← do
    for name in [``panicCore, ``Array.get!, ``Array.set!] do
      if parents.contains name then
        return some name
    return none
  let mut some name := root
    | return []
  let mut names := []
  repeat
    let some parent := parents.find? name
      | break
    names := name :: names
    if name == parent then break
    name := parent
  return names
  -- change to namemap boolean, initially only known bad, and update to true each time

#eval canPanic ``isort'
-/

/-
open Lean in
partial def getUsedConstants (name : Name) : CoreM (Array Name) := do
  let rec visit name : StateT (NameSet × Array Name) CoreM Unit := do
    if (← get).1.contains name then
      return
    modify fun (visited, names) => (visited.insert name, names)
    let info ← getConstInfo name
    info.type.getUsedConstants.forM visit
    if let some value := info.value? then
      value.getUsedConstants.forM visit
    match ← getConstInfo name with
    | .axiomInfo info => modify fun (visited, names) => (visited, names.push info.name)
    | .opaqueInfo info => modify fun (visited, names) => (visited, names.push info.name)
    | .quotInfo info => modify fun (visited, names) => (visited, names.push info.name)
    | _ =>
      if isExtern (← getEnv) name then
        modify fun (visited, names) => (visited, names.push info.name)
  return (← visit name (.empty, #[])).2.2

deriving instance Repr for Lean.ExternEntry
deriving instance Repr for Lean.ExternAttrData

#eval getUsedConstants ``isort'
-/

/-
#check Lean.isStructureLike
deriving instance Repr for Lean.StructureInfo

structure Foo where
  a : Nat
  b : Nat

structure Bar extends Foo where
  {c : Nat}
  [d : Nat]

structure Baz where
  e : Bar
  f : Nat := by simp

section

open Lean

#eval show CoreM _ from do return getStructureInfo? (← getEnv) ``Foo
#eval show CoreM _ from do return getStructureInfo? (← getEnv) ``Bar
#eval show CoreM _ from do return getStructureInfo? (← getEnv) ``Baz

end
-/

/-
inductive Coroutine (Out In α : Type)
  | return (x : α)
  | yield (out : Out) (cont : In → Coroutine Out In α)

def Coroutine.bind (f : α → Coroutine Out In β) : Coroutine Out In α → Coroutine Out In β
  | .return x => f x
  | .yield out cont => .yield out λ in' => bind f (cont in')

instance : Monad (Coroutine Out In) where
  pure := .return
  bind x f := .bind f x

def M.yield (out : Out) : Coroutine Out In In :=
  .yield out .return

partial def loop [Inhabited α] [Monad m] : m α := loop

def runC [Inhabited α] [Monad m] (f : Out → m In) (co : Coroutine Out In α) : m α := do
  let mut co := co
  repeat
    match co with
    | .return x => return x
    | .yield out cont => co := cont (← f out)
  loop

macro "yield " t:term : term => `(← M.yield $t)

#check do _ := ← M.yield ()
#check do _ := yield ()

def foo : Coroutine Nat Nat Bool := do
  let x := yield 100
  return x > 5

#eval runC (λ x => do IO.println x; return x) foo
-/

/-
section

variable [I : LE α] [DecidableRel I.le]

def le [Monad m] (x y : α) : m Bool :=
  return x ≤ y

def timeLE (x y : α) : StateM Nat Bool :=
  fun n => (x ≤ y, n + 1)

def insertionSortTime (l : List α) : Nat :=
  insertionSort timeLE l 0 |>.2

end

-- this holds for any soted list

def List.rangeAux' (m : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => m :: rangeAux' (m + 1) n

def List.range' : Nat → List Nat :=
  List.rangeAux' 0

theorem List.length_rangeAux' (m) : ∀ n, length (rangeAux' m n) = n
  | 0 => rfl
  | n + 1 => congrArg _ <| length_rangeAux' (m + 1) n

theorem List.length_range' : ∀ n, length (range' n) = n :=
  length_rangeAux' 0

theorem insertM_range : insertM timeLE k (.rangeAux' (k + 1) (n + 1)) t = (.rangeAux' k (n + 2), t + 1) := by
  simp [insertM, timeLE, k.le_succ]
  rfl

theorem insertionSortM_range : insertionSortM timeLE (.rangeAux' k (n + 1)) t = (.rangeAux' k (n + 1), t + n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    unfold insertionSortM List.rangeAux'
    simp [bind, StateT.bind, ih]
    exact insertM_range

example (n : Nat) : ∃ l : List Nat, l.length = n ∧ insertionSortTime l = n - 1 :=
  .intro (.range' n) <| .intro (List.length_range' n) <| by
    cases n with
    | zero => rfl
    | succ n => simp [insertionSortTime, List.range', insertionSortM_range, Nat.succ_sub_succ]

theorem List.length_iota : ∀ n, length (iota n) = n
  | 0 => rfl
  | n + 1 => congrArg _ <| length_iota n

theorem insertM_iota : insertM timeLE (k + 1) (.iota k) t = (.iota (k + 1), t + k) := by
  sorry

example (n : Nat)

#eval List.range 5

#eval insertionSortTime [1]
#eval insertionSortTime [4, 3, 2, 1, 6]
-/

/-
@[simp]
def List.concatMap (f : α → List β) : List α → List β
  | [] => []
  | x :: l => f x ++ concatMap f l

instance : Monad List where
  pure x := [x]
  bind l := l.concatMap

def maxLE (_ _ : α) : StateT Nat List Bool :=
  fun n => [(false, n + 1), (true, n + 1)]

def insertionSortTime' (n : Nat) : Nat :=
  insertionSort maxLE (.range n) 0 |>.foldl (fun x (_, y) => .max x y) 0

def ContT (r : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m r) → m r

instance [Monad m] : Monad (ContT r m) where
  pure x k := k x
  bind f g k := f λ x => g x k

abbrev Cont (r : Type u) (α : Type v) := ContT r Id α

def maxLE' (_ _ : α) : Cont Nat Bool :=
  λ k =>
    let r : Nat := k false
    let s : Nat := k true
    max r s + 1

def maxLE'' (_ _ : α) : Cont (Nat × List α) Bool :=
  λ k =>
    let r := k false
    let s := k true
    if r.1 ≤ s.1
    then (s.1 + 1, s.2)
    else (r.1 + 1, r.2)

#eval insertionSort maxLE (.range 5) 0
#eval insertionSort maxLE' (.range 5) λ _ => 0
#eval insertionSort maxLE'' (.range 5) λ l => (0, l)
-/
