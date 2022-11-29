import Rec

def Fin.zero : Fin (.succ n) :=
  ⟨0, n.zero_lt_succ⟩

def Fin.last : Fin (.succ n) :=
  ⟨n, n.lt_succ_self⟩

def Fin.castSucc : Fin n → Fin n.succ
  | ⟨i, h⟩ => ⟨i, .step h⟩

def String.joinSep l sep := join (List.intersperse sep l)

/-
def Fin.cast (h' : k ≤ n) : Fin k → Fin n
  | ⟨i, h⟩ => ⟨i, Nat.le_trans h h'⟩

def Fin.cases {α : Fin (n + 1) → Sort u} (zero : α .zero) (succ : ∀ i, α (Fin.succ i)) : ∀ i, α i
  | ⟨0, _⟩ => zero
  | ⟨i + 1, h⟩ => succ ⟨i, Nat.pred_le_pred h⟩

def Fin.revCases {α : Fin (n + 1) → Sort u} (last : α .last) (castSucc : ∀ i, α (Fin.castSucc i)) : ∀ i, α i
  | ⟨i, h⟩ =>
    if h' : i = n
    then by simp [h']; exact last
    else castSucc ⟨i, Nat.lt_of_le_of_ne (Nat.pred_le_pred h) h'⟩

namespace FinTuple

def foldr' {α : Fin n → Sort u} (f : ∀ {i}, Nat → α i → β → β) (y : β) (xs : ∀ i, α i) : β :=
  foldr (λ x (y, k) => (f k x y, k + 1)) (y, 0) xs |>.1

def dfoldr {α : Fin n → Sort u} {β : Fin (n + 1) → Sort v} (f : ∀ {i}, α i → β i.succ → β i.castSucc) (y : β .last) (xs : ∀ i, α i) : β .zero :=
  match n with
  | 0 => y
  | _ + 1 => f (xs .zero) (dfoldr (β := β ∘ .succ) f y (xs ·.succ))

def dfoldl {α : Fin n → Sort u} {β : Fin (n + 1) → Sort v} (f : ∀ {i}, β i.castSucc → α i → β i.succ) (y : β .zero) (xs : ∀ i, α i) : β .last :=
  match n with
  | 0 => y
  | _ + 1 => dfoldl (β := β ∘ .succ) (f ·) (f (i := .zero) y (xs .zero)) (xs ·.succ)

def toStringAux : ∀ {n} {α : Fin n → Type u} [∀ i, ToString (α i)], Bool → (∀ i, α i) → String
  | 0, _, _, _, _ => ""
  | _ + 1, _, _, true, xs => toString (xs 0) ++ toStringAux false (xs ·.succ)
  | _ + 1, _, _, false, xs => ", " ++ toString (xs 0) ++ toStringAux false (xs ·.succ)

instance {α : Fin n → Type u} [∀ i, ToString (α i)] : ToString (∀ i, α i) where
  toString xs := "⟦" ++ toStringAux true xs ++ "⟧"

macro "⟦" t:term,* "⟧'" : term => `(@Sigma.mk Nat ((_ : Fin ·) → _) _ ⟦$t,*⟧)

end FinTuple
-/

namespace FinTuple

def nil {α : Fin 0 → Sort u} i : α i := nomatch i

def cons {α : Fin (.succ n) → Sort u} (x : α .zero) (xs : ∀ i, α (.succ i)) : ∀ i, α i
  | ⟨0, _⟩ => x
  | ⟨i + 1, h⟩ => xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

scoped syntax "⟦" term,* "⟧" : term

macro_rules
  | `(⟦⟧)          => ``(nil)
  | `(⟦$x⟧)        => ``(cons $x ⟦⟧)
  | `(⟦$x, $xs,*⟧) => ``(cons $x ⟦$xs,*⟧)

@[app_unexpander nil]
protected def nilUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => ``(⟦⟧)
  | _           => throw ()

@[app_unexpander cons]
protected def consUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $x ⟦⟧)      => ``(⟦$x⟧)
  | `($_ $x ⟦$xs,*⟧) => ``(⟦$x, $xs,*⟧)
  | _                => throw ()

def foldr {α : Fin n → Sort u} {β : Sort v} (f : ∀ {i}, α i → β → β) (y : β) (xs : ∀ i, α i) : β :=
  match n with
  | 0 => y
  | _ + 1 => f (xs .zero) (foldr f y (xs ·.succ))

def foldl {α : Fin n → Sort u} {β : Sort v} (f : ∀ {i}, β → α i → β) (y : β) (xs : ∀ i, α i) : β :=
  match n with
  | 0 => y
  | _ + 1 => foldl f (f y (xs .zero)) (xs ·.succ)

def toList : (Fin n → α) → List α :=
  foldr .cons .nil

end FinTuple

variable {α : Type u} (β : α → Sort v) in
inductive DList : List α → Sort _
  | nil : DList []
  | cons : β a → DList as → DList (a :: as)

namespace DList

scoped syntax "⟦" term,* "⟧" : term

macro_rules
  | `(⟦⟧)          => ``(nil)
  | `(⟦$x⟧)        => ``(cons $x ⟦⟧)
  | `(⟦$x, $xs,*⟧) => ``(cons $x ⟦$xs,*⟧)

@[app_unexpander nil]
protected def nilUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_) => ``(⟦⟧)

@[app_unexpander cons]
protected def consUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $x ⟦⟧)      => ``(⟦$x⟧)
  | `($_ $x ⟦$xs,*⟧) => ``(⟦$x, $xs,*⟧)
  | _                => throw ()

variable {α : Type u} {β₁ : α → Type v₁} {β₂ : α → Type v₂} (f : ∀ {a}, β₁ a → β₂ a) in
def map : DList β₁ as → DList β₂ as
  | nil => nil
  | cons x xs => cons (f x) (map xs)

variable {α : Type u} {β : α → Sort v} {γ : Sort w} (f : ∀ {a}, β a → γ → γ) (y : γ) in
def foldr : DList β as → γ
  | nil => y
  | cons x xs => f x (foldr xs)

def toList : DList (λ _ => α) as → List α :=
  foldr .cons .nil

end DList

structure Var (s : α) where
  x : Nat

instance : DecidableEq (Var s)
  | ⟨x⟩, ⟨y⟩ =>
    if h : x = y
    then isTrue (congrArg Var.mk h)
    else isFalse (h ∘ congrArg Var.x)

instance : OfNat (Var s) n := ⟨⟨n⟩⟩

protected partial def Var.toString : Var s → String
  | ⟨x⟩ => ⟨f x []⟩
where f x s :=
  let s := Char.ofNat ('a'.toNat + x % 26) :: s
  match x / 26 with
  | 0 => s
  | q + 1 => f q s

instance : ToString (Var s) := ⟨Var.toString⟩

instance : Coe String (Var s) where
  coe s := ⟨s.foldl (λ x c => (x + 1) * 26 + (c.toNat - 'a'.toNat).min 25) 0 - 26 ^ s.length⟩

/-
syntax "ast " ident " where " (ident (" | " ident term*)*)* : command
macro_rules
  | `(ast $l where $[$s $[| $o $[$a]*]*]*) => do
    let is ← (s.zip (o.zip a)).mapM λ (s, (o, a)) =>
      `(inductive $s)
    `(namespace $l $(⟨Lean.mkNullNode is⟩) end $l)

set_option trace.Elab.command true in
ast Example where
  Exp
  | var Var
  | num "[" Nat "]"
  | plus "(" Exp "; " Exp ")"
  | times "(" Exp "; " Exp ")"
-/

namespace Example

inductive Exp
  | var : Var Exp → Exp
  | num : Nat → Exp
  | plus : Exp → Exp → Exp
  | times : Exp → Exp → Exp

instance : ToString Exp where
  toString := toString
where
  toString
  | .var x => x.toString
  | .num n => s!"num[{n}]"
  | .plus e₁ e₂ => s!"plus({toString e₁}; {toString e₂})"
  | .times e₁ e₂ => s!"times({toString e₁}; {toString e₂})"

namespace Exp

variable (e : Exp) (x : Var Exp) in
def substExp : Exp → Exp
  | var y => if y = x then e else .var y
  | num n => num n
  | plus e₁ e₂ => plus (substExp e₁) (substExp e₂)
  | times e₁ e₂ => times (substExp e₁) (substExp e₂)

#eval plus (num 2) (times (num 3) (var 0))
#eval substExp (num 2) 0 (plus (var 0) (var 1))

end Exp

end Example

variable {S : Type} (O : List S → S → Type) in
inductive Ast : S → Type
  | var (x : Var s) : Ast s
  | op (o : O si s) (ai : DList Ast si) : Ast s

#compile mutual Ast

namespace Ast

def ndrec
  {motive : S → Type u}
  (var : ∀ {s}, Var s → motive s)
  (op : ∀ {si s}, O si s → DList (Ast O) si → DList motive si → motive s)
: ∀ {s}, Ast O s → motive s :=
  @rec S O (λ s _ => motive s) (λ si _ => DList motive si) var op DList.nil λ _ _ => DList.cons

def subst [DecidableEq S] {s : S} (a : Ast O s) (x : Var s) : Ast O t → Ast O t :=
  ndrec
    (λ {t} y => if h : t = s then if h ▸ y = x then h ▸ a else var y else var y)
    (λ o _ ai' => op o ai')

protected def toString [∀ si s, ToString (O si s)] : Ast O s → String :=
  ndrec
    (λ x => x.toString)
    (λ | o, .nil, _ => toString o
       | o, _, ai' => toString o ++ "(" ++ .joinSep ai'.toList "; " ++ ")")

end Ast

instance [∀ si s, ToString (O si s)] : ToString (Ast O s) := ⟨Ast.toString⟩

variable {S : Type} (O : ∀ ⦃n⦄, (Fin n → S) → S → Type) in
inductive Ast' : S → Type
  | var (x : Var s) : Ast' s
  | op (o : @O n si s) (ai : ∀ i, Ast' (si i)) : Ast' s

namespace Ast'

variable [DecidableEq S] {s : S} (a : Ast' O s) (x : Var s) in
def subst : Ast' O t → Ast' O t
  | var y => if h : t = s then if h ▸ y = x then h ▸ a else var y else var y
  | op o ai => op o λ i => subst (ai i)

protected def toString [∀ {n} si s, ToString (@O n si s)] : Ast' O s → String
  | var x => x.toString
  | op (n := 0) o _ => toString o
  | op o ai => toString o ++ "(" ++ .joinSep (FinTuple.toList λ i => (ai i).toString) "; " ++ ")"

end Ast'

instance [∀ {n} si s, ToString (@O n si s)] : ToString (Ast' O s) := ⟨Ast'.toString⟩

namespace ExampleAst

open DList

inductive S
  | Exp
deriving DecidableEq

inductive O : List S → S → Type
  | num : Nat → O [] .Exp
  | plus : O [.Exp, .Exp] .Exp
  | times : O [.Exp, .Exp] .Exp

instance : ToString (O si s) where
  toString
  | .num n => s!"num[{n}]"
  | .plus => "plus"
  | .times => "times"

abbrev Ast := _root_.Ast O

abbrev Exp := Ast .Exp

namespace Exp

def var (x : Var S.Exp) : Exp := .var x
def num (n : Nat) : Exp := .op (.num n) ⟦⟧
def plus (a b : Exp) : Exp := .op .plus ⟦a, b⟧
def times (a b : Exp) : Exp := .op .times ⟦a, b⟧

#eval plus (num 2) (times (num 3) (var 0))
#eval Ast.subst (num 2) 0 (plus (var 0) (var 1))

end Exp

end ExampleAst

namespace ExampleAst'

open FinTuple

inductive S
  | Exp
deriving DecidableEq

inductive O : ∀ ⦃n⦄, (Fin n → S) → S → Type
  | num : Nat → O ⟦⟧ .Exp
  | plus : O ⟦.Exp, .Exp⟧ .Exp
  | times : O ⟦.Exp, .Exp⟧ .Exp

instance : ToString (O si s) where
  toString
  | .num n => s!"num[{n}]"
  | .plus => "plus"
  | .times => "times"

abbrev Ast := _root_.Ast' O

abbrev Exp := Ast .Exp

namespace Exp

def var (x : Var S.Exp) : Exp := .var x
def num (n : Nat) : Exp := .op (.num n) ⟦⟧
def plus (a b : Exp) : Exp := .op .plus ⟦a, b⟧
def times (a b : Exp) : Exp := .op .times ⟦a, b⟧

#eval plus (num 2) (times (num 3) (var 0))
#eval Ast'.subst (num 2) 0 (plus (var 0) (var 1))

end Exp

end ExampleAst'

variable {S : Type} (O : List (List S × S) → S → Type) in
inductive Abt₁ : S → Type
  | bvar s (n : Nat) : Abt₁ s
  | var (x : Var s) : Abt₁ s
  | op (o : O si s) (ai : DList (Abt₁ ·.2) si) : Abt₁ s

#compile mutual Abt₁

namespace Abt₁

def ndrec
  {motive : S → Type u}
  (bvar : ∀ s, Nat → motive s)
  (var : ∀ {s}, Var s → motive s)
  (op : ∀ {si s}, O si s → DList (Abt₁ O ·.2) si → DList (motive ·.2) si → motive s)
: ∀ {s}, Abt₁ O s → motive s :=
  @rec S O (λ s _ => motive s) (λ si _ => DList (motive ·.2) si) bvar var op DList.nil λ _ _ => DList.cons (α := _ × S) (β := (motive ·.2))

end Abt₁

variable {S : Type} (O : ∀ ⦃n⦄, (Fin n → List S × S) → S → Type) in
inductive Abt₂ : S → Type
  | bvar s (n : Nat) : Abt₂ s
  | var (x : Var s) : Abt₂ s
  | op (o : @O n si s) (ai : ∀ i, Abt₂ (si i).2) : Abt₂ s

variable {S : Type} (O : ∀ ⦃n⦄, (Fin n → ((m : Nat) × (Fin m → S)) × S) → S → Type) in
inductive Abt₃ : S → Type
  | bvar s (n : Nat) : Abt₃ s
  | var (x : Var s) : Abt₃ s
  | op (o : @O n si s) (ai : ∀ i, Abt₃ (si i).2) : Abt₃ s

def Abt₁.subst [DecidableEq S] {s : S} (a : Abt₁ O s) (x : Var s) : Abt₁ O t → Abt₁ O t :=
  ndrec
    (λ t n => bvar t n)
    (λ {t} y => if h : t = s then if h ▸ y = x then h ▸ a else var y else var y)
    (λ o _ ai' => op o ai')

variable [DecidableEq S] {s : S} (a : Abt₂ O s) (x : Var s) in
def Abt₂.subst : Abt₂ O t → Abt₂ O t
  | bvar t n => bvar t n
  | var y => if h : t = s then if h ▸ y = x then h ▸ a else var y else var y
  | op o ai => op o λ i => subst (ai i)

variable [DecidableEq S] {s : S} (a : Abt₃ O s) (x : Var s) in
def Abt₃.subst : Abt₃ O t → Abt₃ O t
  | bvar t n => bvar t n
  | var y => if h : t = s then if h ▸ y = x then h ▸ a else var y else var y
  | op o ai => op o λ i => subst (ai i)

variable [DecidableEq S] (s : S) in
def bindCount : List S → Nat
  | [] => 0
  | t :: ts => bindCount ts + if t = s then 1 else 0

variable {S : Type u} [DecidableEq S] (s : S) in
def bindCount' : ((m : Nat) × (Fin m → S)) → Nat
  | ⟨0, _⟩ => 0
  | ⟨m + 1, ts⟩ => bindCount' ⟨m, ts ∘ .succ⟩ + if ts .zero = s then 1 else 0

def Abt₁.bind [DecidableEq S] {s : S} (x : Var s) : @Abt₁ S O t → Nat → Abt₁ O t :=
  ndrec (motive := λ t => Nat → Abt₁ O t)
    (λ t m _ => bvar t m)
    (λ {t} y n => if h : t = s then if h ▸ y = x then bvar t n else var y else var y)
    (λ o _ ai' n => op o (ai'.map λ {b} f => f (n + bindCount s b.1)))

variable [DecidableEq S] {s : S} (x : Var s) in
def Abt₂.bind (n : Nat) : @Abt₂ S O t → Abt₂ O t
  | bvar t m => bvar t m
  | var y => if h : t = s then if h ▸ y = x then bvar t n else var y else var y
  | op (si := si) o ai => op o λ i => bind (n + bindCount s (si i).1) (ai i)

variable [DecidableEq S] {s : S} (x : Var s) in
def Abt₃.bind (n : Nat) : @Abt₃ S O t → Abt₃ O t
  | bvar t m => bvar t m
  | var y => if h : t = s then if h ▸ y = x then bvar t n else var y else var y
  | op (si := si) o ai => op o λ i => bind (n + bindCount' s (si i).1) (ai i)

def Abt₁.op' [DecidableEq S] {s : S} (o : O si s) (ai : DList (λ b => DList Var b.1 × Abt₁ O b.2) si) : Abt₁ O s :=
  .op o <| ai.map λ a => a.1.foldr (λ {t} x (a, n) => (bind x a (n t), λ u => if u = t then n u + 1 else n u)) (a.2, λ _ : S => 0) |>.1

def Abt₂.op' [DecidableEq S] {s : S} (o : O si s) (ai : ∀ i, DList Var (si i).1 × Abt₂ O (si i).2) : Abt₂ O s :=
  .op o λ i => (ai i).1.foldr (λ {t} x (a, n) => (bind x (n t) a, λ u => if u = t then n u + 1 else n u)) ((ai i).2, λ _ : S => 0) |>.1

def Abt₃.op' [DecidableEq S] {s : S} (o : O si s) (ai : ∀ i, (∀ j, Var ((si i).1.2 j)) × Abt₃ O (si i).2) : Abt₃ O s :=
  .op o λ i => FinTuple.foldr (λ {j} x (a, n) => let t := (si i).1.2 j; (bind x (n t) a, λ u => if u = t then n u + 1 else n u)) ((ai i).2, λ _ : S => 0) (ai i).1 |>.1

inductive O₁ : List (List Unit × Unit) → Unit → Type
  | foo : O₁ [([], ()), ([], ())] ()
  | bar : O₁ [([(), ()], ())] ()

instance : ToString (O₁ si s) where
  toString
  | .foo => "foo"
  | .bar => "bar"

open FinTuple in
inductive O₂ : ∀ ⦃n⦄, (Fin n → List Unit × Unit) → Unit → Type
  | foo : O₂ ⟦([], ()), ([], ())⟧ ()
  | bar : O₂ ⟦([(), ()], ())⟧ ()

instance : ToString (O₂ si s) where
  toString
  | .foo => "foo"
  | .bar => "bar"

open FinTuple in
inductive O₃ : ∀ ⦃n⦄, (Fin n → ((m : Nat) × (Fin m → Unit)) × Unit) → Unit → Type
  | foo : O₃ ⟦(⟨_, ⟦⟧⟩, ()), (⟨_, ⟦⟧⟩, ())⟧ ()
  | bar : O₃ ⟦(⟨_, ⟦(), ()⟧⟩, ())⟧ ()

instance : ToString (O₃ si s) where
  toString
  | .foo => "foo"
  | .bar => "bar"

variable {S : Type} {O : ∀ ⦃n⦄, (Fin n → List S × S) → S → Type} in
instance [DecidableEq S] [∀ {n} si s, ToString (@O n si s)] : ToString (Abt₂ O s) where
  toString a := h (λ _ => 0) a
where
  h {s} (d : S → Nat) : Abt₂ O s → String
  | .var x => x.toString ++ "'"
  | .bvar s (x : Nat) => Var.toString (s := s) ⟨d s - 1 - x⟩
  | .op (si := si) o ai => toString o ++ h' λ i => h'' d (si i).1 ++ h (λ s' => d s' + bindCount s' (si i).1) (ai i)
  h' : ∀ {n}, (Fin n → String) → String
  | 0, _ => ""
  | _ + 1, ai => "(" ++ String.join (List.intersperse "; " (FinTuple.toList ai)) ++ ")"
  h'' (d : S → Nat) : List S → String
  | [] => ""
  | si => String.join (List.intersperse ", " (si.foldl (λ (bs, d) b => (Var.toString (s := b) ⟨d b⟩ :: bs, λ s => d s + if b = s then 1 else 0)) ([], d)).1.reverse) ++ ". "

variable {S : Type} {O : ∀ ⦃n⦄, (Fin n → ((m : Nat) × (Fin m → S)) × S) → S → Type} in
instance [DecidableEq S] [∀ {n} si s, ToString (@O n si s)] : ToString (Abt₃ O s) where
  toString a := h (λ _ => 0) a
where
  h {s} (d : S → Nat) : Abt₃ O s → String
  | .var x => x.toString ++ "'"
  | .bvar s (x : Nat) => Var.toString (s := s) ⟨d s - 1 - x⟩
  | .op (si := si) o ai => toString o ++ h' λ i => h'' d (si i).1 ++ h (λ s' => d s' + bindCount' s' (si i).1) (ai i)
  h' : ∀ {n}, (Fin n → String) → String
  | 0, _ => ""
  | _ + 1, ai => "(" ++ String.join (List.intersperse "; " (FinTuple.toList ai)) ++ ")"
  h'' (d : S → Nat) : (m : Nat) × (Fin m → S) → String
  | ⟨0, _⟩ => ""
  | ⟨_ + 1, si⟩ => String.join (List.intersperse ", " (FinTuple.foldl (λ (bs, d) b => (Var.toString (s := b) ⟨d b⟩ :: bs, λ s => d s + if b = s then 1 else 0)) ([], d) si).1.reverse) ++ ". "

open DList in
#reduce (.op' .bar ⟦(⟦23, 24⟧, .op .foo ⟦.var 23, .var 24⟧)⟧ : Abt₁ O₁ ())
open FinTuple DList in
#eval (.op' .bar ⟦(⟦"x", "y"⟧, .op .foo ⟦.var "x", .var "y"⟧)⟧ : Abt₂ O₂ ())
open FinTuple in
#eval (.op' .bar ⟦(⟦"x", "y"⟧, .op .foo ⟦.var "x", .var "y"⟧)⟧ : Abt₃ O₃ ())

/-
def Abt.free [DecidableEq S] (s' : S) (a : Abt S O s) : Var' s' :=
  let n := fv a
  let v := h a (mkArray n true)
  Id.run do
  for (i, b) in v.toList.enum do
    if b then
      return ⟨i⟩
  return ⟨n⟩
where
  fv {s}
  | .fvar (s := s'') _ => if s'' = s' then 1 else 0
  | .var _ _ => 0
  | .op _ ai => FinTuple.foldr Nat.add 0 λ i => fv (ai i)
  h {s}
  | .fvar (s := s'') x, v => if s'' = s' then v.setD x.x false else v
  | .var _ _, v => v
  | .op _ ai, v => FinTuple.foldr (λ (f : _ → _) a => f a) v λ i => h (ai i)

def Abt.unbind [DecidableEq S] {s' : S} (x : Var' s') (d : Nat) : Abt S O s → Abt S O s
  | .fvar y => .fvar y
  | .var s (y : Nat) =>
    if h : s = s'
    then
      match compare y d with
      | .gt => .var s (y - 1)
      | .eq => h ▸ .fvar x
      | .lt => .var s y
    else .var s y
  | .op (si := si) o ai => .op o λ i => (ai i).unbind x (d + liftAmt s' (si i).1)

def Abt.unop [DecidableEq S] (o : O si s) (ai : ∀ i, Abt S O (si i).2) i : (∀ j, Var' ((si i).1.2 j)) × Abt S O (si i).2 :=
  FinTuple.dfoldl
    (β := λ k => (S → Nat) × ((j : Fin k) → Var' ((si i).1.2 (j.cast (Nat.pred_le_pred k.isLt)))) × Abt S O (si i).2)
    (λ {j} (d, f, a) _ => let b := (si i).1.2 j; let x := a.free b; let d' s := if s = b then d s - 1 else d s; (d', Fin.revCases x f, a.unbind x (d' b)))
    ((liftAmt · (si i).1), λ k => nomatch k, ai i)
    (si i).1.2
    |>.2

instance (priority := low) [ToString α] : Repr α where
  reprPrec x _ := toString x

namespace ExampleAbt

inductive S
  | Exp
deriving DecidableEq

inductive O : ∀ ⦃n⦄, (Fin n → ((m : Nat) × (Fin m → S)) × S) → S → Type
  | num : Nat → O ⟦⟧ .Exp
  | plus : O ⟦(⟦⟧', .Exp), (⟦⟧', .Exp)⟧ .Exp
  | times : O ⟦(⟦⟧', .Exp), (⟦⟧', .Exp)⟧ .Exp
  | let : O ⟦(⟦⟧', .Exp), (⟦.Exp⟧', .Exp)⟧ .Exp

abbrev Abt := _root_.Abt S O

instance : ToString (O si s) where
  toString := h
where h
  | .num n => s!"num[{n}]"
  | .plus => "plus"
  | .times => "times"
  | .let => "let"

inductive Exp
  | var : Var' S.Exp → Exp
  | num : Nat → Exp
  | plus : Abt .Exp → Abt .Exp → Exp
  | times : Abt .Exp → Abt .Exp → Exp
  | let : Abt .Exp → Var' S.Exp → Abt .Exp → Exp
  deriving Repr

def Exp.in : Exp → Abt .Exp
  | .var x => .fvar x
  | .num n => .op (.num n) ⟦⟧ 
  | .plus a b => .op .plus ⟦a, b⟧
  | .times a b => .op .times ⟦a, b⟧
  | .let a x b => .op' .let ⟦(⟦⟧, a), (⟦x⟧, b)⟧

def Exp.out : Abt .Exp → Exp
  | .fvar x => .var x
  | .var _ x => .var ⟨x⟩
  | .op (.num n) _ => .num n 
  | .op .plus ai => .plus (ai 0) (ai 1)
  | .op .times ai => .times (ai 0) (ai 1)
  | .op .let ai => let ai' := Abt.unop .let ai; .let (ai' 0).2 ((ai' 1).1 .zero) (ai' 1).2

def Exp'.var := (Exp.in <| Exp.var ·)
def Exp'.num := (Exp.in <| Exp.num ·)
def Exp'.plus := (Exp.in <| Exp.plus · ·)
def Exp'.times := (Exp.in <| Exp.times · ·)
def Exp'.let := (Exp.in <| Exp.let · · ·)

theorem Exp.in_out : ∀ e, Exp.in (Exp.out e) = e
  | .fvar x => rfl
  | .var _ x => sorry
  | .op (.num n) _ => congrArg (Abt.op _) <| funext λ i => nomatch i
  | .op .plus ai => congrArg (Abt.op _) <| funext λ | 0 => rfl | 1 => rfl
  | .op .times ai => congrArg (Abt.op _) <| funext λ | 0 => rfl | 1 => rfl
  | .op .let ai => congrArg (Abt.op _) <| funext λ | 0 => rfl | 1 => sorry

end ExampleAbt

section
open ExampleAbt Exp'
#eval Exp'.let (plus (num 2) (num 3)) "z" (times (var "z") (num 5))
#eval match Exp'.let (plus (num 2) (num 3)) "z" (times (var "z") (num 5)) with | .op .let ai => Abt.unop O.let ai | _ => unreachable!
end

inductive O : ∀ ⦃n⦄, (Fin n → ((m : Nat) × (Fin m → Unit)) × Unit) → Unit → Type
  | zero : O ⟦(⟦⟧', ()), (⟦⟧', ())⟧ ()
  | one : O ⟦(⟦()⟧', ())⟧ ()
  | two : O ⟦(⟦(), ()⟧', ())⟧ ()

instance : ToString (O si s) where
  toString
    | .zero => "zero"
    | .one => "one"
    | .two => "two"

#eval Abt.op' O.one ⟦(⟦"x"⟧, .fvar "x")⟧
#eval Abt.op' O.one ⟦(⟦"x"⟧, .fvar "y")⟧
#eval Abt.op' O.two ⟦(⟦"x", "y"⟧, .fvar "x")⟧
#eval Abt.op' O.two ⟦(⟦"x", "y"⟧, .fvar "y")⟧
#eval Abt.op' O.two ⟦(⟦"x", "y"⟧, .fvar "z")⟧
#eval Abt.op' O.two ⟦(⟦"x", "y"⟧, .op' .zero ⟦(⟦⟧, .fvar "x"), (⟦⟧, .fvar "y")⟧)⟧

#eval match Abt.op' O.two ⟦(⟦"x", "y"⟧, .fvar "x")⟧ with | .op .two ai => Abt.unop O.two ai | _ => unreachable!
#eval match Abt.op' O.two ⟦(⟦"x", "y"⟧, .fvar "y")⟧ with | .op .two ai => Abt.unop O.two ai | _ => unreachable!
#eval match Abt.op' O.two ⟦(⟦"x", "y"⟧, .fvar "z")⟧ with | .op .two ai => Abt.unop O.two ai | _ => unreachable!
#eval match Abt.op' O.two ⟦(⟦"x", "y"⟧, .op' .zero ⟦(⟦⟧, .fvar "y"), (⟦⟧, .fvar "x")⟧)⟧ with | .op .two ai => Abt.unop O.two ai | _ => unreachable!

#eval Abt.op' O.one ⟦(⟦"x"⟧, .op' .one ⟦(⟦"y"⟧, .op .zero ⟦.fvar "x", .fvar "y"⟧)⟧)⟧
#eval match Abt.op' O.one ⟦(⟦"x"⟧, .op' .one ⟦(⟦"y"⟧, .op .zero ⟦.fvar "x", .fvar "y"⟧)⟧)⟧ with | .op .one ai => Abt.unop O.one ai | _ => unreachable!
#eval match Abt.op' O.one ⟦(⟦"x"⟧, .op' .one ⟦(⟦"y"⟧, .op .zero ⟦.fvar "x", .fvar "y"⟧)⟧)⟧ with | .op .one ai => (match Abt.unop O.one ai 0 |>.2 with | .op .one ai => Abt.unop O.one ai | _ => unreachable!) | _ => unreachable!

/-
variable (S : Type) (O : ∀ ⦃n⦄, (Fin n → (S → Nat) × S) → S → Type) in
inductive CAbt : (S → Nat) → S → Type
  | var s (x : Fin (X s)) : CAbt X s
  | op (o : O si s) (ai : ∀ i, CAbt (λ s => X s + (si i).1 s) (si i).2) : CAbt X s

def ClAbt S O := CAbt S O λ _ => 0
-/

/-
def Nat.le.rec' {n} {motive : (a : Nat) → n.le a → Sort u}
  (refl : motive n .refl)
  (step : ∀ {m} a, motive m a → motive m.succ a.step) {a} t
: motive a t := by
  cases h : a - n
    <;> have := Nat.sub_add_cancel t |>.symm |>.trans <| congrArg (· + n) h
    <;> simp [this, Nat.succ_add]
  . exact refl
  . exact step (Nat.le_add_left n _) (rec' refl step _)
  -/
-/
