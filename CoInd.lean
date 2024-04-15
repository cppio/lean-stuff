inductive List'
  | nil : List'
  | cons : Nat → List' → List'

instance : Nonempty List' := ⟨.nil⟩

def List'.rec' {α} (nil : α) (cons : Nat → α → α) : List' → α
  | .nil => nil
  | .cons h t => cons h (rec' nil cons t)

instance : Repr List' where
  reprPrec l _ :=
    repr (l.rec' [] .cons)

/-
coinductive Stream'
  | nil : Stream'
  | cons : Nat → Stream' → Stream'
-/

variable (τ : Sort u) in
inductive Stream'.View'
  | nil : View'
  | cons : Nat → τ → View'

def Stream'.View'.map (f : τ₁ → τ₂) : View' τ₁ → View' τ₂
  | nil => nil
  | cons h t => cons h (f t)

structure Stream' := gen ::
  {α : Type}
  (unfold : α → Stream'.View' α)
  (x : α)

def Stream'.View := Stream'.View' Stream'

def Stream'.out : Stream' → View
  | { α, unfold, x } => match unfold x with | .nil => .nil | .cons h x => .cons h { α, unfold, x }

def Stream'.in : View → Stream'
  | .nil => { α := Unit, unfold := λ () => .nil, x := () }
  | .cons h { α, unfold, x } => { α := Option α, unfold := λ | none => .cons h (some x) | some t => unfold t |>.map some, x := none }

def List'.toStream' : List' → Stream'
  | nil => .in .nil
  | cons h t => .in (.cons h t.toStream')

partial def Stream'.toList (s : Stream') : List' :=
  match s.out with
  | .nil => .nil
  | .cons h t => .cons h t.toList

def Stream'.toList' (s : Stream') : (_ : Nat := 9) → List' × Option Stream'
  | 0 => (.nil, some s)
  | n + 1 =>
    match s.out with
    | .nil => (.nil, none)
    | .cons h t =>
      let (l, s) := t.toList' n
      (.cons h l, s)

instance : Repr Stream' where
  reprPrec s p :=
    let (l, s?) := s.toList'
    match s? with
    | none => repr l
    | some _ =>
      @List.repr _ ⟨λ | none, _ => "..." | some n, _ => repr n⟩ (l.rec' [none] (some · :: ·)) p

#eval Stream'.gen (λ n => .cons n (n * 2)) 1
