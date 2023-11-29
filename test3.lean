/-
map : (α → β) → ϕ(α) → ϕ(β)

fold : ϕ(μ(ϕ)) → μ(ϕ)
rec : (ϕ(α) → α) → μ(ϕ) → α

rec f (fold x) = f (map (rec f) x)

gen : (α → ϕ(α)) → α → ν(ϕ)
unfold : ν(ϕ) → ϕ(ν(ϕ))

unfold (gen f x) = map (gen f) (f x)


unfold = rec (map fold)
fold = gen (map unfold)

id = rec fold
id = gen unfold


list(t) = 1 + τ × t

map : (α → β) → list(α) → list(β)

map f (1·⟨⟩) = 1·⟨⟩
map f (2·⟨h, t⟩) = 2⬝⟨h, f t⟩

fold : list(μ(list)) → μ(list)
rec : (list(α) → α) → μ(list) → α

rec f (fold (1·⟨⟩)) = f (1·⟨⟩)
rec f (fold (2·⟨h, t⟩)) = f (2·⟨h, rec f t⟩)


ϕ(t) = (t → τ) → σ

map : (α → β) → ϕ(α) → ϕ(β)

map f g h = g (h ∘ f)

fold : ϕ(μ(ϕ)) → μ(ϕ)
rec : (ϕ(α) → α) → μ(ϕ) → α

rec f (fold x) = f (map (rec f) x)


type tau = int
type sigma = int
type 'a phi = ('a -> tau) -> sigma
fun map f (g : 'a phi) : 'b phi = fn h => g (h o f)
datatype mu = fold of mu phi
fun rec' f (fold x) = f (map (rec' f) x)
-/

def map (f : α → β) : (Unit ⊕ α) → (Unit ⊕ β)
  | .inl () => .inl ()
  | .inr x => .inr (f x)

def fold : (Unit ⊕ Nat) → Nat
  | .inl () => .zero
  | .inr n => .succ n

def rec (f : Unit ⊕ α → α) : Nat → α
  | .zero => f (.inl ())
  | .succ n => f (.inr (rec f n))

def unfold : Nat → Unit ⊕ Nat :=
  rec (map fold)

def pred : Nat → Nat :=
  λ n =>
    match unfold n with
    | .inl () => .zero
    | .inr n => n

def rec' {motive : Sort _} (zero : motive) (succ : motive → motive) : Nat → motive
  | .zero => zero
  | .succ n => succ (rec' zero succ n)

def pred' : Nat → Nat :=
  λ n =>
    match rec' (Sum.inl ()) (λ | .inl () => .inr Nat.zero | .inr n => .inr n.succ) n with
    | .inl () => .zero
    | .inr n => n

def pred'' : Nat → Nat :=
  λ n =>
    Prod.fst <| rec' (.zero, .zero) (λ (_, x) => (x, x.succ)) n

inductive Foo
  | mk : (Nat → Foo) → Foo

#check λ {α} (f : (_ → _) → _) => @Foo.rec (λ _ => α) λ _ => f
--rec : (ϕ(α) → α) → μ(ϕ) → α
-- ((Nat → α) → α) → Foo → α
