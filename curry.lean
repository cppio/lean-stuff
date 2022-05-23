class uncurry_ty (α : Sort*) :=
(ty : (α → Sort*) → Sort*)
(uncurry : ∀ {β : α → Sort*}, (∀ x, β x) → ty β)

namespace uncurry_ty

instance default {α} : uncurry_ty α :=
⟨λ β, ∀ x, β x, λ β, id⟩

instance prod {α α'} [uncurry_ty α'] : uncurry_ty (α × α') :=
⟨λ β, ∀ x, ty (λ x', β ⟨x, x'⟩), λ β f x, uncurry (λ x', f ⟨x, x'⟩)⟩

instance sigma {α} {α' : α → Sort*} [∀ x, uncurry_ty (α' x)] : uncurry_ty (sigma α') :=
⟨λ β, ∀ x, ty (λ x', β ⟨x, x'⟩), λ β f x, uncurry (λ x', f ⟨x, x'⟩)⟩

end uncurry_ty

open uncurry_ty (uncurry)

def sum₃ : ℕ × ℕ × ℕ → ℕ :=
λ ⟨x, y, z⟩, x + y + z

def head : (Σ n, fin (n + 1) → ℕ) → ℕ :=
λ ⟨n, f⟩, f 0

def typeof {α} (_ : α) := α

#reduce typeof $ uncurry sum₃
#reduce typeof $ uncurry head

#eval (λ _, uncurry sum₃) () 1 2 3
#eval (λ _, uncurry head) () 1 (λ _, 42)

def sum₃' : ℕ → ℕ → ℕ → ℕ := uncurry sum₃

class uncurry_ty' (α : Sort*) :=
(ty : ∀ (β : α → Sort*) [∀ x, uncurry_ty (β x)], Sort*) (uncurry : ∀ {β : α → Sort*} [∀ x, uncurry_ty (β x)], (∀ x, β x) → ty β)

namespace uncurry_ty'

instance default {α} : uncurry_ty' α :=
⟨λ β I, sorry, sorry⟩

end uncurry_ty'

def sum₃' : ℕ → ℕ × ℕ → ℕ :=
λ x ⟨y, z⟩, x + y + z

def head' : ∀ (α : Type*), (Σ n, fin (n + 1) → α) → α :=
λ α ⟨n, f⟩, f 0

#reduce typeof $ uncurry sum₃'
#reduce typeof $ uncurry head'
