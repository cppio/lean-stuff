class uncurry_ty (α : Sort*) (ty : out_param (Sort* → Sort*)) :=
(uncurry : ∀ {β}, (α → β) → ty β)

namespace uncurry_ty

instance default {α} : uncurry_ty α ((→) α) :=
⟨λ β, id⟩

instance prod {α α' ty} [uncurry_ty α' ty] : uncurry_ty (α × α') (λ β, α → ty β) :=
⟨λ β f x, uncurry (f ∘ prod.mk x)⟩

instance sigma {α} {α' : α → Sort*} {ty : α → Sort* → Sort*} [∀ x, uncurry_ty (α' x) (ty x)] :
  uncurry_ty (sigma α') (λ β, ∀ x, ty x β) :=
⟨λ β f x, uncurry (f ∘ sigma.mk x)⟩

end uncurry_ty

open uncurry_ty (uncurry)

def sum₃ : ℕ × ℕ × ℕ → ℕ :=
λ ⟨x, y, z⟩, x + y + z

def head : (Σ n, fin (n + 1) → ℕ) → ℕ :=
λ ⟨n, f⟩, f 0

def typeof {α} (_ : α) := α

#reduce typeof $ uncurry sum₃
#reduce typeof $ uncurry head

#eval uncurry sum₃ 1 2 3
#eval uncurry head 1 (λ _, 42)

#eval (λ _, uncurry sum₃) () 1 2 3
#eval (λ _, uncurry head) () 1 (λ _, 42)

def sum₃' : ℕ → ℕ × ℕ → ℕ :=
λ x ⟨y, z⟩, x + y + z

def head' {α : Type*} : (Σ n, fin (n + 1) → α) → α :=
λ ⟨n, f⟩, f 0

#reduce typeof $ uncurry sum₃'
#reduce typeof $ uncurry head'

class uncurry_ty' (α : Sort*) :=
(ty : Sort* → Sort*) (uncurry

namespace uncurry_ty

instance fn {α α'} [uncurry_ty α'] : uncurry_ty (α → α') :=
⟨λ β, ∀ x, ty (α' x) β, λ β f x, uncurry (λ A, sorry)⟩

end uncurry_ty

#reduce typeof $ uncurry (sum₃' 0)
#reduce typeof $ uncurry head'

#reduce typeof $ uncurry sum₃
#reduce typeof $ uncurry head
