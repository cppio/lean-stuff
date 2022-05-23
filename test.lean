import logic.equiv.basic

variables {α β γ : Sort*}

example : equiv (pprod α β → γ) (α → β → γ) :=
⟨λ f x y, f ⟨x, y⟩,
 λ g xy, g xy.fst xy.snd,
 λ f, funext $ λ ⟨x, y⟩, rfl,
 λ g, rfl⟩

-- c^(a b) = (c^b)^a

@[simp]
theorem pprod.mk_fst_snd : ∀ xy : pprod α β, pprod.mk xy.fst xy.snd = xy :=
@pprod.rec α β (λ xy, pprod.mk xy.fst xy.snd = xy) (λ fst snd, rfl)

example : equiv (psum α β → γ) (pprod (α → γ) (β → γ)) :=
⟨λ f, ⟨λ x, f (psum.inl x), λ y, f (psum.inr y)⟩,
 λ g, @psum.rec α β (λ _, γ) g.fst g.snd,
 λ f, funext $ @psum.rec α β (λ xy, @psum.rec α β (λ _, γ) (λ x, f (psum.inl x)) (λ y, f (psum.inr y)) xy = f xy) (λ x, rfl) (λ y, rfl),
 λ ⟨g₁, g₂⟩, rfl⟩

-- c^(a+b) = c^a c^b

example : equiv (α → pprod β γ) (pprod (α → β) (α → γ)) :=
⟨λ f, ⟨λ x, (f x).fst, λ x, (f x).snd⟩,
 λ g x, ⟨g.fst x, g.snd x⟩,
 λ f, funext $ λ x, pprod.mk_fst_snd (f x),
 λ ⟨g₁, g₂⟩, rfl⟩

-- (b c)^a = b^a c^a

--variable f : psum α β → γ

--def f' : (∀ {φ}, (α → φ) → (β → φ) → φ) → γ := λ h, f (h or.inl or.inr)

example : equiv (psum α β → γ) ((∀ {φ}, (α → φ) → (β → φ) → φ) → γ) :=
⟨λ f h, f $ h psum.inl psum.inr,
 λ g, @psum.rec α β (λ _, γ) (λ x, g $ λ φ h₁ h₂, h₁ x) (λ y, g $ λ φ h₁ h₂, h₂ y),
 λ f, funext $ @psum.rec α β (λ xy, @psum.rec α β (λ _, γ) (λ x, f (psum.inl x)) (λ y, f (psum.inr y)) xy = f xy) (λ x, rfl) (λ y, rfl),
 λ g, funext $ λ h, by { dsimp, }⟩

example : equiv (α → pprod β γ) (α → ∀ {φ}, (β → γ → φ) → φ) :=
⟨λ f x φ h, h (f x).fst (f x).snd,
 λ g x, ⟨@g x β (λ y z, y), @g x γ (λ y z, z)⟩,
 sorry,
 sorry⟩
