@[simp]
theorem List.map_append : map f (l ++ l') = map f l ++ map f l' := by
  induction l with
  | nil => rfl
  | cons => dsimp!; congr

namespace Param

class Functor (f : Sort u → Sort v) where
  map : (α → β) → f α → f β
  map_id (x : f α) : map id x = x
  map_comp (g : β → γ) (h : α → β) (x : f α) : map (g ∘ h) x = map g (map h x)

class ContraFunctor (f : Sort u → Sort v) where
  map : (α → β) → f β → f α
  map_id (x : f α) : map id x = x
  map_comp (g : β → γ) (h : α → β) (x : f γ) : map (g ∘ h) x = map h (map g x)

instance : Functor List where
  map := List.map
  map_id x := by
    induction x with
    | nil => rfl
    | cons => dsimp!; congr
  map_comp _ _ x := by
    induction x with
    | nil => rfl
    | cons => dsimp!; congr

def Set (α : Sort u) := α → Prop

instance : Functor Set where
  map f s y := ∃ x, s x ∧ f x = y
  map_id _ := funext λ _ => propext ⟨λ ⟨_, p, rfl⟩ => p, λ p => ⟨_, p, rfl⟩⟩
  map_comp _ _ _ := funext λ _ => propext ⟨λ ⟨x, p, h⟩ => ⟨_, ⟨x, p, rfl⟩, h⟩, λ ⟨_, ⟨x, p, rfl⟩, h⟩ => ⟨x, p, h⟩⟩

instance : ContraFunctor Set where
  map f s x := s (f x)
  map_id _ := rfl
  map_comp _ _ _ := rfl

inductive List.lift (r : α → β → Prop) : List α → List β → Prop
  | nil : lift r [] []
  | cons : r x x' → lift r l l' → lift r (x :: l) (x' :: l')

theorem List.lift_fun_eq_map : lift (g · = ·) l l' ↔ List.map g l = l' := by
  induction l generalizing l' with
  | nil => cases l'; exact ⟨λ _ => rfl, λ _ => .nil⟩; exact ⟨λ h => nomatch h, λ h => nomatch h⟩
  | cons _ _ ih => cases l'; exact ⟨λ h => nomatch h, λ h => nomatch h⟩; exact ⟨λ | .cons rfl h => congrArg (List.cons _) <| ih.mp h, λ h => have ⟨h₁, h₂⟩ := List.cons.inj h; .cons h₁ <| ih.mpr h₂⟩

def ft₁ (f : ∀ {α}, List α → List α) := ∀ {α β} (r : α → β → Prop) {l l'} (h : List.lift r l l'), List.lift r (f l) (f l')
def ft₁' (f : ∀ {α}, List α → List α) := ∀ {α β} (g : α → β) (l : List α), (f l).map g = f (l.map g)

example : ft₁ f → ft₁' f
  | h, _, _, _, _ => List.lift_fun_eq_map.mp <| h _ <| List.lift_fun_eq_map.mpr rfl

/-
 forall (x, y) in lift{[]}(R). (f x, f y) in lift{[]}(R)

lift{[]}(R)
  = {([], [])}
  u {(x : xs, y : ys) | ((x, y) in R) && ((xs, ys) in lift{[]}(R))}
-/

example : List.reverse (Functor.map f x) = Functor.map f (List.reverse x) := by
  dsimp [Functor.map]
  induction x with
  | nil => rfl
  | cons => simp! [*]

def Set.comp (s : Set α) : Set α
  | x => !s x

example : Set.comp (ContraFunctor.map f s) = ContraFunctor.map f (Set.comp s) := rfl

def List.toSet [BEq α] (l : List α) : Set α
  | x => l.contains x
