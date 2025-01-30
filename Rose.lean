inductive Rose (α : Type u)
  | mk (x : α) (xs : List (Rose α))

noncomputable def Rose.rec'.{u_1, u_2, u}
  {α : Type u}
  {motive_1 : Rose α → Sort u_1}
  {motive_2 : List (Rose α) → Sort u_2}
  (mk : ∀ x xs, motive_2 xs → motive_1 (mk x xs))
  (nil : motive_2 [])
  (cons : ∀ head tail, motive_1 head → motive_2 tail → motive_2 (head :: tail))
  t
: motive_1 t :=
  @Rose.rec
    α
    (fun t => ULift.{max u_1 u_2} <| PLift <| motive_1 t)
    (fun t => ULift.{max u_1 u_2} <| PLift <| motive_2 t)
    (fun x xs xs_ih => ULift.up <| .up <| mk x xs xs_ih.down.down)
    (ULift.up <| .up nil)
    (fun head tail head_ih tail_ih => ULift.up <| .up <| cons head tail head_ih.down.down tail_ih.down.down)
    t
  |>.down.down

inductive List.Dep {α : Type u} (motive : α → Sort v) : List α → Sort (max (u + 1) v)
  | nil : Dep motive []
  | cons head tail : motive head → Dep motive tail → Dep motive (head :: tail)

noncomputable def Rose.recAux {α : Type u} {motive : Rose α → Sort v} (mk : ∀ x xs, xs.Dep motive → motive (mk x xs)) : ∀ xs, motive xs :=
  @Rose.rec' α motive (List.Dep motive) mk .nil .cons

def Rose.id : Rose α → Rose α
  | mk x xs => mk x <| map xs
  where map
    | []      => []
    | x :: xs => id x :: map xs

def Rose.id_eq : (t : Rose α) → id t = t
  | mk x xs => id.eq_1 x xs ▸ congrArg (mk x) (dfoldr xs)
  where dfoldr : (xs : List (Rose α)) → id.map xs = xs
    | []      => rfl
    | x :: xs => id.map.eq_2 x xs ▸ congr (congrArg List.cons (id_eq x)) (dfoldr xs)
