import data.list.alist

infixr ` <&> `:100 := flip functor.map

/-
def var := list ℕ
instance : has_coe string var := ⟨list.map char.to_nat ∘ string.to_list⟩
instance : has_repr var := ⟨repr ∘ list.as_string ∘ list.map char.of_nat⟩
-/

def var := string

class imperative m extends monad m :=
(load : var → m ℕ)
(store : var → ℕ → m unit)
(loop : m bool → ℕ → m unit)

prefix `⋆`:100 := imperative.load
infix ` ≔ `:1 := imperative.store

def imperative.while {m} [imperative m] (f : ℕ) (cond : m bool) (body : m unit) : m unit :=
imperative.loop (do b ← cond, if b then do body, return ff else return tt) (f + 1)

@[reducible]
def ctx := alist (λ _ : var, ℕ)
@[reducible]
def imp := state_t ctx option

def imp.load : var → imp ℕ := λ v, state_t.get >>= state_t.lift ∘ alist.lookup v
def imp.store : var → ℕ → imp unit := λ v, state_t.modify ∘ alist.insert v
def imp.loop (c : imp bool) : ℕ → imp unit
| 0 := ⟨λ _, none⟩
| (f + 1) := do
  b ← c,
  if b
  then return ()
  else imp.loop f

instance : imperative imp := ⟨imp.load, imp.store, imp.loop⟩

def imp.sim {α} : imp α → option α :=
option.map prod.fst ∘ flip state_t.run ∅

open imperative (while) imp (sim)

#eval sim $ do
  "x" ≔ 4,
  "y" ≔ 0,
  x ← ⋆"x",
  while x (⋆"x" <&> (>0)) (do
    x ← ⋆"x",
    y ← ⋆"y",
    "y" ≔ x + y,
    "x" ≔ x - 1
  ),
  ⋆"y"

/-
def ctx := ℕ × alist (λ _ : var, ℕ)
@[reducible]
def imp := state_t ctx option

instance : imperative imp := ⟨λ v, state_t.get >>= λ s, state_t.lift (s.snd.lookup v), λ v x, state_t.modify $ λ s, (s.fst, s.snd.insert v x)⟩

def sim {α} (f) (m : imp α) : option α :=
(m.run (f, ∅)).map prod.fst

def while' (cond : imp bool) (body : imp unit) : ℕ → alist (λ _ : var, ℕ) → option (unit × ctx)
| 0 _ := none
| (f + 1) Γ := do
  (c, s) ← cond.run (f + 1, Γ),
  if c
  then do
    ((), (_, Γ)) ← body.run s,
    while' f Γ
  else some ((), s)

def while (cond : imp bool) (body : imp unit) : imp unit :=
⟨λ s, while' cond body s.fst s.snd⟩

/-
int x = 10;
int y = 0;
while (x > 0) {
    y = x + y;
    x = x - 1;
}
return y;
-/

#eval sim 5 $ do
  "x" ≔ 4,
  "y" ≔ 0,
  while (do
    x ← ⋆"x",
    return $ x > 0
  ) (do
    x ← ⋆"x",
    y ← ⋆"y",
    "y" ≔ x + y,
    "x" ≔ x - 1
  ),
  ⋆"y"
-/
