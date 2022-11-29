import Sorting.List

variable (le : α → α → Bool)

def insert (x : α) : List α → List α
  | [] => [x]
  | y :: l =>
    if le x y
    then x :: y :: l
    else y :: insert x l

def insertionSort : List α → List α
  | [] => []
  | x :: l => insert le x (insertionSort l)

theorem perm_insert x : ∀ l, List.Perm (insert le x l) (x :: l)
  | [] => .cons x .nil
  | y :: l => show List.Perm (ite ..) _ from
    if h : le x y
    then if_pos h ▸ .cons x (.cons y (.refl l))
    else if_neg h ▸ .trans (.cons y (perm_insert x l)) (.swap x y (.refl l))

theorem perm_insertionSort : ∀ l, List.Perm (insertionSort le l) l
  | [] => .nil
  | x :: l => .trans (perm_insert le x (insertionSort le l)) (.cons x (perm_insertionSort l))

def insertPerm (x : α) : (l : List α) → { r // List.Perm r (x :: l) }
  | [] => ⟨[x], .cons x .nil⟩
  | y :: l =>
    if le x y
    then ⟨x :: y :: l, .cons x (.cons y (.refl l))⟩
    else
      let ⟨r, h⟩ := insertPerm x l
      ⟨y :: r, .trans (.cons y h) (.swap x y (.refl l))⟩

def insertionSortPerm : (l : List α) → { r // List.Perm r l }
  | [] => ⟨[], .nil⟩
  | x :: l =>
    let ⟨r, h⟩ := insertionSortPerm l
    let ⟨r', h'⟩ := insertPerm le x r
    ⟨r', .trans h' (.cons x h)⟩

theorem chain_insert (hle : ∀ {x y}, ¬le x y → le y x) x : ∀ {l}, List.Chain (le · ·) l → List.Chain (le · ·) (insert le x l)
  | [], _ => .singleton x
  | y :: l, h => show List.Chain _ (ite ..) from
    if h' : le x y
    then if_pos h' ▸ .cons h' h
    else if_neg h' ▸ match l with
                     | [] => .cons (hle h') (.singleton x)
                     | z :: l => show List.Chain _ (_ :: ite ..) from
                       if h'' : le x z
                       then if_pos h'' ▸ .cons (hle h') (.cons h'' h.snd)
                       else if_neg h'' ▸ .cons h.fst (have := if_neg h'' ▸ show List.Chain _ (ite ..) from chain_insert hle x h.snd; by exact this)

variable [Monad m] {α} (le : α → α → m Bool)

def insertM (x : α) : List α → m (List α)
  | [] => return [x]
  | y :: l => do
    if ← le x y
    then return x :: y :: l
    else return y :: (← insertM x l)

def insertionSortM : List α → m (List α)
  | [] => return []
  | x :: l => do
    let r ← insertionSortM l
    insertM le x r

def insertPermM (x : α) : (l : List α) → m { r // List.Perm r (x :: l) }
  | [] => return ⟨[x], by simp /- .cons x .nil -/⟩
  | y :: l => do
    if ← le x y
    then return ⟨x :: y :: l, .cons x (.cons y (.refl l))⟩
    else
      let r ← insertPermM x l
      return ⟨y :: r.1, .trans (.cons y r.2) (.swap x y (.refl l))⟩

def insertionSortPermM : (l : List α) → m { r // List.Perm r l }
  | [] => return ⟨[], .nil⟩
  | x :: l => do
    let r ← insertionSortPermM l
    let r' ← insertPermM le x r.1
    return ⟨r'.1, .trans r'.2 (.cons x r.2)⟩
