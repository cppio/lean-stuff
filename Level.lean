import Lean

def foo.{u} : Sort (max 1 (imax 1 u + 1)) := Unit → Sort (imax 1 u)

universe u
#reduce Type (max 0 (imax 1 u))
#reduce Type (max 0 (max 1 u))

deriving instance DecidableEq for Lean.LevelMVarId
deriving instance DecidableEq for Lean.Level

@[simp]
def Lean.Level.hasMVar' : Level → Bool
  | mvar _ => true
  | succ u => u.hasMVar'
  | max u v => u.hasMVar' || v.hasMVar'
  | imax u v => u.hasMVar' || v.hasMVar'
  | _ => false

@[simp]
def Lean.Level.hasParam' : Level → Bool
  | param _ => true
  | succ u => u.hasParam'
  | max u v => u.hasParam' || v.hasParam'
  | imax u v => u.hasParam' || v.hasParam'
  | _ => false

@[simp]
def Lean.Level.instantiateParams' (s : Name → Level) : Level → Level
  | succ u   => succ (u.instantiateParams' s)
  | max u v  => max (u.instantiateParams' s) (v.instantiateParams' s)
  | imax u v => imax (u.instantiateParams' s) (v.instantiateParams' s)
  | param n  => s n
  | u        => u

theorem Lean.Level.hasParam_instantiateParams' (u : Level) (h : ∀ n, (s n).hasParam' = false) : (u.instantiateParams' s).hasParam' = false := by
  induction u <;> simp [*]

@[simp]
def Lean.Level.getOffset' : Level → Nat
  | succ u => u.getOffset'.succ
  | _ => .zero

@[simp]
def Lean.Level.addOffset' (u : Level) : Nat → Level
  | .zero => u
  | .succ n => succ (u.addOffset' n)

def Lean.Level.mkMax (u v : Level) : Level :=
  let uo := u.getOffset'
  let vo := v.getOffset'
  let ul := u.getLevelOffset
  let vl := v.getLevelOffset
  if ul = vl
  then if uo ≥ vo then u else v
  else
    let o := uo.min vo
    (max (ul.addOffset' (uo - o)) (vl.addOffset' (vo - o))).addOffset' o

def Lean.Level.normalize' : Level → Level
  | succ u => succ u.normalize'
  | max u v => mkMax u.normalize' v.normalize'
  | imax u v =>
    let u := u.normalize'
    let v := v.normalize'
    let vo := v.getOffset'
    if vo > 0
    then mkMax u v
    else
      let uo := u.getOffset'
      let ul := u.getLevelOffset
      let vl := v.getLevelOffset
      imax (ul.addOffset' uo) (vl.addOffset' vo)
  | u => u

def u : Lean.Level := .param `u
#eval Lean.Level.normalize' <| .max .zero u

@[simp]
def Lean.Level.toNat' : Level → Option Nat
  | zero => some .zero
  | succ u => match u.toNat' with
    | none => none
    | some u => some (.succ u)
  | max u v => match u.toNat' with
    | none => none
    | some u => match v.toNat' with
      | none => none
      | some v => some (.max u v)
  | imax u v => match u.toNat' with
    | none => none
    | some u => match v.toNat' with
      | none => none
      | some v => some (.imax u v)
  | _ => none

@[simp]
theorem or_eq_false_iff : ∀ {a b}, (a || b) = false ↔ a = false ∧ b = false
  | false, false => ⟨λ _ => ⟨rfl, rfl⟩, λ _ => rfl⟩
  | false, true => ⟨λ h => nomatch h, λ h => nomatch h⟩
  | true, _ => ⟨λ h => nomatch h, λ h => nomatch h⟩

example (u v : Lean.Level) (hu : u.hasMVar' = false) (hv : v.hasMVar' = false) (h : u.normalize' ≠ v.normalize') : ∃ s, (∀ n, (s n).hasParam' = false) ∧ (u.instantiateParams' s).toNat' ≠ (v.instantiateParams' s).toNat' := by
  induction u
  case mvar => cases hu
  case zero =>
    clear hu
    induction v
    case mvar => cases hv
    case zero => cases h rfl
    case param =>
      apply Exists.intro λ _ => .succ .zero
      simp
    case succ v ih =>
      simp at hv
      simp [hv, Lean.Level.getLevelOffset, Lean.Level.getOffset, Lean.Level.getOffsetAux]
      apply Exists.intro λ _ => .zero
      split <;> simp
    case max u v ihu ihv =>
      simp at hv
      specialize ihu hv.left
      specialize ihv hv.right
      clear hv
      simp at ihu ihv ⊢
      by_cases .zero = u.normalize'
      case inr hu =>
        specialize ihu hu
        clear hu ihv h
        cases ihu with | _ s ih =>
        apply Exists.intro s
        simp [ih]
        split <;> simp
        split <;> simp [Nat.max]
        rename_i u' hu _ v' hv
        simp [hu] at ih
        split
        case _ h =>
          intro h'
          cases h'
          cases h
          exact ih.right rfl
        case _ =>
          exact ih.right
      case inl hu =>
        clear ihu
        by_cases .zero = v.normalize'
        case inl hv => simp [Lean.Level.normalize', ← hu, ← hv] at h
        case inr hv =>
          specialize ihv hv
          clear hu hv h
          cases ihv with | _ s ih =>
          apply Exists.intro s
          simp [ih]
          split <;> simp
          split <;> simp [Nat.max]
          rename_i u' hu _ v' hv
          simp [hv] at ih
          split
          case _ =>
            exact ih.right
          case _ h =>
            intro h'
            cases h'
            apply h
            apply Nat.zero_le
    case imax =>
      sorry
  case succ =>
    sorry
  case max =>
    sorry
  case imax =>
    sorry
  case param =>
    sorry
