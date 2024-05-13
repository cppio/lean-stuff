import Lean

mutual

inductive Even
  | zero
  | succ (o : Odd)

inductive Odd
  | succ (e : Even)

end

run_elab
  let Even_toNat := `Even.toNat
  let Odd_toNat  := `Odd.toNat

  let Even_toNat_body := .const ``Nat []
  let Odd_toNat_body  := .const ``Nat []

  let Even_toNat_zero := .const ``Nat.zero []

  let Even_toNat_succ_body := .app (.const ``Nat.succ []) (.app (.const Odd_toNat  []) (.bvar 0))
  let Odd_toNat_succ_body  := .app (.const ``Nat.succ []) (.app (.const Even_toNat []) (.bvar 0))

  let Even_toNat_succ_rec := .lam `o (.const ``Odd  []) (.const ``Nat.succ []) .default
  let Odd_toNat_succ_rec  := .lam `e (.const ``Even  []) (.const ``Nat.succ []) .default

  let Even_toNat_type (mk := Lean.Expr.lam) := mk `e (.const ``Even []) Even_toNat_body .default
  let Odd_toNat_type  (mk := Lean.Expr.lam) := mk `o (.const ``Odd  []) Odd_toNat_body  .default

  let Even_toNat_succ := .lam `o (.const ``Odd  []) Even_toNat_succ_body .default
  let Odd_toNat_succ  := .lam `e (.const ``Even []) Odd_toNat_succ_body  .default

  Lean.addDecl <| .defnDecl {
    name := Even_toNat
    levelParams := []
    type := Even_toNat_type .forallE
    value := .app (.app (.app (.app (.app (.const ``Even.rec [.succ .zero]) Even_toNat_type) Odd_toNat_type) Even_toNat_zero) Even_toNat_succ_rec) Odd_toNat_succ_rec
    hints := .opaque
    safety := .safe
  }

  Lean.addDecl <| .defnDecl {
    name := Odd_toNat
    levelParams := []
    type := Odd_toNat_type .forallE
    value := .app (.app (.app (.app (.app (.const ``Odd.rec [.succ .zero]) Even_toNat_type) Odd_toNat_type) Even_toNat_zero) Even_toNat_succ_rec) Odd_toNat_succ_rec
    hints := .opaque
    safety := .safe
  }

  Lean.addDecl <| .defnDecl {
    name := Lean.Compiler.mkUnsafeRecName Even_toNat
    levelParams := []
    type := Even_toNat_type .forallE
    value := .lam `e (.const ``Even []) (.app (.app (.app (.app (.const ``Even.casesOn [.succ .zero]) Even_toNat_type) (.bvar 0)) Even_toNat_zero) Even_toNat_succ) .default
    hints := .opaque
    safety := .safe
  }

  Lean.addDecl <| .defnDecl {
    name := Lean.Compiler.mkUnsafeRecName Odd_toNat
    levelParams := []
    type := Odd_toNat_type .forallE
    value := .lam `o (.const ``Odd []) (.app (.app (.app (.const ``Odd.casesOn [.succ .zero]) Odd_toNat_type) (.bvar 0)) Odd_toNat_succ) .default
    hints := .opaque
    safety := .safe
  }

  Lean.compileDecls [Lean.Compiler.mkUnsafeRecName Even_toNat, Lean.Compiler.mkUnsafeRecName Odd_toNat]

  Lean.addDecl <| .thmDecl {
    name := Even_toNat.str "eq_1"
    levelParams := []
    type := .app (.app (.app (.const ``Eq [.succ .zero]) Even_toNat_body) (.app (.const Even_toNat []) (.const ``Even.zero []))) Even_toNat_zero
    value := .app (.app (.const ``Eq.refl [.succ .zero]) Even_toNat_body) Even_toNat_zero
  }

  Lean.addDecl <| .thmDecl {
    name := Even_toNat.str "eq_2"
    levelParams := []
    type := .forallE `o (.const ``Odd []) (.app (.app (.app (.const ``Eq [.succ .zero]) Even_toNat_body) (.app (.const Even_toNat []) (.app (.const ``Even.succ []) (.bvar 0)))) Even_toNat_succ_body) .default
    value := .lam `o (.const ``Odd []) (.app (.app (.const ``Eq.refl [.succ .zero]) Even_toNat_body) Even_toNat_succ_body) .default
  }

  Lean.addDecl <| .thmDecl {
    name := Odd_toNat.str "eq_1"
    levelParams := []
    type := .forallE `e (.const ``Even []) (.app (.app (.app (.const ``Eq [.succ .zero]) Odd_toNat_body) (.app (.const Odd_toNat []) (.app (.const `Odd.succ []) (.bvar 0)))) Odd_toNat_succ_body) .default
    value := .lam `e (.const ``Even []) (.app (.app (.const ``Eq.refl [.succ .zero]) Odd_toNat_body) Odd_toNat_succ_body) .default
  }

  Lean.addDecl <| .defnDecl {
    name := Even_toNat.str "match_1"
    levelParams := [`u]
    type := .forallE `motive (.forallE `e (.const ``Even []) (.sort (.param `u)) .default) (.forallE `e (.const ``Even []) (.forallE `zero (.app (.bvar 1) (.const ``Even.zero [])) (.forallE `succ (.forallE `o (.const ``Odd []) (.app (.bvar 3) (.app (.const ``Even.succ []) (.bvar 0))) .default) (.app (.bvar 3) (.bvar 2)) .default) .default) .default) .implicit
    value := .const ``Even.casesOn [.param `u]
    hints := .abbrev
    safety := .safe
  }

  Lean.addDecl <| .defnDecl {
    name := Odd_toNat.str "match_1"
    levelParams := [`u]
    type := .forallE `motive (.forallE `o (.const ``Odd []) (.sort (.param `u)) .default) (.forallE `o (.const ``Odd []) (.forallE `succ (.forallE `e (.const ``Even []) (.app (.bvar 2) (.app (.const ``Odd.succ []) (.bvar 0))) .default) (.app (.bvar 2) (.bvar 1)) .default) .default) .implicit
    value := .const ``Odd.casesOn [.param `u]
    hints := .abbrev
    safety := .safe
  }

  Lean.Meta.Match.addMatcherInfo (Even_toNat.str "match_1") {
    numParams := 0
    numDiscrs := 1
    altNumParams := #[0, 1]
    uElimPos? := some 0
    discrInfos := #[{}]
  }

  Lean.Meta.Match.addMatcherInfo (Odd_toNat.str "match_1") {
    numParams := 0
    numDiscrs := 1
    altNumParams := #[1]
    uElimPos? := some 0
    discrInfos := #[{}]
  }

  Lean.addDecl <| .thmDecl {
    name := Even_toNat.str Lean.Meta.unfoldThmSuffix
    levelParams := []
    type := .forallE `e (.const ``Even []) (.app (.app (.app (.const ``Eq [.succ .zero]) Even_toNat_body) (.app (.const Even_toNat []) (.bvar 0))) (.app (.app (.app (.app (.const (Even_toNat.str "match_1") [.succ .zero]) Even_toNat_type) (.bvar 0)) Even_toNat_zero) Even_toNat_succ)) .default
    value := .lam `e (.const ``Even []) (.app (.app (.app (.app (.const ``Even.casesOn [.zero]) (.lam `e (.const ``Even []) (.app (.app (.app (.const ``Eq [.succ .zero]) Even_toNat_body) (.app (.const Even_toNat []) (.bvar 0))) (.app (.app (.app (.app (.const (Even_toNat.str "match_1") [.succ .zero]) Even_toNat_type) (.bvar 0)) Even_toNat_zero) Even_toNat_succ)) .default)) (.bvar 0)) (.const (Even_toNat.str "eq_1") [])) (.const (Even_toNat.str "eq_2") [])) .default
  }

  Lean.addDecl <| .thmDecl {
    name := Odd_toNat.str Lean.Meta.unfoldThmSuffix
    levelParams := []
    type := .forallE `o (.const ``Odd []) (.app (.app (.app (.const ``Eq [.succ .zero]) Odd_toNat_body) (.app (.const Odd_toNat []) (.bvar 0))) (.app (.app (.app (.const (Odd_toNat.str "match_1") [.succ .zero]) Odd_toNat_type) (.bvar 0)) Odd_toNat_succ)) .default
    value := .lam `o (.const ``Odd []) (.app (.app (.app (.const ``Odd.casesOn [.zero]) (.lam `o (.const ``Odd []) (.app (.app (.app (.const ``Eq [.succ .zero]) Odd_toNat_body) (.app (.const Odd_toNat []) (.bvar 0))) (.app (.app (.app (.const (Odd_toNat.str "match_1") [.succ .zero]) Odd_toNat_type) (.bvar 0)) Odd_toNat_succ)) .default)) (.bvar 0)) (.const (Odd_toNat.str "eq_1") [])) .default
  }

  Lean.addDecl <| .defnDecl {
    name := Lean.Meta.mkSmartUnfoldingNameFor Even_toNat
    levelParams := []
    type := Even_toNat_type .forallE
    value := .lam `e (.const ``Even []) (Lean.Meta.markSmartUnfoldingMatch (.app (.app (.app (.app (.const (Even_toNat.str "match_1") [.succ .zero]) Even_toNat_type) (.bvar 0)) (Lean.Meta.markSmartUnfoldingMatchAlt Even_toNat_zero)) (.lam `o (.const ``Odd []) (Lean.Meta.markSmartUnfoldingMatchAlt Even_toNat_succ_body) .default))) .default
    hints := .opaque
    safety := .safe
  }

  Lean.addDecl <| .defnDecl {
    name := Lean.Meta.mkSmartUnfoldingNameFor Odd_toNat
    levelParams := []
    type := Odd_toNat_type .forallE
    value := .lam `o (.const ``Odd []) (Lean.Meta.markSmartUnfoldingMatch (.app (.app (.app (.const (Odd_toNat.str "match_1") [.succ .zero]) Odd_toNat_type) (.bvar 0)) (.lam `e (.const ``Even []) (Lean.Meta.markSmartUnfoldingMatchAlt Odd_toNat_succ_body) .default))) .default
    hints := .opaque
    safety := .safe
  }

example : Even.toNat (.succ o) = sorry := by rw [Even.toNat]; sorry
example : Even.toNat (.succ o) = sorry := by unfold Even.toNat; sorry
example : Even.toNat (.succ o) = sorry := by dsimp only [Even.toNat]; sorry
example : Even.toNat (.succ o) = sorry := by simp only [Even.toNat]; sorry
example : Even.toNat e = sorry := by rw [Even.toNat]; sorry
example : Even.toNat e = sorry := by unfold Even.toNat; sorry
example : Even.toNat e = sorry := by dsimp only [Even.toNat]; sorry
example : Even.toNat e = sorry := by simp only [Even.toNat]; sorry

inductive Vector : Nat → Type
  | nil : Vector .zero
  | cons : Nat → Vector n → Vector n.succ

example : Vector (Even.toNat (.succ o)) := .cons 0 sorry

#reduce Even.toNat (.succ (.succ .zero))
#eval Even.toNat (.succ (.succ .zero))
