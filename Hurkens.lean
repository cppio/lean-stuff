structure Paradoxical where
  U : Sort u
  σ : U → U → Prop
  τ : (U → Prop) → U
  paradoxical : σ (τ X) y ↔ ∃ x, X x ∧ y = τ (σ x)

set_option linter.unusedVariables false in
theorem Paradoxical.contradiction (self : Paradoxical) : False :=
  let wf x := ∀ X : self.U → Prop, (∀ x, (∀ y, self.σ x y → X y) → X x) → X x
  have : wf (self.τ wf) := fun X hX =>
    hX _ fun y hy =>
      let ⟨w, hw, h⟩ := self.paradoxical.mp hy
      h ▸ hw _ fun x hx =>
        hX _ fun y hy =>
          let ⟨z, hz, h⟩ := self.paradoxical.mp hy
          h ▸ hx z hz
  this
    (fun y => ¬self.σ y (self.τ (self.σ y)))
    (fun x hx h => hx _ h (self.paradoxical.mpr ⟨_, h, rfl⟩))
    (self.paradoxical.mpr ⟨_, this, rfl⟩)

theorem Paradoxical.no_impredicative
  (Pi : (Type u → Type u) → Type u)
  (lam : ∀ {F}, (∀ A, F A) → Pi F)
  (app : ∀ {F}, Pi F → ∀ A, F A)
  (app_lam : ∀ {F} f A, @app F (lam f) A = f A)
: False :=
  let τ X := lam fun A c a => ∃ x, X x ∧ a = c (app x A c)
  contradiction {
    U := Pi fun A => ((A → Prop) → A) → A → Prop
    τ
    σ x := app x _ τ
    paradoxical := by intros; rw [app_lam]
  }

structure Powerful where
  U : Sort u
  σ : U → (U → Prop) → Prop
  τ : ((U → Prop) → Prop) → U
  powerful : σ (τ C) X ↔ C fun y => X (τ (σ y))

set_option linter.unusedVariables false in
theorem Powerful.contradiction (self : Powerful) : False :=
  let ind X := ∀ x, self.σ x X → X x
  have : ∀ X, ind X → X (self.τ ind) := fun X hX =>
    hX _ <| self.powerful.mpr fun x hx =>
      hX _ (self.powerful.mpr hx)
  this
    (fun y => ¬∀ X, self.σ y X → X (self.τ (self.σ y)))
    (fun x hx h => h _ hx fun X hX => h _ (self.powerful.mp hX))
    (fun X hX => this _ (self.powerful.mp hX))

theorem Powerful.no_impredicative
  (Pi : (Type u → Type u) → Type u)
  (lam : ∀ {F}, (∀ A, F A) → Pi F)
  (app : ∀ {F}, Pi F → ∀ A, F A)
  (app_lam : ∀ {F} f A, @app F (lam f) A = f A)
: False :=
  let τ t := lam fun X f p => t fun x => p (f (app x X f))
  contradiction {
    U := Pi fun A => (((A → Prop) → Prop) → A) → (A → Prop) → Prop
    τ
    σ s := app s _ τ
    powerful := by intros; rewrite [app_lam]; rfl
  }

theorem Powerful.no_impredicative'
  (Pi : (Type u → Type u) → Type u)
  (lam : ∀ {F}, (∀ A, F A) → Pi F)
  (app : ∀ {F}, Pi F → ∀ A, F A)
  (app_lam : ∀ {F} f A, @app F (lam f) A = f A)
: False :=
  let τ u := lam fun X f => f fun q => u fun x => q (app x X f)
  contradiction {
    U := Pi fun A => (((A → Prop) → Prop) → A) → A
    τ
    σ a := app a _ fun F q => F fun x => q (τ x)
    powerful := by intros; rewrite [app_lam]; rfl
  }
