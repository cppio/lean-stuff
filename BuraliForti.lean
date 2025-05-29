theorem WellFounded.irrefl (wf : WellFounded r) : ¬r a a
  | haa => (wf.apply a).rec (motive := fun b _ => a ≠ b) (fun | _, _, h, rfl => h a haa rfl) rfl

theorem WellFounded.asymm (wf : WellFounded r) : r a b → ¬r b a
  | hab, hba => (wf.apply a).rec (motive := fun c _ => ¬(a = c ∨ b = c)) (fun | _, _, h, .inl rfl => h b hba (.inr rfl) | _, _, h, .inr rfl => h a hab (.inl rfl)) (.inl rfl)

structure WellOrder where
  α : Type u
  r : α → α → Prop

  connected a b : r a b ∨ a = b ∨ r b a
  wf : WellFounded r

theorem WellOrder.trans (self : WellOrder) {a b c} : self.r a b → self.r b c → self.r a c
  | hab, hbc =>
    match self.connected a c with
    | .inl hac => hac
    | .inr (.inl hac) => (self.wf.asymm hab (hac ▸ hbc)).elim
    | .inr (.inr hac) => (self.wf.apply a).rec (motive := fun d _ => d = a ∨ d = b ∨ d = c → self.r a c) (fun | _, _, h, .inl rfl => h c hac (.inr (.inr rfl)) | _, _, h, .inr (.inl rfl) => h a hab (.inl rfl) | _, _, h, .inr (.inr rfl) => h b hbc (.inr (.inl rfl))) (.inl rfl)

def WellOrder.segment (self : WellOrder) (b : self.α) : WellOrder where
  α := { a // self.r a b }
  r a b := self.r a.val b.val
  connected a b := self.connected a b |>.imp_right <| .imp_left Subtype.eq
  wf := InvImage.wf Subtype.val self.wf

instance : Setoid WellOrder where
  r X Y := ∃ f : X.α → Y.α, (∀ {a b}, X.r a b → Y.r (f a) (f b)) ∧ ∃ g : Y.α → X.α, (∀ {a b}, Y.r a b → X.r (g a) (g b)) ∧ (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)
  iseqv.refl _ := ⟨id, id, id, id, fun _ => rfl, fun _ => rfl⟩
  iseqv.symm | ⟨f, hf, g, hg, hgf, hfg⟩ => ⟨g, hg, f, hf, hfg, hgf⟩
  iseqv.trans | ⟨f, hf, g, hg, hgf, hfg⟩, ⟨f', hf', g', hg', hgf', hfg'⟩ => ⟨f' ∘ f, hf' ∘ hf, g ∘ g', hg ∘ hg', fun x => (hgf' (f x) ▸ hgf x :), fun y => (hfg (g' y) ▸ hfg' y :)⟩

instance : LT WellOrder where
  lt X Y := ∃ a, X ≈ Y.segment a

theorem WellOrder.lt_cong {X Y X' Y' : WellOrder} : X < Y → X ≈ X' → Y ≈ Y' → X' < Y'
  | ⟨a, h₁⟩, h₂, ⟨f, hf, g, hg, hgf, hfg⟩ => ⟨f a, Setoid.trans (Setoid.symm h₂) (Setoid.trans h₁ ⟨fun ⟨x, hx⟩ => ⟨f x, hf hx⟩, hf, fun ⟨y, hy⟩ => ⟨g y, hgf a ▸ hg hy⟩, hg, fun _ => Subtype.eq (hgf _), fun _ => Subtype.eq (hfg _)⟩)⟩

theorem WellOrder.lt_trans {X Y Z : WellOrder} : X < Y → Y < Z → X < Z
  | ⟨a, f, hf, g, hg, h₁, h₂⟩, ⟨a', f', hf', g', hg', h₁', h₂'⟩ => ⟨(f' a).val, fun x => ⟨(f' (f x).val).val, hf' (f x).property⟩, fun h'' => hf' (hf h''), fun ⟨z, hz⟩ => g ⟨g' ⟨z, Z.trans hz (f' a).property⟩, (h₁' a ▸ hg' (a := ⟨_, _⟩) hz :)⟩, fun h'' => hg <| hg' h'', fun x => .trans (by dsimp; congr; exact h₁' (f x).val) (h₁ x), fun ⟨z, hz⟩ => Subtype.eq (by dsimp; rw [h₂, h₂'])⟩

theorem WellOrder.lt_wf : @WellFounded WellOrder LT.lt :=
  ⟨fun X => ⟨X, fun Y ⟨a, h⟩ => by induction X.wf.apply a generalizing Y with | intro a _ ih => constructor; intro Z ⟨b, f', hf', g', hg', h₁', h₂'⟩; rcases h with ⟨f, hf, g, hg, h₁, h₂⟩; exact ih (f b).val (f b).property Z (lt_trans ⟨b, f', hf', g', hg', h₁', h₂'⟩ ⟨a, f, hf, g, hg, h₁, h₂⟩) ⟨fun z => ⟨(f (f' z).val).val, hf (f' z).property⟩, fun h'' => hf (hf' h''), fun ⟨x, hx⟩ => g' ⟨g ⟨x, X.trans hx (f b).property⟩, (h₁ b ▸ (hg hx : Y.r (g ⟨x, _⟩) _) :)⟩, fun h'' => hg' (hg h''), fun z => .trans (by dsimp; congr; exact h₁ (f' z).val) (h₁' z), fun ⟨x, hx⟩ => Subtype.eq (by dsimp; rw [h₂', h₂])⟩⟩⟩

theorem WellFounded.has_min (self : @WellFounded α r) (s : α → Prop) a : s a → ¬¬∃ b, s b ∧ ∀ x, s x → ¬r x b :=
  (self.apply a).rec fun x _ IH hx hne => hne ⟨x, hx, fun y hy hyx => IH y hyx hy hne⟩

theorem WellOrder.lt_irrefl {X Y : WellOrder} : X < Y → ¬X ≈ Y
  | ⟨y, h₁⟩, h₂ =>
    let ⟨_, _, g, hg, _⟩ := Setoid.trans (Setoid.symm h₁) h₂
    Y.wf.has_min (fun z => Y.r (g z).val z) y (g y).property fun ⟨x, hx₁, hx₂⟩ => hx₂ (g x).val (hg hx₁) hx₁

theorem WellOrder.segment_mono (self : WellOrder) {x y} : self.r x y → self.segment x < self.segment y
  | h => ⟨⟨x, h⟩, fun ⟨z, hz⟩ => ⟨⟨z, self.trans hz h⟩, hz⟩, id, fun ⟨z, hz⟩ => ⟨z.val, hz⟩, id, fun _ => rfl, fun _ => rfl⟩

theorem WellOrder.segment_inj (self : WellOrder) {x y} : self.segment x ≈ self.segment y → x = y
  | h =>
    match self.connected x y with
    | .inl h' => (lt_irrefl (self.segment_mono h') h).elim
    | .inr (.inl h') => h'
    | .inr (.inr h') => (lt_irrefl (self.segment_mono h') (Setoid.symm h)).elim

theorem WellOrder.segment_mono_rev (self : WellOrder) {x y} : self.segment x < self.segment y → self.r x y
  | h =>
    match self.connected x y with
    | .inl h' => h'
    | .inr (.inl h') => by cases h'; cases lt_irrefl h (Setoid.refl _)
    | .inr (.inr h') => by cases lt_irrefl (lt_trans h (self.segment_mono h')) (Setoid.refl _)

theorem WellOrder.lt_connected (X Y : WellOrder) : X < Y ∨ X ≈ Y ∨ Y < X := by
  let P x := ∃ y, X.segment x ≈ Y.segment y
  let ⟨f, hf⟩ : { f : { x // P x } → Y.α // ∀ z, X.segment z.val ≈ Y.segment (f z) } := ⟨_, fun z => Classical.choose_spec z.property⟩
  have f_mono {a b} (h : X.r a.val b.val) : Y.r (f a) (f b) := Y.segment_mono_rev (lt_cong (X.segment_mono h) (hf a) (hf b))
  have f_mono_rev {a b} (h : Y.r (f a) (f b)) : X.r a.val b.val := X.segment_mono_rev (lt_cong (Y.segment_mono h) (Setoid.symm (hf a)) (Setoid.symm (hf b)))
  have f_inj {a b} (h : f a = f b) : a = b := Subtype.eq (X.segment_inj (Setoid.trans (h ▸ hf a) (Setoid.symm (hf b))))
  cases Classical.em (∀ x, P x) with
  | inl h =>
    cases Classical.em (∀ y, ∃ x, y = f ⟨x, h x⟩) with
    | inl h' =>
      refine .inr (.inl ?_)
      refine ⟨fun x => f ⟨x, h x⟩, (f_mono ·), fun y => Classical.choose (h' y), ?_, ?_, ?_⟩
      . intro y y' h
        dsimp
        generalize hx : Classical.choose _ = x
        replace hx := hx ▸ Classical.choose_spec _
        generalize hx' : Classical.choose _ = x'
        replace hx' := hx' ▸ Classical.choose_spec _
        cases hx
        cases hx'
        exact f_mono_rev h
      . intro x
        dsimp
        generalize hy : Classical.choose _ = y
        replace hy := hy ▸ Classical.choose_spec _
        exact congrArg Subtype.val (f_inj hy).symm
      . intro y
        dsimp
        generalize hx : Classical.choose _ = x
        replace hx := hx ▸ Classical.choose_spec _
        exact hx.symm
    | inr h' =>
      refine .inl ?_
      simp at h'
      rcases h' with ⟨y, hy⟩
      have := Classical.not_not.1 <| Y.wf.has_min (∀ x, · ≠ f ⟨x, h x⟩) y hy
      clear y hy
      rcases this with ⟨y, hy, hy'⟩
      refine ⟨y, fun x => ⟨f ⟨x, h x⟩, ?_⟩, (f_mono ·), fun ⟨y, hy⟩ => Classical.choose (Classical.not_not.1 fun h' => hy' y (fun x' hx' => h' ⟨x', hx'⟩) hy), ?_, ?_, ?_⟩
      . match Y.connected (f ⟨x, h x⟩) y with
        | .inl h' => exact h'
        | .inr (.inl h') => cases h'; cases hy x rfl
        | .inr (.inr h') =>
          exfalso
          let ⟨f', hf', g', hg', hgf', hfg'⟩ := hf ⟨x, h x⟩
          apply hy (g' ⟨y, h'⟩).val
          apply Y.segment_inj
          refine Setoid.trans ?_ (hf _)
          exact ⟨fun ⟨z, hz⟩ => ⟨(g' ⟨z, Y.trans hz h'⟩).val, hg' hz⟩, (hg' ·), fun ⟨z, hz⟩ => ⟨(f' ⟨z, X.trans hz (g' _).property⟩).val, (hfg' ⟨y, h'⟩ ▸ @hf' ⟨z, _⟩ _ hz :)⟩, (hf' ·), fun _ => Subtype.eq (congrArg Subtype.val (hfg' _) :), fun _ => Subtype.eq (congrArg Subtype.val (hgf' _) :)⟩
      . intro ⟨y, hy⟩ ⟨y', hy'⟩ h
        dsimp
        generalize hx : Classical.choose _ = x
        replace hx := hx ▸ Classical.choose_spec _
        generalize hx' : Classical.choose _ = x'
        replace hx' := hx' ▸ Classical.choose_spec _
        cases hx
        cases hx'
        exact f_mono_rev h
      . intro x
        dsimp
        generalize hy : Classical.choose _ = y
        replace hy := hy ▸ Classical.choose_spec _
        exact congrArg Subtype.val (f_inj hy).symm
      . intro ⟨y, hy⟩
        dsimp
        generalize hx : Classical.choose _ = x
        replace hx := hx ▸ Classical.choose_spec _
        exact Subtype.eq hx.symm
  | inr h =>
    have P_down {x y} : X.r x y → P y → P x := by
      intro hxy ⟨z, f, hf, g, hg, hgf, hfg⟩
      exact ⟨(f ⟨x, hxy⟩).val, fun ⟨w, hw⟩ => ⟨(f ⟨w, X.trans hw hxy⟩).val, hf hw⟩, (hf ·), fun ⟨w, hw⟩ => ⟨(g ⟨w, Y.trans hw (f ⟨x, hxy⟩).property⟩).val, (hgf ⟨x, hxy⟩ ▸ @hg ⟨w, _⟩ _ hw :)⟩, (hg ·), fun _ => Subtype.eq (congrArg Subtype.val (hgf _) :), fun _ => Subtype.eq (congrArg Subtype.val (hfg _) :)⟩
    refine .inr (.inr ?_)
    simp at h
    rcases h with ⟨x, hx⟩
    have := Classical.not_not.1 <| X.wf.has_min (¬P ·) x hx
    clear x hx
    rcases this with ⟨x, hx, h'⟩
    refine ⟨x, ?_⟩
    have (x') : P x' ↔ X.r x' x := by
      constructor
      . intro h
        match X.connected x' x with
        | .inl h' => exact h'
        | .inr (.inl h') => cases h'; cases hx h
        | .inr (.inr h') => cases hx (P_down h' h)
      . intro hx'
        apply Classical.not_not.1
        intro hx''
        exact h' x' hx'' hx'
    have (y) : ∃ x hx, y = f ⟨x, (this x).mpr hx⟩ := by
      apply Classical.not_not.1
      intro hy
      simp at hy
      have := Classical.not_not.1 <| Y.wf.has_min (∀ x' hx', · ≠ f ⟨x', (this x').mpr hx'⟩) y hy
      clear y hy
      rcases this with ⟨y, hy, hy'⟩
      replace hy' := fun x h₁ h₂ => hy' x h₂ h₁
      simp at hy'
      refine hx ⟨y, fun ⟨x, hx⟩ => ⟨f ⟨x, (this x).mpr hx⟩, ?_⟩, (f_mono ·), fun ⟨z, hz⟩ => ⟨Classical.choose (hy' z hz), (Classical.choose_spec (hy' z hz)).1⟩, ?_, ?_, ?_⟩
      . match Y.connected (f ⟨x, (this x).mpr hx⟩) y with
        | .inl h => exact h
        | .inr (.inl h) => cases h; cases hy x hx rfl
        | .inr (.inr h) =>
          exfalso
          let ⟨⟨x, hx₁⟩, hx₂⟩ := lt_cong (Y.segment_mono h) (Setoid.refl _) (Setoid.symm (hf _))
          refine hy x (X.trans hx₁ hx) ?_
          apply Y.segment_inj
          refine Setoid.trans ?_ (hf _)
          refine Setoid.trans hx₂ ?_
          exact ⟨fun ⟨⟨x, hx₁⟩, hx₂⟩ => ⟨x, hx₂⟩, id, fun ⟨x, hx⟩ => ⟨⟨x, X.trans hx hx₁⟩, hx⟩, id, fun _ => rfl, fun _ => rfl⟩
      . intro ⟨y, hy⟩ ⟨y', hy'⟩ h
        dsimp [segment]
        generalize hx : Classical.choose _ = x
        replace ⟨hx, hx'⟩ := hx ▸ Classical.choose_spec _
        cases hx'
        generalize hx' : Classical.choose _ = x'
        replace ⟨hx', hx''⟩ := hx' ▸ Classical.choose_spec _
        cases hx''
        exact f_mono_rev h
      . intro ⟨x, hx⟩ 
        apply Subtype.eq
        dsimp
        generalize hx : Classical.choose _ = x'
        replace ⟨hx, hx'⟩ := hx ▸ Classical.choose_spec _
        cases f_inj hx'
        rfl
      . intro ⟨y', hy⟩
        exact Subtype.eq (Classical.choose_spec (hy' y' hy)).2.symm
    refine ⟨fun y => ⟨Classical.choose (this y), (Classical.choose_spec (this y)).1⟩, fun h => ?_, fun ⟨x, hx⟩ => f ⟨x, Classical.not_not.1 fun h => h' x h hx⟩, (f_mono ·), ?_, ?_⟩
    . dsimp [segment]
      generalize hx : Classical.choose _ = x
      replace ⟨hx, hx'⟩ := hx ▸ Classical.choose_spec _
      cases hx'
      generalize hx' : Classical.choose _ = x'
      replace ⟨hx', hx''⟩ := hx' ▸ Classical.choose_spec _
      cases hx''
      exact f_mono_rev h
    . intro y
      dsimp
      let ⟨x, hx, h⟩ := this y
      cases h
      congr
      generalize hx : Classical.choose _ = x'
      replace ⟨hx, hx'⟩ := hx ▸ Classical.choose_spec _
      cases f_inj hx'
      rfl
    . intro ⟨y, hy⟩
      apply Subtype.eq
      dsimp
      generalize hx : Classical.choose _ = x
      replace ⟨hx, hx'⟩ := hx ▸ Classical.choose_spec _
      cases f_inj hx'
      rfl

def Ordinal := Quotient (inferInstanceAs (Setoid WellOrder))

instance : LT Ordinal where
  lt α β := α.lift (fun X => β.lift (fun Y => X < Y) fun Y Y' hY => propext ⟨(WellOrder.lt_cong · (Setoid.refl X) hY), (WellOrder.lt_cong · (Setoid.refl X) (Setoid.symm hY))⟩) fun X X' hX => by dsimp; congr; funext Y; exact propext ⟨(WellOrder.lt_cong · hX (Setoid.refl Y)), (WellOrder.lt_cong · (Setoid.symm hX) (Setoid.refl Y))⟩

theorem Ordinal.lt_wf : @WellFounded Ordinal LT.lt :=
  ⟨Quot.ind fun X => (WellOrder.lt_wf.apply X).rec fun _ _ h => ⟨_, Quot.ind h⟩⟩

theorem Ordinal.lt_connected (α β : Ordinal) : α < β ∨ α = β ∨ β < α := by
  revert α β
  apply Quot.ind
  intro X
  apply Quot.ind
  intro Y
  match WellOrder.lt_connected X Y with
  | .inl h => exact .inl h
  | .inr (.inl h) => exact .inr (.inl (Quot.sound h))
  | .inr (.inr h) => exact .inr (.inr h)

noncomputable def WellOrder.lt_witness (X Y : WellOrder) : X < Y → Y.α :=
  Classical.choose

theorem WellOrder.lt_witness_spec {X Y : WellOrder} : (h : X < Y) → X ≈ Y.segment (lt_witness X Y h) :=
  Classical.choose_spec

theorem WellOrder.lt_witness_cong {X X' Y : WellOrder} (h : X < Y) (hX : X ≈ X') : lt_witness X Y h = lt_witness X' Y (lt_cong h hX (Setoid.refl Y)) := by
  generalize hy : lt_witness X Y h = y
  replace hy := hy ▸ lt_witness_spec h
  generalize hy' : lt_witness X' Y (lt_cong h hX (Setoid.refl Y)) = y'
  replace hy' := hy' ▸ lt_witness_spec (lt_cong h hX (Setoid.refl Y))
  exact Y.segment_inj (Setoid.trans (Setoid.symm hy) (Setoid.trans hX hy'))

theorem WellOrder.lt_witness_mono {X X' Y : WellOrder} (h : X' < Y) (hX : X < X') : Y.r (lt_witness X Y (lt_trans hX h)) (lt_witness X' Y h) := by
  generalize hy : lt_witness X Y (lt_trans hX h) = y
  replace hy := hy ▸ lt_witness_spec (lt_trans hX h)
  generalize hy' : lt_witness X' Y h = y'
  replace hy' := hy' ▸ lt_witness_spec h
  exact Y.segment_mono_rev (lt_cong hX hy hy')

theorem WellOrder.lt_witness_self : lt_witness (X.segment x) X ⟨x, Setoid.refl _⟩ = x := by
  generalize hy : lt_witness (X.segment x) X ⟨x, Setoid.refl _⟩ = y
  replace hy := hy ▸ lt_witness_spec ⟨x, Setoid.refl _⟩
  exact (X.segment_inj hy).symm

noncomputable def Ordinal.lt_witness (α : Ordinal) X : α < .mk _ X → X.α :=
  α.rec (fun Y => WellOrder.lt_witness Y X) fun Y Y' hY => by
    have {α : Ordinal} (eq : .mk _ Y = α) : Eq.ndrec (motive := (· < .mk _ X → X.α)) (WellOrder.lt_witness Y X) eq = fun h => WellOrder.lt_witness _ X (eq ▸ h) := by
      cases eq
      rfl
    rewrite [this (Quot.sound hY)]
    clear this
    funext h
    exact WellOrder.lt_witness_cong _ hY

theorem Ordinal.lt_witness_eq (h : X < Y) : lt_witness (Quot.mk _ X) Y h = WellOrder.lt_witness X Y h :=
  rfl

theorem no_embedding
  (Lower : Type (u + 1) → Type u)
  (down : ∀ {α}, α → Lower α)
  (up : ∀ {α}, Lower α → α)
  (up_down : ∀ {α} (x : α), up (down x) = x)
  (down_up : ∀ {α} (x : Lower α), down (up x) = x)
: False := by
  let Ω : WellOrder := {
    α := Lower Ordinal
    r x y := up x < up y
    connected x y := Ordinal.lt_connected (up x) (up y) |>.imp_right <| .imp_left fun h => (down_up x).symm.trans ((congrArg down h).trans (down_up y))
    wf := InvImage.wf up Ordinal.lt_wf
  }
  suffices Ω < Ω from
    WellOrder.lt_irrefl this (Setoid.refl Ω)
  refine ⟨down (.mk _ Ω), ?_⟩
  refine ⟨fun x => ⟨down (.mk _ (Ω.segment x)), by simp [Ω, up_down]; exact ⟨x, Setoid.refl _⟩⟩, fun h => by simp [WellOrder.segment, Ω, up_down]; exact Ω.segment_mono h, fun ⟨x, hx⟩ => Ordinal.lt_witness (up x) Ω (by simp [Ω, up_down] at hx; exact hx), ?_, ?_, ?_⟩
  . intro ⟨x, hx⟩ ⟨y, hy⟩ h
    let ⟨α, hα⟩ : ∃ α, down α = x := ⟨up x, down_up x⟩
    cases hα
    let ⟨β, hβ⟩ : ∃ β, down β = y := ⟨up y, down_up y⟩
    cases hβ
    revert α β
    apply Quot.ind
    intro Y hY'
    apply Quot.ind
    intro Z hZ' h
    simp [WellOrder.segment, Ω, up_down] at h
    simp [up_down, Ordinal.lt_witness_eq]
    apply WellOrder.lt_witness_mono
    exact h
  . intro x
    simp [up_down, Quotient.mk, Ordinal.lt_witness_eq]
    exact WellOrder.lt_witness_self
  . intro ⟨x, hx⟩
    let ⟨α, hα⟩ : ∃ α, down α = x := ⟨up x, down_up x⟩
    cases hα
    revert α
    apply Quot.ind
    intro Y hY
    dsimp
    congr 2
    apply Quot.sound
    simp [up_down, Ordinal.lt_witness_eq]
    apply Setoid.symm
    apply WellOrder.lt_witness_spec
