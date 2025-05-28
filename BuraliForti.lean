structure WellOrder where
  α : Type u
  r : α → α → Prop

  connected a b : r a b ∨ a = b ∨ r b a
  wf : WellFounded r

def WellOrder.subtype (self : WellOrder) (P : self.α → Prop) : WellOrder where
  α := { x // P x }
  r := fun x y => self.r x y
  connected a b := propext Subtype.eq_iff ▸ self.connected a b
  wf := by
    constructor
    intro ⟨x, hx⟩
    have := self.wf.apply x
    induction this with
    | intro x _ ih =>
    exact ⟨_, fun ⟨y, hy⟩ h => ih y h hy⟩

theorem WellOrder.irrefl (self : WellOrder) {a} : ¬self.r a a
  | haa => (self.wf.apply a).rec (motive := fun b _ => a ≠ b) (fun | _, _, h, rfl => h a haa rfl) rfl

theorem WellOrder.ne_of_lt (self : WellOrder) {a b} : self.r a b → a ≠ b
  | h, rfl => self.irrefl h

theorem WellOrder.asymm (self : WellOrder) {a b} : self.r a b → ¬self.r b a
  | hab, hba => (self.wf.apply a).rec (motive := fun c _ => a ≠ c ∧ b ≠ c) (fun _ _ h => ⟨fun | rfl => (h b hba).right rfl, fun | rfl => (h a hab).left rfl⟩) |>.left rfl

theorem WellOrder.trans (self : WellOrder) {a b c} : self.r a b → self.r b c → self.r a c
  | hab, hbc =>
    match self.connected a c with
    | .inl hac => hac
    | .inr (.inl hac) => (self.asymm hab (hac ▸ hbc)).elim
    | .inr (.inr hac) => (self.wf.apply a).rec (motive := fun d _ => (a = d ∨ b = d ∨ c = d) → self.r a c) (fun | _, _, h, .inl rfl => h c hac (.inr (.inr rfl)) | _, _, h, .inr (.inl rfl) => h a hab (.inl rfl) | _, _, h, .inr (.inr rfl) => h b hbc (.inr (.inl rfl))) (.inl rfl)

instance : Setoid WellOrder where
  r X Y := ∃ f : X.α → Y.α, (∀ {a b}, X.r a b → Y.r (f a) (f b)) ∧ ∃ g : Y.α → X.α, (∀ {a b}, Y.r a b → X.r (g a) (g b)) ∧ (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)
  iseqv.refl X := ⟨id, id, id, id, fun _ => rfl, fun _ => rfl⟩
  iseqv.symm | ⟨f, hf, g, hg, hgf, hfg⟩ => ⟨g, hg, f, hf, hfg, hgf⟩
  iseqv.trans | ⟨f, hf, g, hg, hgf, hfg⟩, ⟨f', hf', g', hg', hgf', hfg'⟩ => ⟨f' ∘ f, hf' ∘ hf, g ∘ g', hg ∘ hg', by simp [hgf', hgf], by simp [hfg, hfg']⟩

theorem WellOrder.subtype_true (self : WellOrder) {P} (h : ∀ x, P x) : self.subtype P ≈ self :=
  ⟨Subtype.val, id, fun x => ⟨x, h x⟩, id, fun _ => rfl, fun _ => rfl⟩

theorem WellOrder.subtype_subtype (self : WellOrder) {P Q} : (self.subtype P).subtype Q ≈ self.subtype (∃ h, Q ⟨·, h⟩) :=
  ⟨fun ⟨⟨x, p⟩, q⟩ => ⟨x, p, q⟩, id, fun ⟨x, pq⟩ => ⟨⟨x, pq.1⟩, pq.2⟩, id, fun _ => rfl, fun _ => rfl⟩

instance : LT WellOrder where
  lt X Y := ∃ a : Y.α, X ≈ Y.subtype (Y.r · a)

theorem WellOrder.lt_cong {X Y X' Y' : WellOrder} : X < Y → X ≈ X' → Y ≈ Y' → X' < Y'
  | ⟨a, h₁⟩, h₂, ⟨f, hf, g, hg, hgf, hfg⟩ => ⟨f a, Setoid.trans (Setoid.symm h₂) (Setoid.trans h₁ ⟨fun ⟨x, hx⟩ => ⟨f x, hf hx⟩, hf, fun ⟨y, hy⟩ => ⟨g y, hgf a ▸ hg hy⟩, hg, by simp [subtype, hgf], by simp [subtype, hfg]⟩)⟩

theorem WellOrder.lt_trans {X Y Z : WellOrder} : X < Y → Y < Z → X < Z
  | ⟨a, f, hf, g, hg, h₁, h₂⟩, ⟨a', f', hf', g', hg', h₁', h₂'⟩ => ⟨(f' a).val, fun x => ⟨(f' (f x).val).val, hf' (f x).property⟩, fun h'' => hf' (hf h''), fun ⟨z, hz⟩ => g ⟨g' ⟨z, Z.trans hz (f' a).property⟩, (h₁' a ▸ hg' (a := ⟨_, _⟩) hz :)⟩, fun h'' => hg <| hg' h'', fun x => .trans (by simp; congr; exact h₁' (f x).val) (h₁ x), fun ⟨z, hz⟩ => by simp [h₂, h₂']⟩

theorem WellOrder.lt_wf : @WellFounded WellOrder LT.lt :=
  ⟨fun X => ⟨X, fun Y ⟨a, h⟩ => by induction X.wf.apply a generalizing Y with | intro a _ ih => constructor; intro Z ⟨b, f', hf', g', hg', h₁', h₂'⟩; rcases h with ⟨f, hf, g, hg, h₁, h₂⟩; exact ih (f b).val (f b).property Z (lt_trans ⟨b, f', hf', g', hg', h₁', h₂'⟩ ⟨a, f, hf, g, hg, h₁, h₂⟩) ⟨fun z => ⟨(f (f' z).val).val, hf (f' z).property⟩, fun h'' => hf (hf' h''), fun ⟨x, hx⟩ => g' ⟨g ⟨x, X.trans hx (f b).property⟩, (h₁ b ▸ (hg hx : Y.r (g ⟨x, _⟩) _) :)⟩, fun h'' => hg' (hg h''), fun z => .trans (by simp; congr; exact h₁ (f' z).val) (h₁' z), fun ⟨x, hx⟩ => by simp [h₂', h₂]⟩⟩⟩

theorem WellFounded.has_min (self : @WellFounded α r) (s : α → Prop) a : s a → ¬¬∃ b, s b ∧ ∀ x, s x → ¬r x b :=
  (self.apply a).rec fun x _ IH hx hne => hne ⟨x, hx, fun y hy hyx => IH y hyx hy hne⟩

theorem WellOrder.lt_irrefl {X Y : WellOrder} : X < Y → ¬X ≈ Y := by
  intro ⟨y, h₁⟩ h₂
  let ⟨f, hf, g, hg, h₁, h₂⟩ := Setoid.trans (Setoid.symm h₁) h₂
  dsimp [subtype] at f hf g hg h₁ h₂
  have : (g y).val ≠ y := fun h => Y.irrefl (h ▸ (g y).property)
  apply Y.wf.has_min (fun z => (g z).val ≠ z) y this
  intro ⟨x, hx₁, hx₂⟩
  match Y.connected (g x).val x with
  | .inl hx => exact hx₂ (g x).val (Y.ne_of_lt (hg hx)) hx
  | .inr (.inl hx) => exact hx₁ hx
  | .inr (.inr hx) =>
    let z := f ⟨x, Y.trans hx (g x).property⟩
    have : g z = ⟨x, _⟩ := h₁ _
    match Y.connected z x with
    | .inl hz => exact hx₂ z (this ▸ (Y.ne_of_lt hz).symm) hz
    | .inr (.inl hz) => exact hx₁ ((hz ▸ this) ▸ rfl)
    | .inr (.inr hz) => exact Y.irrefl (Y.trans hx (this ▸ hg hz :))

theorem WellOrder.subtype_mono (self : WellOrder) {x y} : self.r x y → self.subtype (self.r · x) < self.subtype (self.r · y)
  | h => ⟨⟨x, h⟩, fun ⟨z, hz⟩ => ⟨⟨z, self.trans hz h⟩, hz⟩, id, fun ⟨z, hz⟩ => ⟨z.val, hz⟩, id, fun _ => rfl, fun _ => rfl⟩

theorem WellOrder.subtype_inj (self : WellOrder) {x y} : self.subtype (self.r · x) ≈ self.subtype (self.r · y) → x = y
  | h =>
    match self.connected x y with
    | .inl h' => (lt_irrefl (self.subtype_mono h') h).elim
    | .inr (.inl h') => h'
    | .inr (.inr h') => (lt_irrefl (self.subtype_mono h') (Setoid.symm h)).elim

theorem WellOrder.subtype_mono_rev (self : WellOrder) {x y} : self.subtype (self.r · x) < self.subtype (self.r · y) → self.r x y
  | h =>
    match self.connected x y with
    | .inl h' => h'
    | .inr (.inl h') => by cases h'; cases lt_irrefl h (Setoid.refl _)
    | .inr (.inr h') => by cases lt_irrefl (lt_trans h (self.subtype_mono h')) (Setoid.refl _)

theorem WellOrder.lt_connected (X Y : WellOrder) : X < Y ∨ X ≈ Y ∨ Y < X := by
  let P x := ∃ y, X.subtype (X.r · x) ≈ Y.subtype (Y.r · y)
  let ⟨f, hf⟩ : { f : { x // P x } → Y.α // ∀ z, X.subtype (X.r · z.val) ≈ Y.subtype (Y.r · (f z)) } := ⟨_, fun z => Classical.choose_spec z.property⟩
  have f_mono {a b} (h : (X.subtype P).r a b) : Y.r (f a) (f b) := Y.subtype_mono_rev (lt_cong (X.subtype_mono h) (hf a) (hf b))
  have f_mono_rev {a b} (h : Y.r (f a) (f b)) : (X.subtype P).r a b := X.subtype_mono_rev (lt_cong (Y.subtype_mono h) (Setoid.symm (hf a)) (Setoid.symm (hf b)))
  have f_inj {a b} (h : f a = f b) : a = b :=
    match X.connected a b with
    | .inl h' => (Y.irrefl (h ▸ f_mono h')).elim
    | .inr (.inl h') => Subtype.eq h'
    | .inr (.inr h') => (Y.irrefl (h ▸ f_mono h')).elim
  cases Classical.em (∀ x, P x) with
  | inl h =>
    have : X ≈ Y.subtype fun y => ∃ x, y = f ⟨x, h x⟩ := by
      refine ⟨fun x => ⟨_, x, rfl⟩, (f_mono ·), fun ⟨y, hy⟩ => Classical.choose hy, ?_, ?_, ?_⟩
      . intro ⟨y, hy⟩ ⟨y', hy'⟩ h
        dsimp
        generalize hx : Classical.choose hy = x
        replace hx := hx ▸ Classical.choose_spec hy
        generalize hx' : Classical.choose hy' = x'
        replace hx' := hx' ▸ Classical.choose_spec hy'
        cases hx
        cases hx'
        exact f_mono_rev h
      . intro x
        dsimp
        generalize hy : Classical.choose _ = y
        replace hy := hy ▸ Classical.choose_spec _
        exact X.subtype_inj (Setoid.trans (hy ▸ hf ⟨y, h y⟩) (Setoid.symm (hf ⟨x, h x⟩)))
      . intro ⟨y, hy⟩
        dsimp
        generalize hx : Classical.choose hy = x
        replace hx := hx ▸ Classical.choose_spec hy
        cases hx
        rfl
    cases Classical.em (∀ y, ∃ x, y = f ⟨x, h x⟩) with
    | inl h' => exact .inr (.inl (Setoid.trans this (Y.subtype_true h')))
    | inr h' =>
      refine .inl ?_
      simp at h'
      rcases h' with ⟨y, hy⟩
      have := Classical.not_not.1 <| Y.wf.has_min (∀ x, · ≠ f ⟨x, h x⟩) y hy
      clear y hy
      rcases this with ⟨y, hy, hy'⟩
      refine ⟨y, Setoid.trans this ?_⟩
      refine cast ?_ (Setoid.refl (Y.subtype (Y.r · y)))
      congr
      funext y'
      simp
      constructor
      . exact fun h => Classical.not_not.1 fun h' => hy' y' (fun x' hx' => h' ⟨x', hx'⟩) h
      . intro ⟨x, h⟩
        cases h
        match Y.connected (f ⟨x, h x⟩) y with
        | .inl h' => exact h'
        | .inr (.inl h') => cases h'; cases hy x rfl
        | .inr (.inr h') =>
          exfalso
          let ⟨f', hf', g', hg', hgf', hfg'⟩ := hf ⟨x, h x⟩
          apply hy (g' ⟨y, h'⟩).val
          apply Y.subtype_inj
          refine Setoid.trans ?_ (hf _)
          exact ⟨fun ⟨z, hz⟩ => ⟨(g' ⟨z, Y.trans hz h'⟩).val, hg' hz⟩, (hg' ·), fun ⟨z, hz⟩ => ⟨(f' ⟨z, X.trans hz (g' _).property⟩).val, (hfg' ⟨y, h'⟩ ▸ @hf' ⟨z, _⟩ _ hz :)⟩, (hf' ·), fun _ => Subtype.eq (congrArg Subtype.val (hfg' _) :), fun _ => Subtype.eq (congrArg Subtype.val (hgf' _) :)⟩
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
          let ⟨⟨x, hx₁⟩, hx₂⟩ := lt_cong (Y.subtype_mono h) (Setoid.refl _) (Setoid.symm (hf _))
          refine hy x (X.trans hx₁ hx) ?_
          apply Y.subtype_inj
          refine Setoid.trans ?_ (hf _)
          refine Setoid.trans hx₂ ?_
          refine Setoid.trans X.subtype_subtype ?_
          refine cast ?_ (Setoid.refl (X.subtype (X.r · x)))
          congr
          funext x'
          simp
          constructor
          . intro h
            exact ⟨X.trans h hx₁, h⟩
          . intro ⟨h, h'⟩
            exact h'
      . intro ⟨y, hy⟩ ⟨y', hy'⟩ h
        dsimp [subtype]
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
    . dsimp [subtype]
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

theorem WellOrder.lt_witness_spec {X Y : WellOrder} : (h : X < Y) → X ≈ Y.subtype (Y.r · (lt_witness X Y h)) :=
  Classical.choose_spec

theorem WellOrder.lt_witness_cong {X X' Y : WellOrder} (h : X < Y) (hX : X ≈ X') : lt_witness X Y h = lt_witness X' Y (lt_cong h hX (Setoid.refl Y)) := by
  generalize hy : lt_witness X Y h = y
  replace hy := hy ▸ lt_witness_spec h
  generalize hy' : lt_witness X' Y (lt_cong h hX (Setoid.refl Y)) = y'
  replace hy' := hy' ▸ lt_witness_spec (lt_cong h hX (Setoid.refl Y))
  exact Y.subtype_inj (Setoid.trans (Setoid.symm hy) (Setoid.trans hX hy'))

theorem WellOrder.lt_witness_mono {X X' Y : WellOrder} (h : X' < Y) (hX : X < X') : Y.r (lt_witness X Y (lt_trans hX h)) (lt_witness X' Y h) := by
  generalize hy : lt_witness X Y (lt_trans hX h) = y
  replace hy := hy ▸ lt_witness_spec (lt_trans hX h)
  generalize hy' : lt_witness X' Y h = y'
  replace hy' := hy' ▸ lt_witness_spec h
  exact Y.subtype_mono_rev (lt_cong hX hy hy')

theorem WellOrder.lt_witness_self : lt_witness (X.subtype (X.r · x)) X ⟨x, Setoid.refl _⟩ = x := by
  generalize hy : lt_witness (X.subtype (X.r · x)) X ⟨x, Setoid.refl _⟩ = y
  replace hy := hy ▸ lt_witness_spec ⟨x, Setoid.refl _⟩
  exact (X.subtype_inj hy).symm

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

/-
def Ω : WellOrder where
  α := Ordinal
  r := LT.lt
  connected := Ordinal.lt_connected
  wf := Ordinal.lt_wf
-/

axiom Ω : WellOrder
axiom f : Ω.{u}.α → Ordinal.{u}
axiom g : Ordinal.{u} → Ω.{u}.α
axiom f_g : ∀ x, f (g x) = x
axiom g_f : ∀ x, g (f x) = x
axiom Ω.r_eq : Ω.{u}.r = fun x y => f x < f y

theorem Ω_lt_Ω : Ω.{u} < Ω.{u} := by
  refine ⟨g (.mk _ Ω.{u}), Setoid.symm (Ω.subtype_true fun x => ?_)⟩
  simp [Ω.r_eq, f_g]
  generalize f x = α
  clear x
  revert α
  apply Quot.ind
  intro X
  refine ⟨g (.mk _ X), ?_⟩
  simp [Ω.r_eq]
  refine ⟨fun x => ⟨g (.mk _ (X.subtype (X.r · x))), by simp [f_g]; exact ⟨x, Setoid.refl _⟩⟩, fun h => by simp [WellOrder.subtype, Ω.r_eq, f_g]; exact X.subtype_mono h, fun ⟨x, hx⟩ => Ordinal.lt_witness (f x) X (by simp [f_g] at hx; exact hx), ?_, ?_, ?_⟩
  . intro ⟨x, hx⟩ ⟨y, hy⟩ h
    let ⟨α, hα⟩ : ∃ α, g α = x := ⟨f x, g_f x⟩
    cases hα
    let ⟨β, hβ⟩ : ∃ β, g β = y := ⟨f y, g_f y⟩
    cases hβ
    revert α β
    apply Quot.ind
    intro Y hY'
    apply Quot.ind
    intro Z hZ' h
    simp [WellOrder.subtype, Ω.r_eq, f_g] at h
    simp [f_g, Ordinal.lt_witness_eq]
    apply WellOrder.lt_witness_mono
    exact h
  . intro x
    simp [f_g, Quotient.mk, Ordinal.lt_witness_eq]
    exact WellOrder.lt_witness_self
  . intro ⟨x, hx⟩
    let ⟨α, hα⟩ : ∃ α, g α = x := ⟨f x, g_f x⟩
    cases hα
    revert α
    apply Quot.ind
    intro Y hY
    dsimp
    congr 2
    apply Quot.sound
    simp [f_g, Ordinal.lt_witness_eq]
    apply Setoid.symm
    apply WellOrder.lt_witness_spec

theorem False.intro : False :=
  WellOrder.lt_irrefl Ω_lt_Ω (Setoid.refl Ω.{0})
