structure Set where
  α : Type u
  r : α → α → Prop
  x : α

instance : Setoid Set where
  r S T := ∃ r : S.α → T.α → Prop, r S.x T.x ∧ ∀ v w, r v w → (∀ x, S.r x v → ∃ y, T.r y w ∧ r x y) ∧ (∀ y, T.r y w → ∃ x, S.r x v ∧ r x y)
  iseqv.refl _ := ⟨Eq, rfl, fun | _, _, rfl => ⟨fun x h => ⟨x, h, rfl⟩, fun y h => ⟨y, h, rfl⟩⟩⟩
  iseqv.symm | ⟨r, hx, h⟩ => ⟨fun y x => r x y, hx, fun v w hvw => (h w v hvw).symm⟩
  iseqv.trans
  | ⟨r₁, hx₁, h₁⟩, ⟨r₂, hx₂, h₂⟩ =>
    ⟨fun x z => ∃ y, r₁ x y ∧ r₂ y z, ⟨_, hx₁, hx₂⟩, fun v w ⟨vw, hvw₁, hvw₂⟩ => ⟨
      fun x hxv => let ⟨y, hyvw, hxy⟩ := (h₁ v vw hvw₁).left x hxv; let ⟨z, hzw, hyz⟩ := (h₂ vw w hvw₂).left y hyvw; ⟨z, hzw, y, hxy, hyz⟩,
      fun z hzw => let ⟨y, hyvw, hyz⟩ := (h₂ vw w hvw₂).right z hzw; let ⟨x, hxv, hxy⟩ := (h₁ v vw hvw₁).right y hyvw; ⟨x, hxv, y, hxy, hyz⟩
    ⟩⟩

instance : Membership Set Set where
  mem T S := ∃ y : T.α, T.r y T.x ∧ S ≈ { T with x := y }

theorem Set.mem_cong {S S' T T' : Set} : S ∈ T → S ≈ S' → T ≈ T' → S' ∈ T'
  | ⟨y, hyx, hST⟩, hS, ⟨r, hx, h⟩ => let ⟨y', hyx', hy'⟩ := (h T.x T'.x hx).left y hyx; ⟨y', hyx', Setoid.trans (Setoid.symm hS) (Setoid.trans hST ⟨r, hy', h⟩)⟩

theorem no_embedding
  (Lower : Type (u + 1) → Type u)
  (down : ∀ {α}, α → Lower α)
  (up : ∀ {α}, Lower α → α)
  (up_down : ∀ {α} (x : α), up (down x) = x)
: False :=
  let P (S : Set.{u}) : Prop := ¬S ∈ S
  have hP {S T} (h : S ≈ T) (hS : P S) : P T :=
    fun hT => hS (Set.mem_cong hT (Setoid.symm h) (Setoid.symm h))
  let Ω : Set.{u} := {
    α := Option (Lower Set)
    r a b := ∃ ha, (∃ hb, up (a.get ha) ∈ up (b.get hb)) ∨ b = none ∧ P (up (a.get ha))
    x := none
  }
  have Ω_cong a : { Ω with x := some a } ≈ up a :=
    ⟨fun x y => ∃ h, up (x.get h) ≈ { up a with x := y }, ⟨rfl, Setoid.refl (up a)⟩, fun (some v) w ⟨_, r, hx, h⟩ => ⟨
      fun (some x) ⟨_, .inl ⟨_, y, hy, h'⟩⟩ => let ⟨y', hyw', hy'⟩ := (h (up v).x w hx).left y hy; ⟨y', hyw', rfl, Setoid.trans h' ⟨r, hy', h⟩⟩,
      fun y hyw => ⟨some (down { up a with x := y }), ⟨rfl, .inl ⟨rfl, let ⟨x, hx, hxy⟩ := (h _ w hx).right y hyw; by simp [up_down]; exact ⟨x, hx, Setoid.symm ⟨r, hxy, h⟩⟩⟩⟩, rfl, by simp [up_down]; exact Setoid.refl _⟩
    ⟩⟩
  have Ω_mem S : S ∈ Ω ↔ P S := ⟨
    fun ⟨some y, ⟨_, hy⟩, h⟩ => hP (Setoid.symm (Setoid.trans h (Ω_cong y))) (hy.resolve_left nofun).right,
    fun h => ⟨some (down S), ⟨rfl, .inr ⟨rfl, by simp [up_down]; exact h⟩⟩, have := Ω_cong (down S); by simp only [up_down] at this; exact Setoid.symm this⟩
  ⟩
  iff_not_self (Ω_mem Ω)
