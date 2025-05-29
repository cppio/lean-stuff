theorem WellFounded.irrefl (wf : WellFounded r) : ¬r a a
  | raa => wf.apply a |>.rec (motive := fun b _ => b ≠ a) (fun | _, _, ih, rfl => ih a raa rfl) rfl

structure Order where
  α : Type u
  r : α → α → Prop

  trans : r a b → r b c → r a c
  wf : WellFounded r

def Order.segment (self : Order) (b : self.α) : Order where
  α := { a // self.r a b }
  r a b := self.r a.val b.val
  trans := self.trans
  wf := InvImage.wf Subtype.val self.wf

instance : LT Order where
  lt X Y := ∃ a, ∃ f : X.α → (Y.segment a).α, ∀ {a b}, X.r a b → Y.r (f a).val (f b).val

theorem Order.lt_trans {X Y Z : Order} : X < Y → Y < Z → X < Z
  | ⟨_, f, hf⟩, ⟨a', f', hf'⟩ => ⟨a', f' ∘ Subtype.val ∘ f, hf' ∘ hf⟩

theorem Order.lt_wf : @WellFounded Order LT.lt := by
  refine ⟨fun X => ⟨X, fun Y ⟨a, f, hf⟩ => ?_⟩⟩
  induction X.wf.apply a generalizing Y with
  | intro a _ ih =>
    exact ⟨Y, fun Z ⟨a', f', hf'⟩ => ih _ (f a').property Z (lt_trans ‹_› ‹_›) (fun z => ⟨_, hf (f' z).property⟩) (hf ∘ hf')⟩

theorem Order.segment_mono (self : Order) {x y} : self.r x y → self.segment x < self.segment y
  | h => ⟨⟨x, h⟩, fun ⟨x', h'⟩ => ⟨⟨x', self.trans h' h⟩, h'⟩, id⟩

theorem no_embedding
  (Lower : Type (u + 1) → Type u)
  (down : ∀ {α}, α → Lower α)
  (up : ∀ {α}, Lower α → α)
  (up_down : ∀ {α} (x : α), up (down x) = x)
: False := by
  let Ω : Order := {
    α := Lower Order
    r x y := up x < up y
    trans := Order.lt_trans
    wf := InvImage.wf up Order.lt_wf
  }
  suffices Ω < Ω from
    Order.lt_wf.irrefl this
  refine ⟨down Ω, fun x => ⟨down (Ω.segment x), ?_⟩, fun h => ?_⟩
  . simp [Ω, up_down]
    exact ⟨x, id, id⟩
  . simp [Ω, up_down]
    exact Ω.segment_mono h
