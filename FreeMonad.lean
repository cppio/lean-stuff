namespace Quot

variable {α : Sort u} {r : α → α → Prop} {β : Sort v} {γ : Sort w} (f : (β → α) → γ)

private unsafe def liftF.impl (_ : ∀ a b, (∀ x, mk r (a x) = mk r (b x)) → f a = f b) (q : β → Quot r) : γ :=
  f λ x => unsafeCast <| q x

@[implemented_by liftF.impl]
def liftF (c : ∀ a b, (∀ x, mk r (a x) = mk r (b x)) → f a = f b) (q : β → Quot r) : γ :=
  f λ x => Classical.choose (q x).exists_rep

theorem liftF_mk (c : ∀ a b, (∀ x, mk r (a x) = mk r (b x)) → f a = f b) (a : β → α) : liftF f c (λ x => mk r (a x)) = f a :=
  c _ a λ _ => Classical.choose_spec <| exists_rep _

end Quot

namespace Quotient

variable {α : Sort u} {s : Setoid α} {β : Sort v} {γ : Sort w} (f : (β → α) → γ) (c : ∀ a b, (∀ x, a x ≈ b x) → f a = f b)

def liftF (q : β → Quotient s) : γ :=
  Quot.liftF f (λ a b h => c a b λ x => exact <| h x) q

theorem liftF_mk (a : β → α) : Quotient.liftF f c (λ x => .mk s (a x)) = f a :=
  Quot.liftF_mk ..

end Quotient

set_option autoImplicit false

universe u

inductive FreeStateM (σ α : Type u) : Type u
  | pure (a : α)
  | get (k : σ → FreeStateM σ α)
  | set (s : σ) (k : FreeStateM σ α)

variable {σ α : Type u}

inductive FreeStateM.Eq : FreeStateM σ α → FreeStateM σ α → Prop
  | pure a : Eq (pure a) (pure a)
  | get {k₁ k₂} : (∀ s, Eq (k₁ s) (k₂ s)) → Eq (get k₁) (get k₂)
  | set {k₁ k₂} s : Eq k₁ k₂ → Eq (set s k₁) (set s k₂)

  | symm {k₁ k₂} : Eq k₁ k₂ → Eq k₂ k₁
  | trans {k₁ k₂ k₃} : Eq k₁ k₂ → Eq k₂ k₃ → Eq k₁ k₃

  | get_get (k : _ → _) : Eq (get (λ s => get (k s))) (get (λ s => k s s))
  | get_set k : Eq (get λ s => set s k) k
  | set_get s k : Eq (set s (get k)) (set s (k s))
  | set_set s₁ s₂ k : Eq (set s₁ (set s₂ k)) (set s₂ k)

theorem FreeStateM.Eq.refl : (k : FreeStateM σ α) → Eq k k
  | .pure a => pure a
  | .get k => get λ s => refl (k s)
  | .set s k => set s <| refl k

def StateM' (σ α : Type u) := Quotient ⟨@FreeStateM.Eq σ α, .refl, .symm, .trans⟩

def StateM'.pure (a : α) : StateM' σ α :=
  .mk _ <| .pure a

def StateM'.get : (k : σ → StateM' σ α) → StateM' σ α :=
  .liftF (λ k => .mk _ <| .get k) λ _ _ hk => Quot.sound <| .get hk

def StateM'.set (s : σ) : (k : StateM' σ α) → StateM' σ α :=
  .lift (λ k => .mk _ <| .set s k) λ _ _ hk => Quot.sound <| .set s hk

def StateM'.bind' {β : Type u} (f : α → StateM' σ β) : (k : FreeStateM σ α) → StateM' σ β
  | .pure a => f a
  | .get k => .get λ s => bind' f (k s)
  | .set s k => .set s (bind' f k)

theorem StateM'.bind_wf {β} f k₁ k₂ (hk : FreeStateM.Eq k₁ k₂) : @bind' σ α β f k₁ = bind' f k₂ := by
  induction hk with dsimp [bind']
  | get _ ih => congr; exact funext ih
  | set => congr
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | get_get k =>
    refine .trans (Quotient.liftF_mk ..) ?_
    apply Quot.sound
    exact .get_get ..
  | get_set k =>
    cases bind' f k using Quot.ind with
    | mk =>
      apply Quot.sound
      refine .trans ?_ <| .get_set _
      refine .get ?_
      intro s
      apply Quotient.exact (s := ⟨_, _⟩)
      exact Classical.choose_spec <| Quot.exists_rep _
  | set_get s k =>
    cases h : bind' f (k s) using Quot.ind with
    | mk =>
      apply Quot.sound
      refine .trans (.set_get ..) ?_
      refine .set _ ?_
      apply Quotient.exact (s := ⟨_, _⟩)
      refine .trans ?_ h
      exact Classical.choose_spec <| Quot.exists_rep _
  | set_set s₁ s₂ k =>
    cases bind' f k using Quot.ind with
    | mk =>
      apply Quot.sound
      exact .set_set ..

def StateM'.bind {β : Type u} (f : α → StateM' σ β) : (k : StateM' σ α) → StateM' σ β :=
  .lift (bind' f) (bind_wf f)

instance : Monad (StateM' σ) where
  pure := .pure
  bind k := k.bind

@[simp]
theorem StateM'.bind_pure {β} f a : @bind σ α β f (pure a) = f a := rfl

@[simp]
theorem StateM'.bind_get {β} f k : @bind σ α β f (get k) = get λ s => bind f (k s) := by
  refine Quot.sound <| .get λ s => ?_
  apply Quotient.exact (s := ⟨_, _⟩)
  generalize h : k s = x
  have h₁ : ∃ a, _ = k s := Quot.exists_rep _
  have h₂ : ∃ a, _ = bind' f (Classical.choose h₁) := Quot.exists_rep _
  have h₃ : ∃ a, _ = bind f (k s) := Quot.exists_rep _
  cases x using Quot.ind with
  | mk x =>
    show Quot.mk _ (Classical.choose h₂) = Quot.mk _ (Classical.choose h₃)
    apply Eq.trans <| Classical.choose_spec h₂
    apply Eq.trans <| bind_wf f _ x <| Quotient.exact <| Classical.choose_spec h₁ |>.trans h
    apply Eq.trans _ <| .symm <| Classical.choose_spec h₃
    exact .symm <| congrArg _ h

@[simp]
theorem StateM'.bind_set {β} f s k : @bind σ α β f (set s k) = set s (bind f k) := by
  cases k using Quot.ind with
  | mk => rfl

@[eliminator]
def StateM'.ind {motive : StateM' σ α → Prop}
  (pure : ∀ a, motive (pure a))
  (get : ∀ k, (∀ s, motive (k s)) → motive (get k))
  (set : ∀ s k, motive k → motive (set s k))
  t : motive t := by
  cases t using Quot.ind with
  | mk t =>
    induction t with
    | pure a => exact pure a
    | get _ ih =>
      specialize get _ ih
      conv at get => arg 1; apply Quotient.liftF_mk
      exact get
    | set s _ ih => exact set s _ ih

instance : LawfulMonad (StateM' σ) where
  map_const := rfl
  id_map x := by
    dsimp [Functor.map]
    induction x with simp <;> congr
    | get _ ih => exact funext ih
  seqLeft_eq x y := by
    dsimp [SeqLeft.seqLeft, Seq.seq, Functor.map]
    induction x with simp <;> congr
    | get _ ih => exact funext ih
  seqRight_eq x y := by
    dsimp [SeqRight.seqRight, Seq.seq, Functor.map]
    induction x with simp <;> congr
    | pure =>
      induction y with simp <;> congr
      | get _ ih => exact funext ih
    | get _ ih => exact funext ih
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc x _ _ := by
    dsimp [bind]
    induction x with simp <;> congr
    | get _ ih => exact funext ih

instance : MonadState σ (StateM' σ) where
  get := .get .pure
  set s := .set s (.pure .unit)
  modifyGet f := .get λ s => let (a, s) := f s; .set s (.pure a)

def StateM'.toStateM' : FreeStateM σ α → StateM σ α
  | .pure a => StateT.pure a
  | .get k => StateT.get.bind λ s => toStateM' <| k s
  | .set s k => StateT.set s |>.bind λ _ => toStateM' k

theorem StateM'.toStateM_wf (k₁ k₂ : FreeStateM σ α) (hk : FreeStateM.Eq k₁ k₂) : toStateM' k₁ = toStateM' k₂ := by
  induction hk with dsimp [toStateM', StateT.bind, StateT.get, StateT.set]
  | get _ ih => exact funext λ s => congrFun (ih s) s
  | set s _ ih => exact funext λ _ => congrFun ih s
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def StateM'.ofStateM : StateM σ α → StateM' σ α := modifyGet
def StateM'.toStateM : StateM' σ α → StateM σ α := Quot.lift toStateM' toStateM_wf

@[simp]
theorem StateM'.toStateM_pure a : @toStateM σ α (pure a) = StateT.pure a := rfl

@[simp]
theorem StateM'.toStateM_get k : @toStateM σ α (get k) = StateT.get.bind λ s => toStateM (k s) := by
  funext s
  generalize h : k s = x
  cases x using Quot.ind with
  | mk x =>
    show toStateM' (Classical.choose _) s = toStateM _ _
    apply Eq.trans
    . apply congrFun (f := toStateM' <| Classical.choose _)
      apply toStateM_wf _ x
      apply Quotient.exact (s := ⟨_, _⟩)
      apply Eq.trans _ h
      exact Classical.choose_spec <| Quot.exists_rep _
    rw [h]
    rfl

@[simp]
theorem StateM'.toStateM_set s k : @toStateM σ α (set s k) = (StateT.set s).bind λ _ => toStateM k := by
  cases k using Quot.ind with
  | mk k => rfl

theorem StateM'.toStateM_ofStateM (k : StateM σ α) : toStateM (ofStateM k) = k := by
  funext s
  show toStateM' (Classical.choose _) s = _
  apply congrFun (g := λ _ => k s)
  apply toStateM_wf _ <| .set _ <| .pure _
  apply Quotient.exact (s := ⟨_, _⟩)
  exact Classical.choose_spec <| Quot.exists_rep _

theorem StateM'.ofStateM_toStateM (k : StateM' σ α) : ofStateM (toStateM k) = k := by
  dsimp [ofStateM, modifyGet]
  apply Eq.trans <| Quotient.liftF_mk ..
  cases k using Quot.ind with
  | mk k =>
    apply Quot.sound
    dsimp [toStateM]
    induction k with dsimp [toStateM', StateT.pure, StateT.bind, StateT.get, StateT.set]
    | pure => exact .get_set _
    | get k ih =>
      refine .trans ?_ <| .get ih
      clear ih
      refine .trans ?_ <| .symm <| .get_get _
      exact .refl _
    | set s k ih =>
      refine .trans ?_ <| .get_set _
      refine .get ?_
      intro s'
      refine .trans ?_ <| .symm <| .set_set ..
      clear s'
      refine .trans ?_ <| ih.set s
      clear ih
      refine .trans ?_ <| .symm <| .set_get ..
      refine .trans ?_ <| .symm <| .set_set ..
      exact .refl _

theorem StateM'.toStateM_get' : @toStateM σ σ MonadState.get = StateT.get := by simp [MonadState.get]; rfl
theorem StateM'.toStateM_set' s : @toStateM σ PUnit (MonadState.set s) = StateT.set s := rfl

theorem StateM'.toStateM_bind {β} (f : α → StateM' σ β) x : @toStateM σ β (bind f x) = StateT.bind (toStateM x) λ x => toStateM (f x) := by
  funext s
  induction x generalizing s with simp
  | pure => rfl
  | get _ ih => exact ih s s
  | set s' _ ih => exact ih s'

theorem StateM'.ofStateM_pure a : @ofStateM σ α (StateT.pure a) = pure a := by
  apply Quot.sound
  refine .trans ?_ <| .get_set _
  refine .get ?_
  intro s
  apply Quotient.exact (s := ⟨_, _⟩)
  exact Classical.choose_spec <| Quot.exists_rep _

theorem StateM'.ofStateM_get' : @ofStateM σ σ StateT.get = MonadState.get := by
  apply Quot.sound
  apply FreeStateM.Eq.trans
  . apply FreeStateM.Eq.get
    intro s
    apply Quotient.exact (s := ⟨_, _⟩)
    exact Classical.choose_spec <| Quot.exists_rep _
  . refine .symm ?_
    apply FreeStateM.Eq.trans
    . apply FreeStateM.Eq.get
      intro s
      apply Quotient.exact (s := ⟨_, _⟩)
      exact Classical.choose_spec <| Quot.exists_rep _
    . refine .trans (.symm <| .get_set _) ?_
      apply FreeStateM.Eq.get
      intro s
      exact .set_get _ _

theorem StateM'.ofStateM_set' s : @ofStateM σ PUnit (StateT.set s) = MonadState.set s := by
  apply Quot.sound
  apply FreeStateM.Eq.trans
  . apply FreeStateM.Eq.get
    intro s'
    apply Quotient.exact (s := ⟨_, _⟩)
    exact Classical.choose_spec <| Quot.exists_rep _
  . refine .trans ?_ <| .get_set _
    refine .get ?_
    intro s'
    refine .trans ?_ <| .symm <| .set_set ..
    exact .refl _

theorem StateM'.ofStateM_bind {β} (f : α → StateM σ β) x : @ofStateM σ β (StateT.bind x f) = bind (λ x => ofStateM (f x)) (ofStateM x) := by
  apply Quot.sound
  apply FreeStateM.Eq.trans
  . apply FreeStateM.Eq.get
    intro s
    apply Quotient.exact (s := ⟨_, _⟩)
    exact Classical.choose_spec <| Quot.exists_rep _
  . refine .symm ?_
    apply FreeStateM.Eq.trans
    . apply FreeStateM.Eq.get
      intro s
      have : ∃ a, Quot.mk _ a = match x s with | (a, s) => Quot.mk FreeStateM.Eq (.set s <| .pure a) := Quot.exists_rep _
      conv at «this» => rhs; ext; rhs; change Quot.mk FreeStateM.Eq <| .set (x s).snd <| .pure (x s).fst
      show FreeStateM.Eq (Classical.choose (_ : ∃ a, Quot.mk _ a = bind' _ (Classical.choose this))) _
      have := bind_wf (λ x => ofStateM (f x)) (Classical.choose this) (.set (x s).snd <| .pure (x s).fst) <| Quotient.exact (s := ⟨_, .refl, .symm, .trans⟩) <| Classical.choose_spec this
      simp [this]
      apply Quotient.exact (s := ⟨_, _⟩)
      exact Classical.choose_spec <| Quot.exists_rep _
    . refine .get ?_
      intro s
      refine .trans (.set_get ..) ?_
      refine .trans ?_ <| .set_set (x s).snd _ _
      refine .set _ ?_
      apply Quotient.exact (s := ⟨_, _⟩)
      exact Classical.choose_spec <| Quot.exists_rep _
