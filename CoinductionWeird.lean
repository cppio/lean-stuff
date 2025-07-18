@[simp]
theorem eqRec_heq_eq : (@Eq.rec α x motive lhs y h ≍ rhs) = (lhs ≍ rhs) :=
  by cases h; rfl

theorem eqRec_pi {α : Sort u} {x : α} {motive₁ : ∀ y, x = y → Sort v} (motive₂ : ∀ y h, motive₁ y h → Sort w) {refl : ∀ z, motive₂ x rfl z} {y : α} {h : x = y} : @Eq.rec α x (fun y h => ∀ z, motive₂ y h z) refl y h = fun z => cast (by cases h; rfl) (refl (h.symm.rec (motive := fun x h' => motive₁ x (h.trans h')) z)) :=
  by cases h; rfl

@[simp]
theorem eqRec_eqRec {α : Sort u} {x : α} {motive : ∀ y, x = y → Sort v} {refl : motive x rfl} {y : α} {h : x = y} {z : α} {h' : y = z} : @Eq.rec α y (fun z h' => motive z (h.trans h')) (@Eq.rec α x motive refl y h) z h' = @Eq.rec α x motive refl z (h.trans h') :=
  by cases h; rfl

theorem hfunext {α : Sort u} {β γ : α → Sort v} {f : ∀ x, β x} {g : ∀ x, γ x} (h : ∀ x, f x ≍ g x) : f ≍ g := by
  cases funext fun x => type_eq_of_heq (h x)
  simp at h ⊢
  exact funext h

theorem hfunext' {α α' : Sort u} {β : α → Sort v} {γ : α' → Sort v} {f : ∀ x, β x} {g : ∀ y, γ y} (hα : α = α') (h : ∀ x y, x ≍ y → f x ≍ g y) : f ≍ g := by
  cases hα
  simp at h
  cases funext fun x => type_eq_of_heq (h x)
  simp at h ⊢
  exact funext h

variable {α : Type} {β : α → Type}

variable (hd : σ → α) (tl : ∀ s, β (hd s) → σ) in
inductive Valid : σ → List (Σ a, β a) → α → Prop
  | nil : Valid s [] (hd s)
  | cons : Valid (tl s b) bs a → Valid s (⟨hd s, b⟩ :: bs) a

theorem Valid.comap (f : σ' → σ) (hd_f : ∀ s, hd (f s) = hd' s) (tl_f : ∀ s b, tl (f s) b = f (tl' s (hd_f s ▸ b))) (h : @Valid σ α β hd tl (f s) bs a) : @Valid σ' α β hd' tl' s bs a := by
  generalize hs : f s = s' at h
  induction h generalizing s with
  | nil =>
    cases hs
    rewrite [hd_f]
    constructor
  | cons =>
    cases hs
    generalize hb : Sigma.mk .. = b'
    rcases b' with ⟨a, b'⟩
    cases (congrArg (·.1) hb).symm.trans (hd_f s)
    constructor
    grind

theorem Valid.ext {σ hd tl} {r : σ → σ → Prop} (rhd : ∀ {s s'}, r s s' → hd s = hd s') (rtl : ∀ {s s'} h b, r (tl s b) (tl s' (rhd h ▸ b))) {s s'} (rs : r s s') (h : @Valid σ α β hd tl s bs a) : Valid hd tl s' bs a := by
  induction h generalizing s' with
  | nil => rewrite [rhd rs]; constructor
  | @cons _ b _ _ h ih =>
    generalize hb : Sigma.mk .. = b
    cases b
    simp [rhd rs] at hb
    rcases hb with ⟨rfl, hb⟩
    constructor
    replace hb : rhd rs ▸ b = _ := eq_of_heq (.trans (by simp) hb)
    exact ih (hb ▸ rtl rs _)

def Valid' (hd : σ → α) (tl : ∀ s, β (hd s) → σ) (s : σ) (bs : List (Σ a, β a)) (a : α) : Prop :=
  match bs with
  | [] => a = hd s
  | b :: bs => ∃ h : b.1 = hd s, Valid' hd tl (tl s (h ▸ b.2)) bs a
  --bs.foldr (fun b k s => ∃ h : b.1 = hd s, k (tl s (h ▸ b.2))) (fun s => a = hd s) s

theorem Valid'.comap (f : σ' → σ) (hd_f : ∀ s, hd (f s) = hd' s) (tl_f : ∀ s b, tl (f s) b = f (tl' s (hd_f s ▸ b))) (h : @Valid' α β σ hd tl (f s) bs a) : @Valid' α β σ' hd' tl' s bs a :=
  by induction bs generalizing s with grind [Valid']

variable (γ : List (Σ a, β a) → α → Type)

def MW.Approx : Nat → (σ : Type) × (σ → List (Σ a, β a) → α → Prop)
  | 0 => ⟨Unit, fun _ _ _ => False⟩
  | ℓ + 1 =>
    let p s bs a := bs.casesOn (a = s.1) fun b bs => ∃ h : b.1 = s.1, (Approx ℓ).2 (s.2 (h ▸ b.2)) bs a
    ⟨(s : Σ hd, β hd → (Approx ℓ).1) × ∀ bs a, p s bs a → γ bs a, (p ·.1)⟩

variable {γ} in
def MW.Agree (s : (Approx γ ℓ).1) (s' : (Approx γ ℓ').1) : Prop :=
  match ℓ, ℓ' with
  | 0, _ | _ + 1, 0 => True
  | _ + 1, _ + 1 => ∃ hhd : s.1.1 = s'.1.1, (∀ b, Agree (s.1.2 b) (s'.1.2 (hhd ▸ b))) ∧ ∀ bs a h h', s.2 bs a h = s'.2 bs a h'

def MW : Type :=
  { f : ∀ ℓ, (MW.Approx γ ℓ).1 // ∀ ℓ ℓ', MW.Agree (f ℓ) (f ℓ') }

variable {γ}

def MW.hd (self : MW γ) : α :=
  (self.1 1).1.1

def MW.tl (self : MW γ) (b : β self.hd) : MW γ :=
  ⟨fun ℓ => (self.1 ℓ.succ).1.2 ((self.2 1 ℓ.succ).1 ▸ b), fun ℓ ℓ' => cast (by grind only) ((self.2 ℓ.succ ℓ'.succ).2.1 ((self.2 1 ℓ.succ).1 ▸ b))⟩

def MW.val (self : MW γ) (bs : List (Σ a, β a)) a (h : Valid hd tl self bs a) : γ bs a :=
  (self.1 bs.length.succ).2 bs a <| by
    change (Approx γ bs.length.succ).2 (self.1 bs.length.succ) bs a
    induction bs generalizing self with
    | nil => cases h with | nil => rfl
    | cons b bs ih => cases h with | cons h => exact ⟨(self.2 1 (bs.length + 2)).1, ih (self.tl _) h⟩

def MW.corec' (σ : Type u) (hd : σ → α) (tl : ∀ s, β (hd s) → σ) (val : ∀ (s : σ) bs a, Valid hd tl s bs a → γ bs a) (s : σ) : ∀ ℓ, { x : (Approx γ ℓ).1 // ∀ bs a, (Approx γ ℓ).2 x bs a → Valid hd tl s bs a }
  | 0 => ⟨(), nofun⟩
  | ℓ + 1 =>
    have pf bs a (h : bs.casesOn (a = hd s) fun b bs => ∃ h : b.1 = hd s, (Approx γ ℓ).snd (corec' σ hd tl val (tl s (h ▸ b.2)) ℓ).val bs a) : Valid hd tl s bs a := by
      cases bs with
      | nil => cases h; constructor
      | cons b bs =>
        rcases b with ⟨_, b⟩
        rcases h with ⟨h', h⟩
        cases h'
        exact .cons ((corec' σ hd tl val (tl s b) ℓ).2 bs a h)
    ⟨⟨⟨hd s, fun b => corec' σ hd tl val (tl s b) ℓ⟩, fun bs a h => val s bs a (pf bs a h)⟩, pf⟩

def MW.corec (σ : Type u) (hd : σ → α) (tl : ∀ s, β (hd s) → σ) (val : ∀ (s : σ) bs a, Valid hd tl s bs a → γ bs a) (s : σ) : MW γ :=
  .mk (fun ℓ => (corec' σ hd tl val s ℓ).1) fun ℓ ℓ' => by
    induction ℓ generalizing s ℓ' with | zero => constructor | succ ℓ ih =>
    cases ℓ' with | zero => constructor | succ ℓ' =>
    exact ⟨rfl, fun b => ih (tl s b) ℓ', fun bs a h h' => rfl⟩

def MW.hd_corec σ hd tl val s : (@corec α β γ σ hd tl val s).hd = hd s :=
  rfl

def MW.tl_corec σ hd tl val s b : (@corec α β γ σ hd tl val s).tl b = corec σ hd tl val (tl s b) :=
  rfl

def MW.val_corec σ hd tl val s bs a h : (@corec α β γ σ hd tl val s).val bs a h = val s bs a (h.comap (corec σ hd tl val) (fun _ => rfl) (fun _ _ => rfl)) :=
  rfl

theorem MW.ext (r : (lhs rhs : MW γ) → Prop) (hd : ∀ {lhs rhs}, r lhs rhs → hd lhs = hd rhs) (tl : ∀ {lhs rhs} h b, r (tl lhs b) (tl rhs (hd h ▸ b))) (val : ∀ {lhs rhs} (h : r lhs rhs) bs a v, val lhs bs a v = val rhs bs a (Valid.ext @hd @tl h v)) {lhs rhs} (h : r lhs rhs) : lhs = rhs := by
  apply Subtype.eq
  funext ℓ
  induction ℓ using Nat.rec generalizing lhs rhs with | zero => rfl | succ ℓ ih =>
  have : (lhs.1 ℓ.succ).1.1 = (rhs.1 ℓ.succ).1.1 :=
    calc (lhs.1 ℓ.succ).1.1
      _ = lhs.hd             := (lhs.2 ℓ.succ 1).1
      _ = rhs.hd             := hd h
      _ = (rhs.1 ℓ.succ).1.1 := (rhs.2 1 ℓ.succ).1
  dsimp only [Approx]
  ext
  . exact this
  . refine .trans (b := fun b => (rhs.1 ℓ.succ).1.2 (this ▸ b)) (heq_of_eq ?_) (eqRec_pi (motive₁ := fun a _ => β a) (fun _ _ _ => (Approx γ ℓ).1) ▸ (eqRec_heq_eq (motive := fun a _ => β a → (Approx γ ℓ).1) (h := this.symm) (rhs := (rhs.1 ℓ.succ).1.2)).mpr .rfl)
    funext b
    specialize ih (tl h ((lhs.2 1 ℓ.succ).1 ▸ b :))
    simp [MW.tl] at ih
    exact ih
  . clear ih
    refine hfunext fun bs => hfunext fun a => ?_
    refine hfunext' ?_ fun v v' h => ?_
    . cases bs with
      | nil => simp [this]
      | cons b bs =>
        rcases b with ⟨_, b⟩
        ext
        constructor
        . intro ⟨h', v⟩
          obtain rfl : _ = lhs.hd := h'.trans (lhs.2 ℓ.succ 1).1
          refine ⟨.trans h' this, ?_⟩
          obtain rfl : h' = (lhs.2 1 ℓ.succ).1 := rfl
          change (Approx γ ℓ).2 ((lhs.tl b).1 ℓ) bs a at v
          suffices (Approx γ ℓ).2 ((rhs.tl (hd h ▸ b)).1 ℓ) bs a by simpa [MW.tl]
          have h' := tl h b
          generalize lhs.tl b = lhs' at v h'
          generalize rhs.tl (hd h ▸ b) = rhs' at h'
          clear lhs rhs h this b
          induction ℓ generalizing lhs' rhs' bs with
          | zero => cases v
          | succ ℓ ih =>
            cases bs with
            | nil =>
              cases v
              dsimp!
              rewrite [(lhs'.2 ℓ.succ 1).1, (rhs'.2 ℓ.succ 1).1]
              exact hd h'
            | cons b bs =>
              rcases b with ⟨_, b⟩
              rcases v with ⟨v', v⟩
              cases v'
              refine ⟨?_, ?_⟩
              . rewrite [(lhs'.2 ℓ.succ 1).1, (rhs'.2 ℓ.succ 1).1]
                exact hd h'
              specialize ih bs (lhs'.tl ((lhs'.2 ℓ.succ 1).1 ▸ b : β (lhs'.1 1).1.1)) ?_ (rhs'.tl ((lhs'.2 ℓ.succ 1).1.trans (hd h') ▸ b)) ?_
              . simpa [MW.tl] using v
              . specialize tl h' ((lhs'.2 ℓ.succ 1).1 ▸ b : β (lhs'.1 1).1.1)
                simpa using tl
              simpa [MW.tl] using ih
        . intro ⟨h', v⟩
          obtain rfl : _ = lhs.hd := h'.trans (rhs.2 ℓ.succ 1).1 |>.trans (hd h).symm
          refine ⟨.trans h' this.symm, ?_⟩
          obtain rfl : h' = (hd h).trans (rhs.2 1 ℓ.succ).1 := rfl
          replace v : (Approx γ ℓ).2 ((rhs.tl (hd h ▸ b)).1 ℓ) bs a := by simpa [MW.tl] using v
          change (Approx γ ℓ).2 ((lhs.tl b).1 ℓ) bs a
          have h' := tl h b
          generalize lhs.tl b = lhs' at h'
          generalize rhs.tl (hd h ▸ b) = rhs' at v h'
          clear lhs rhs h this b
          induction ℓ generalizing lhs' rhs' bs with
          | zero => cases v
          | succ ℓ ih =>
            cases bs with
            | nil =>
              cases v
              dsimp!
              rewrite [(lhs'.2 ℓ.succ 1).1, (rhs'.2 ℓ.succ 1).1]
              exact (hd h').symm
            | cons b bs =>
              rcases b with ⟨_, b⟩
              rcases v with ⟨v', v⟩
              cases v'
              refine ⟨?_, ?_⟩
              . rewrite [(lhs'.2 ℓ.succ 1).1, (rhs'.2 ℓ.succ 1).1]
                exact (hd h').symm
              specialize ih bs (lhs'.tl ((rhs'.2 ℓ.succ 1).1.trans (hd h').symm ▸ b)) (rhs'.tl ((rhs'.2 ℓ.succ 1).1 ▸ b : β (rhs'.1 1).1.1)) ?_ ?_
              . simpa [MW.tl] using v
              . specialize tl h' ((rhs'.2 ℓ.succ 1).1.trans (hd h').symm ▸ b)
                simpa using tl
              simpa [MW.tl] using ih
    . clear h
      simp
      change (Approx γ ℓ.succ).2 _ bs a at v
      have v₁ : (Approx γ bs.length.succ).2 (lhs.1 _) bs a := by
        clear rhs h this v'
        induction bs generalizing lhs ℓ with
        | nil => cases v; exact (lhs.2 ℓ.succ 1).1
        | cons b bs ih =>
          rcases b with ⟨_, b⟩
          rcases v with ⟨v', v⟩
          cases v'
          refine ⟨(lhs.2 ℓ.succ bs.length.succ.succ).1, ?_⟩
          cases ℓ with | zero => cases v | succ ℓ =>
          specialize @ih ℓ (lhs.tl ((lhs.2 ℓ.succ.succ 1).1 ▸ b : β (lhs.1 1).1.1)) ?_
          . simpa [MW.tl] using v
          simpa [MW.tl] using ih
      rewrite [(lhs.2 ℓ.succ bs.length.succ).2.2 bs a v v₁]
      clear v
      change (Approx γ ℓ.succ).2 _ bs a at v'
      have v₁' : (Approx γ bs.length.succ).2 (rhs.1 _) bs a := by
        clear lhs h this v₁
        induction bs generalizing rhs ℓ with
        | nil => cases v'; exact (rhs.2 ℓ.succ 1).1
        | cons b bs ih =>
          rcases b with ⟨_, b⟩
          rcases v' with ⟨v', v⟩
          cases v'
          refine ⟨(rhs.2 ℓ.succ bs.length.succ.succ).1, ?_⟩
          cases ℓ with | zero => cases v | succ ℓ =>
          specialize @ih ℓ (rhs.tl ((rhs.2 ℓ.succ.succ 1).1 ▸ b : β (rhs.1 1).1.1)) ?_
          . simpa [MW.tl] using v
          simpa [MW.tl] using ih
      rewrite [(rhs.2 ℓ.succ bs.length.succ).2.2 bs a v' v₁']
      clear v'
      refine val h bs a ?_
      clear rhs h this v₁'
      induction bs generalizing lhs with
      | nil => cases v₁; constructor
      | cons b bs ih =>
        cases b
        rcases v₁ with ⟨h, v⟩
        dsimp at h
        cases h
        generalize hb : Sigma.mk .. = b
        cases b
        obtain rfl := (lhs.2 1 bs.length.succ.succ).1.trans (congrArg (·.1) hb)
        constructor
        apply ih
        simp [MW.tl]
        replace hb : ‹β (lhs.1 bs.length.succ.succ).1.1› = (lhs.2 bs.length.succ.succ 1).1 ▸ ‹_› := by grind only
        cases hb
        exact v
