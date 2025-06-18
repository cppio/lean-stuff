inductive W {α : Type u} (β : α → Type v)
  | mk a (t : β a → W β)

private def W.rec'.{u_1} {α : Type u} {β : α → Type v} {motive : W β → Sort u_1} (mk : ∀ a t, (∀ a, motive (t a)) → motive ⟨a, t⟩) : ∀ t, motive t
  | .mk a t => mk a t fun a => @rec' α β motive mk (t a)

@[csimp]
private theorem W.rec_eq_rec' : @rec = @rec' := by
  funext α β motive mk t
  induction t with simp! [*]

def ℕ : Type :=
  W fun
    | false => Empty
    | true => Unit

def ℕ.zero : ℕ :=
  ⟨false, nofun⟩

def ℕ.succ (n : ℕ) : ℕ :=
  ⟨true, fun _ => n⟩

def ℕ.rec {motive : ℕ → Sort u} (zero : motive zero) (succ : ∀ n, motive n → motive (succ n)) : ∀ n, motive n :=
  W.rec fun
    | false, t, _ => (funext nofun : t = nofun) ▸ zero
    | true, t, ht => succ (t ()) (ht ())

/-
inductive V (I : Type u) (α : I → Type v) (β : ∀ i, α i → Type w) (s : ∀ i a, β i a → I) : (i : I) → Type (max u v w)
  | mk i a (t : ∀ b, V I α β s (s i a b)) : V I α β s i
-/

section

variable (I : Type u) (α : I → Type v) (β : ∀ i, α i → Type w) (s : ∀ i a, β i a → I)

def W₁ : Type (max u v w) :=
  W fun a : Sigma α => β a.fst a.snd

def W₂ : Type (max u v w) :=
  W fun a : I × Sigma α => β a.snd.fst a.snd.snd

variable {I α β}

def ξ : W₁ I α β → W₂ I α β :=
  W.rec fun ⟨i, a⟩ _t ξ_t => ⟨⟨i, i, a⟩, ξ_t⟩

def ϕ : W₂ I α β → I → W₂ I α β :=
  W.rec fun ⟨_, a⟩ _t ϕ_t i => ⟨⟨i, a⟩, fun b => ϕ_t b (s _ _ b)⟩

variable (I α β)

def V (i : I) : Type (max u v w) :=
  { t : W₁ I α β // ξ t = ϕ s (ξ t) i }

variable {I α β s}

def V.mk i a (t : ∀ b, V I α β s (s i a b)) : V I α β s i :=
  ⟨⟨⟨i, a⟩, fun b => (t b).val⟩, congrArg _ <| funext fun b => (t b).property⟩

def V.rec' {motive : ∀ i, V I α β s i → Type x} (mk : ∀ i a t, (∀ b, motive (s i a b) (t b)) → motive i (mk i a t)) {i} : ∀ t h, motive i ⟨t, h⟩
  | ⟨⟨i', a⟩, t⟩, h => by
    have := fun b => rec' mk (t b) (congrFun (eq_of_heq (W.mk.inj h).right) b)
    cases congrArg Prod.fst (W.mk.inj h).left
    exact mk i a _ this

def V.rec {motive : ∀ i, V I α β s i → Type x} (mk : ∀ i a t, (∀ b, motive (s i a b) (t b)) → motive i (mk i a t)) {i} : ∀ t, motive i t
  | ⟨t, h⟩ => rec' mk t h

end

def Vec (α : Type u) : ℕ → Type _ :=
  V ℕ (ℕ.rec PUnit fun _ _ => α) (ℕ.rec (fun _ => Empty) fun _ _ _ => Unit) (ℕ.rec nofun fun n _ _ _ => n)

def Vec.nil : Vec α .zero :=
  .mk ℕ.zero ⟨⟩ nofun

def Vec.cons (x : α) (xs : Vec α n) : Vec α n.succ :=
  .mk n.succ x fun _ => xs

def Vec.rec {motive : ∀ n, Vec α n → Type v} (nil : motive .zero nil) (cons : ∀ {n} x xs, motive n xs → motive n.succ (cons x xs)) : ∀ {n} xs, motive n xs :=
  V.rec (ℕ.rec (fun ⟨⟩ t _ => (funext nofun : t = nofun) ▸ nil) fun _ _ x t ht => cons x (t ()) (ht ()))
