structure NatSig where
  Nat : Type
  «Nat.zero» : Nat
  «Nat.succ» (n : Nat) : Nat
  «Nat.rec» {motive : (t : Nat) → Sort u} (zero : motive «Nat.zero») (succ : ∀ n, (n_ih : motive n) → motive («Nat.succ» n)) t : motive t
  /-
  «Nat.rec_zero» {motive zero succ} : @«Nat.rec» motive zero succ «Nat.zero» = zero
  «Nat.rec_succ» {motive zero succ n} : @«Nat.rec» motive zero succ («Nat.succ» n) = succ n («Nat.rec» zero succ n)
  -/

def NatImp : NatSig where
  «Nat.rec» := @Nat.rec
  /-
  «Nat.rec_zero» := rfl
  «Nat.rec_succ» := rfl
  -/

opaque NatStruct : NatSig := NatImp

axiom NatStruct.Nat.{u} : NatStruct.{u}.Nat = NatStruct.{0}.Nat
axiom NatStruct.Nat.zero.{u} : cast Nat NatStruct.{u}.«Nat.zero» = NatStruct.{0}.«Nat.zero»
axiom NatStruct.Nat.succ.{u} n : cast Nat (NatStruct.{u}.«Nat.succ» n) = NatStruct.{0}.«Nat.succ» (cast Nat n)

def ℕ : Type := NatStruct.{0}.Nat
def ℕ.z : ℕ := NatStruct.«Nat.zero»
def ℕ.s : (n : ℕ) → ℕ := NatStruct.«Nat.succ»

def ℕ.rec {motive : (t : ℕ) → Sort u} (zero : motive z) (succ : ∀ n, (n_ih : motive n) → motive n.s) t : motive t :=
  cast (congrArg motive (by simp)) (NatStruct.«Nat.rec» (motive := fun t => motive (cast NatStruct.Nat t)) (cast (congrArg motive NatStruct.Nat.zero.symm) zero) (fun n n_ih => cast (congrArg motive (NatStruct.Nat.succ n).symm) (succ (cast NatStruct.Nat n) n_ih)) (cast NatStruct.Nat.symm t))

set_option pp.proofs.withType true

theorem ℕ.rec_zero : @rec motive zero succ z = zero :=
  by
    unfold rec
    simp [← NatStruct.Nat.zero]
    sorry

#check ℕ
#check ℕ.z
#check ℕ.s
#check ℕ.rec

structure StreamSig where
  Stream (α : Type u) : Type u
  «Stream.hd» {α} (s : Stream α) : α
  «Stream.tl» {α} (s : Stream α) : Stream α
  «Stream.gen» {α} {σ : Type v} (hd : (s : σ) → α) (tl : (s : σ) → σ) (s : σ) : Stream α
  «Stream.hd_gen» {α σ hd tl s} : «Stream.hd» (@«Stream.gen» α σ hd tl s) = hd s
  «Stream.tl_gen» {α σ hd tl s} : «Stream.tl» (@«Stream.gen» α σ hd tl s) = «Stream.gen» hd tl (tl s)

def StreamImp : StreamSig where
  Stream α := Nat → α
  «Stream.hd» s := s .zero
  «Stream.tl» s := s ∘ .succ
  «Stream.gen» hd tl s n := n.rec hd (fun _ s => s ∘ tl) s
  «Stream.hd_gen» := rfl
  «Stream.tl_gen» := rfl

opaque StreamStruct : StreamSig := StreamImp

def Stream' : (α : Type u) → Type u := StreamStruct.Stream.{u, 0}
def Stream'.hd : ∀ {α}, (s : Stream' α) → α := StreamStruct.«Stream.hd»
def Stream'.tl : ∀ {α}, (s : Stream' α) → Stream' α := StreamStruct.«Stream.tl»
def Stream'.gen : ∀ {α} {σ : Type v}, (hd : (s : σ) → α) → (tl : (s : σ) → σ) → (s : σ) → Stream' α := StreamStruct.«Stream.gen»

theorem Stream'.hd_gen : ∀ {α σ hd tl s}, (@gen α σ hd tl s).hd = hd s := StreamStruct.«Stream.hd_gen»
theorem Stream'.tl_gen : ∀ {α σ hd tl s}, (@gen α σ hd tl s).tl = gen hd tl (tl s) := StreamStruct.«Stream.tl_gen»

#check Stream'.gen
