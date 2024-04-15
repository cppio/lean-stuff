import Mathlib.Data.Nat.Basic

-- TODO: optmized repr as lazy thunk

class MonadFix (M : Type u → Type V) where
  fix : ((α → M β) → α → M β) → α → M β

def DelayM (α : Type u) : Type u := { f : Nat → Option α // ∀ n a, f n = some a → f n.succ = some a }

def DelayM.loop : DelayM α := ⟨fun _ => none, fun _ _ => id⟩
def DelayM.withDelay (a : α) (d : Nat) : DelayM α := ⟨fun n => if n < d then none else some a, fun n b h => by dsimp at h ⊢; split at h <;> cases h; split; apply ‹¬n < d›; apply Nat.lt_of_succ_lt; assumption; rfl⟩

instance : Pure DelayM where
  pure a := ⟨fun _ => some a, fun _ _ => id⟩

instance : Bind DelayM where
  bind x f := ⟨fun n => x.val n >>= fun a => f a |>.val n, fun n b h => by cases xn : x.val n with | none => simp [xn, bind] at h | some a => simp [xn, bind] at h; dsimp; rw [x.property n a xn]; simp [bind]; rw [(f a).property n b]; exact h⟩

instance : Monad DelayM where

instance : LawfulMonad DelayM where
  map_const := rfl
  id_map _ := by simp [Functor.map, pure, bind]
  seqLeft_eq _ _ := by
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, bind, Option.bind]
    congr
    funext
    split <;> simp [*]
  seqRight_eq _ _ := by
    simp [SeqRight.seqRight, Seq.seq, Functor.map, pure, bind, Option.bind]
    congr
    funext
    split <;> simp [*]
    split <;> simp [*]
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc x _ _ := by
    simp [bind, Option.bind]
    congr
    funext n
    cases xn : x.val n <;> simp [xn]

def DelayM.nonloop (eq : x.val n = some a) : { d // x = withDelay a d } := by
  cases x with | _ f p =>
  dsimp at eq
  induction n with
  | zero =>
    apply Subtype.mk 0
    congr
    funext n
    induction n with
    | zero => exact eq
    | succ n ih => exact p _ _ ih
  | succ n ih =>
    cases fn : f n with
    | none =>
      apply Subtype.mk n.succ
      congr
      funext m
      split
      case _ h =>
        clear eq ih
        cases Nat.exists_eq_add_of_lt h with | _ n eq =>
        clear h
        simp at eq
        cases eq
        induction n with
        | zero => exact fn
        | succ n ih =>
          apply ih
          cases fmn : f (m + n) with
          | none => rfl
          | some b => exact p _ _ fmn |>.symm |>.trans fn
      case _ h =>
        cases Nat.exists_eq_add_of_le <| Nat.ge_of_not_lt h with | _ m eq =>
        clear h
        cases eq
        induction m with
        | zero => exact eq
        | succ m ih => exact p _ _ ih
    | some b =>
      cases p _ _ fn |>.symm |>.trans eq
      exact ih fn

inductive Same : (f g : Nat → Option α) → Prop
  | same : f .zero = none → Same f (f ∘ .succ)

def NontermM (α : Type u) : Type u := Quot fun (x y : DelayM α) => Same x.val y.val
def NontermM.loop : NontermM α := .mk _ .loop

instance : Pure NontermM where
  pure a := .mk _ (Pure.pure a)

theorem NontermM.withDelay : .mk _ (.withDelay a d) = (pure a : NontermM _) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    apply Eq.trans _ ih
    clear ih
    apply Quot.sound
    have := Same.same (f := DelayM.withDelay a (Nat.succ d) |>.val) (by simp [DelayM.withDelay])
    apply Eq.mp ?_ this
    congr
    funext n
    simp [DelayM.withDelay]
    split
    case _ h => simp [Nat.lt_of_succ_lt_succ h]
    case _ h => simp [show ¬n < d from h ∘ Nat.succ_lt_succ]

theorem NontermM.lemma (eq : x.val n = some a) : .mk _ x = (pure a : NontermM _) := by
  cases DelayM.nonloop eq with | _ d eq =>
  cases eq
  exact withDelay

theorem NontermM.char (x : NontermM α) : x = loop ∨ ∃ a, x = pure a := by
  by_cases h : ∃ a, x = pure a <;> simp [h]
  induction x using Quot.ind with | _ x =>
  cases x with | _ f p =>
  simp [loop]
  congr
  funext n
  cases fn : f n with
  | none => rfl
  | some a => cases h ⟨a, NontermM.lemma (x := ⟨f, p⟩) fn⟩

instance : Bind NontermM where
  bind x f := x.lift (fun x => .mk _ ⟨fun n => x.val n >>= fun a => (f a).lift (·.val n) sorry, sorry⟩) sorry

#check inferInstanceAs (Monad NontermM)
#check inferInstanceAs (LawfulMonad NontermM)

def fix (f : (α → NontermM β) → α → NontermM β) (x : α) : NontermM β := sorry

def log2p1 [Monad M] [MonadFix M] : Nat → M Nat :=
  MonadFix.fix fun log2p1 => fun
    | 0 => return 0
    | n => return (← log2p1 (n / 2)) + 1

#eval log2p1 (M := ReaderT Nat Option) 32 7


def DelayM.fix' (f : (α → Nat → Option β) → α → Nat → Option β) (x : α) : Nat → Option β
  | .zero => none
  | .succ n => f (fun y _ => fix' f y n) x n

instance : MonadFix (ReaderT Nat Option) where
  fix := DelayM.fix'

instance : MonadFix (OptionT (ReaderM Nat)) where
  fix := DelayM.fix'

def DelayM.fix'' (f : (α → DelayM β) → α → DelayM β) (x : α) : Nat → Option β
  | .zero => none
  | .succ n => f (fun y => ⟨fun _ => fix'' f y n, fun _ _ => id⟩) x |>.val n

def DelayM.fix (f : (α → DelayM β) → α → DelayM β) (x : α) : DelayM β := by
  apply Subtype.mk (fix'' f x)
  intro n b eq
  simp [fix'']
  cases n with
  | zero => simp [fix''] at eq
  | succ n =>
  simp [fix''] at eq
  sorry
