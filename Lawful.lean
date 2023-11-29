def Functor' [Monad m] : Functor m :=
  @Functor.mk m
    (fun f x => do let a ← x; return f a)
    (fun a x => do _ ← x; return a)

def Pure' [Monad m] : Pure m :=
  @Pure.mk m
    (fun a => return a)

def Seq₁ [Monad m] : Seq m :=
  @Seq.mk m
    (fun x y => do let f ← x; let a ← y (); return f a)

def Seq₂ [Monad m] : Seq m :=
  @Seq.mk m
    (fun x y => do let a ← y (); let f ← x; return f a)

def SeqLeft₁ [Monad m] : SeqLeft m :=
  @SeqLeft.mk m
    (fun x y => do let a ← x; _ ← y (); return a)

def SeqLeft₂ [Monad m] : SeqLeft m :=
  @SeqLeft.mk m
    (fun x y => do _ ← y (); let a ← x; return a)

def SeqRight₁ [Monad m] : SeqRight m :=
  @SeqRight.mk m
    (fun x y => do _ ← x; let b ← y (); return b)

def SeqRight₂ [Monad m] : SeqRight m :=
  @SeqRight.mk m
    (fun x y => do let b ← y (); _ ← x; return b)

def Applicative₁ [Monad m] : Applicative m :=
  @Applicative.mk m Functor' Pure' Seq₁ SeqLeft₁ SeqRight₁

def Applicative₂ [Monad m] : Applicative m :=
  @Applicative.mk m Functor' Pure' Seq₂ SeqLeft₂ SeqRight₂

instance [Monad m] [LawfulMonad m] : @LawfulFunctor m Functor' := by
  apply @LawfulFunctor.mk m Functor' <;> intros <;> funext <;> simp [Functor']

instance [Monad m] [LawfulMonad m] : @LawfulApplicative m Applicative₁ := by
  apply @LawfulApplicative.mk m Applicative₁ <;> simp [Functor', Seq₁, SeqLeft₁, SeqRight₁, Applicative₁]

instance [Monad m] [LawfulMonad m] : @LawfulApplicative m Applicative₂ := by
  apply @LawfulApplicative.mk m Applicative₂ <;> simp [Functor', Seq₂, SeqLeft₂, SeqRight₂, Applicative₂]
