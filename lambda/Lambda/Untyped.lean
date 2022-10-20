import Lambda.Common

namespace Lambda.Untyped

inductive Term : Nat → Type
  | var (n : Fin2 f) : Term f
  | abs (M : Term f.succ) : Term f
  | app (M N : Term f) : Term f

namespace Term

private partial def reprVar' (x : Nat) (s : List Char) : List Char :=
  let (q, r) := (x / 26, x % 26)
  let s := Char.ofNat ('a'.toNat + r) :: s
  if q > 0
  then reprVar' (q - 1) s
  else s

private def reprVar (x : Nat) : String :=
  ⟨reprVar' x []⟩

protected def repr : Term f → String
  | var n => reprVar n.toNat
  | abs M => "(λ" ++ reprVar f ++ ". " ++ M.repr ++ ")"
  | app M N => "(" ++ M.repr ++ " " ++ N.repr ++ ")"

instance instRepr : Repr (Term f) where
  reprPrec M _ := M.repr

private def impl.liftVar : Nat → ∀ {f}, Fin2 f → Fin2 f.succ
  | .zero, _, n => .succ n
  | .succ _, _, .zero => .zero
  | .succ b, _, .succ n => .succ (liftVar b n)

@[implemented_by impl.liftVar]
protected def liftVar : Nat → ∀ {f}, Fin2 f → Fin2 f.succ :=
  @Nat.rec _
    @Fin2.succ
    (λ _ liftVar_b => @Fin2.rec _
      (λ {f} => @Fin2.zero f.succ)
      (λ {f} n _ => @Fin2.succ f.succ (liftVar_b n)))

private theorem liftVar.impl : ∀ b (n : Fin2 f), Term.liftVar b n = impl.liftVar b n
  | .zero, _ => rfl
  | .succ _, .zero => rfl
  | .succ b, .succ n => congrArg Fin2.succ (impl b n)

private theorem liftVar.le : ∀ {b n}, b ≤ n.toNat → @Term.liftVar b f n = n.succ
  | .zero, _, _ => rfl
  | .succ _, .succ _, h => congrArg Fin2.succ (le (Nat.pred_le_pred h))

private theorem liftVar.gt : ∀ {b n}, b > n.toNat → @Term.liftVar b f n = n.castSucc
  | .succ _, .zero, _ => rfl
  | .succ _, .succ _, h => congrArg Fin2.succ (gt (Nat.pred_le_pred h))

/-
private theorem liftVar.ne : ∀ {b n}, @Term.liftVar b.toNat f n ≠ b
  | .succ _, .succ _, h => ne (Fin2.succ.inj h)
-/

private theorem liftVar_liftVar_le : ∀ {b₁ b₂} {n : Fin2 f}, b₁ ≤ b₂ → Term.liftVar b₁ (Term.liftVar b₂ n) = Term.liftVar b₂.succ (Term.liftVar b₁ n)
  | .zero, _, _, _ => rfl
  | .succ _, .succ _, .zero, _ => rfl
  | .succ _, .succ _, .succ _, h => congrArg Fin2.succ (liftVar_liftVar_le (Nat.pred_le_pred h))

private theorem liftVar_liftVar_gt : ∀ {b₁ b₂} {n : Fin2 f}, b₁ > b₂ → Term.liftVar b₁ (Term.liftVar b₂ n) = Term.liftVar b₂ (Term.liftVar b₁.pred n)
  | .succ _, .zero, _, _ => rfl
  | .succ (.succ _), .succ _, .zero, _ => rfl
  | .succ (.succ _), .succ _, .succ _, h => congrArg Fin2.succ (liftVar_liftVar_gt (Nat.pred_le_pred h))

private def impl.lift' (b : Nat) {f} : Term f → Term f.succ
  | var n => var (Term.liftVar b n)
  | abs M => abs (lift' b M)
  | app M N => app (lift' b M) (lift' b N)

@[implemented_by impl.lift']
protected def lift' (b : Nat) : ∀ {f}, Term f → Term f.succ :=
  @Term.rec _
    (λ n => var (Term.liftVar b n))
    (λ {f} _ => @abs f.succ)
    (λ {f} _ _ => @app f.succ)

private theorem lift'.impl : (M : Term f) → Term.lift' b M = impl.lift' b M
  | var _ => rfl
  | abs M => congrArg abs (impl M)
  | app M N => congrArg₂ app (impl M) (impl N)

private theorem lift'_lift'_le (h : b₁ ≤ b₂) : (M : Term f) → Term.lift' b₁ (Term.lift' b₂ M) = Term.lift' b₂.succ (Term.lift' b₁ M)
  | var _ => congrArg var (liftVar_liftVar_le h)
  | abs M => congrArg abs (lift'_lift'_le h M)
  | app M N => congrArg₂ app (lift'_lift'_le h M) (lift'_lift'_le h N)

private theorem lift'_lift'_gt (h : b₁ > b₂) : (M : Term f) → Term.lift' b₁ (Term.lift' b₂ M) = Term.lift' b₂ (Term.lift' b₁.pred M)
  | var _ => congrArg var (liftVar_liftVar_gt h)
  | abs M => congrArg abs (lift'_lift'_gt h M)
  | app M N => congrArg₂ app (lift'_lift'_gt h M) (lift'_lift'_gt h N)

def lift : Term f → Term f.succ :=
  Term.lift' f

protected def substVar : Fin2 f → Fin2 f → Fin2 f
  | .zero, n => n
  | .succ .zero, .zero => .succ .zero
  | .succ (.succ _), .zero => .succ .zero
  | .succ .zero, .succ .zero => .zero
  | .succ .zero, .succ (.succ n) => n.succ.succ
  | .succ (.succ b), .succ n => match Term.substVar (.succ b) n with | .zero => .zero | n => .succ n

private theorem substVar.lt : ∀ b n, b.toNat < n.toNat → @Term.substVar f b n = n
  | .zero, _, _ => rfl
  | .succ .zero, .succ (.succ _), _ => rfl
  | .succ (.succ b), .succ (.succ n), h => by simp [Term.substVar, lt b.succ n.succ (Nat.pred_le_pred h)]

private theorem substVar.gt : ∀ b (n : Fin2 f), b.toNat > n.toNat → Term.substVar b n.castSucc = n.succ
  | .succ .zero, .zero, _ => rfl
  | .succ (.succ _), .zero, _ => rfl
  | .succ (.succ .zero), .succ .zero, _ => rfl
  | .succ (.succ (.succ _)), .succ .zero, _ => rfl
  | .succ (.succ b), .succ n, h => by
    have := gt b.succ n (Nat.pred_le_pred h)
    dsimp [Fin2.castSucc] at this
    simp [Term.substVar, this]

private theorem substVar.eq : {b : Fin2 (.succ f)} → Term.substVar b b = .zero
  | .zero => rfl
  | .succ .zero => rfl
  | .succ (.succ _) => by simp [Term.substVar, eq]

/-
@[implemented_by impl.substVar]
protected def substVar : ∀ {f}, Fin2 f → Fin2 f → Fin2 f :=
  @Fin2.rec _
    (λ n => n)
    (@Fin2.rec _
      (λ {f} substVar_zero => @Fin2.rec (λ _ _ => Fin2 f.succ.succ)
        (λ {_} => @Fin2.succ f.succ .zero)
        (λ {f'} n _ => @Fin2.rec _ sorry sorry _ (substVar_zero n))
        f.succ.succ)
      (λ {f} b _ substVar_succ_b => @Fin2.rec (λ _ _ => Fin2 f.succ.succ)
        (λ {_} => @Fin2.succ f.succ .zero)
        (λ {f'} n _ => sorry)
        f.succ.succ))
-/

private def impl.subst' : Term f → Fin2 f → Term f.pred → Term f.pred
  | var n, b, M' => match Term.substVar b n with | .zero => M' | .succ n => var n
  | abs M, .zero, M' => abs (subst' M .zero M'.lift)
  | abs M, .succ b, M' => abs (subst' M b.castSucc.succ M'.lift)
  | app M N, b, M' => app (subst' M b M') (subst' N b M')

@[implemented_by impl.subst']
protected def subst' : ∀ {f}, Term f → Fin2 f → Term f.pred → Term f.pred :=
  @Term.rec _
    (λ {f} n b M' => @Fin2.rec (λ f' _ => Term f'.pred → Term f'.pred)
      (λ M' => M')
      (λ {f'} n _ _ => @var f' n)
    f (Term.substVar b n) M')
    (λ {f} _ (subst'_M : Fin2 f.succ → Term f → Term f) b => @Fin2.rec (λ f' _ => (Fin2 f'.succ → Term f' → Term f') → Term f'.pred → Term f'.pred)
      (λ {f'} subst'_M (M' : Term f') => @abs f' (subst'_M (@Fin2.zero f'.succ) M'.lift))
      (λ {f'} b _ subst'_M (M' : Term f') => @abs f' (subst'_M b.castSucc.succ M'.lift))
    f b subst'_M)
    (λ _ _ subst'_M subst'_N M' b => app (subst'_M M' b) (subst'_N M' b))

private theorem subst'.impl : ∀ (M : Term f) (b : Fin2 f) (M' : Term f.pred), Term.subst' M b M' = impl.subst' M b M'
  | var n, b, M' => by dsimp [Term.subst', impl.subst']; cases Term.substVar b n; rfl; rfl
  | abs M, .zero, M' => congrArg abs (impl M .zero M'.lift)
  | abs M, .succ b, M' => congrArg abs (impl M b.castSucc.succ M'.lift)
  | app M N, b, M' => congrArg₂ app (impl M b M') (impl N b M')

def subst (M : Term f.succ) : Term f → Term f :=
  Term.subst' M .last

private theorem substVar_liftVar : (b : Fin2 f.succ) → (n : Fin2 f) → Term.substVar b (Term.liftVar b.toNat n) = n.succ
  | .zero, _ => rfl
  | .succ .zero, .zero => rfl
  | .succ (.succ _), .zero => rfl
  | .succ .zero, .succ _ => rfl
  | .succ (.succ b), .succ n => by
    show Term.substVar b.succ.succ (Term.liftVar b.succ.toNat n).succ = n.succ.succ
    dsimp only [Term.substVar]
    rw [substVar_liftVar b.succ n]

private theorem subst_lift' : ∀ (M : Term f) b, Term.subst' (Term.lift' b.toNat M) b M' = M
  | abs M, .zero => congrArg abs (subst_lift' M .zero)
  | abs M, .succ b => Fin2.toNat_castSucc ▸ congrArg abs (subst_lift' M b.castSucc.succ)
  | app M N, b => congrArg₂ app (subst_lift' M b) (subst_lift' N b)
  | var n, b => by
    show .subst' (var (Term.liftVar b.toNat n)) b M' = var n
    suffices Term.substVar b (Term.liftVar (Fin2.toNat b) n) = .succ n by
      simp [Term.subst', this]
    exact substVar_liftVar b n

theorem subst_lift : subst (lift M) M' = M := by
  have := Fin2.toNat_last ▸ @subst_lift' _ M' M .last
  exact this

private theorem lift_subst_le : ∀ (M : Term (.succ f)) {b₁} (b₂ : Fin2 f.succ), b₁.toNat ≤ b₂.toNat → (M.subst' b₁ M').lift' b₂.toNat = (M.lift' b₂.toNat.succ).subst' b₁.castSucc (M'.lift' b₂.toNat)
  | abs M, .zero, b₂, h => congrArg abs (lift'_lift'_le (Nat.pred_le_pred (Fin2.lt_toNat b₂)) M' ▸ Fin2.toNat_castSucc ▸ lift_subst_le M _ (Fin2.toNat_castSucc.symm ▸ h) : (M.subst' .zero (M'.lift' f)).lift' b₂.toNat = (M.lift' b₂.toNat.succ).subst' .zero ((M'.lift' b₂.toNat).lift' f.succ))
  | abs M, .succ b₁, b₂, h => congrArg abs (lift'_lift'_le (Nat.pred_le_pred (Fin2.lt_toNat b₂)) M' ▸ Fin2.toNat_castSucc ▸ lift_subst_le M _ (Fin2.toNat_castSucc.symm ▸ Fin2.castSucc_succ ▸ Fin2.toNat_castSucc.symm ▸ h) : (M.subst' b₁.castSucc.succ (M'.lift' f)).lift' b₂.toNat = (M.lift' b₂.toNat.succ).subst' b₁.castSucc.castSucc.succ ((M'.lift' b₂.toNat).lift' f.succ))
  | app M N, _, _, h => congrArg₂ app (lift_subst_le M _ h) (lift_subst_le N _ h)
  | var n, b₁, b₂, h => by
    simp only [subst'.impl, impl.subst']
    cases Nat.lt_or_eq_or_gt b₁.toNat n.toNat
    case inr h' =>
      cases h'
      case inr h' =>
        cases n.last_or_castSucc
        case inl hn =>
          simp [hn] at h'
          cases Nat.not_succ_le_self f (Nat.le_trans h' (Nat.pred_le_pred (Fin2.lt_toNat b₁)))
        case inr hn =>
          have ⟨n, hn⟩ := hn
          cases hn
          simp at h'
          simp [substVar.gt b₁ n h', Term.lift']
          cases n.toNat.lt_or_ge b₂.toNat
          case inl h₂ => simp [liftVar.gt h₂, liftVar.gt (Fin2.toNat_castSucc.symm ▸ Nat.lt.step h₂), @substVar.gt _ b₁.castSucc n.castSucc (Fin2.toNat_castSucc.symm ▸ Fin2.toNat_castSucc.symm ▸ h')]
          case inr h₂ =>
            simp [liftVar.le h₂]
            cases Nat.eq_or_lt_of_le h₂
            case inl h₂ =>
              rw [← h₂] at h'
              cases Nat.not_le_of_gt h' h
            case inr h₂ =>
              simp [@liftVar.le _ b₂.toNat.succ n.castSucc (Fin2.toNat_castSucc.symm ▸ h₂)]
              cases Nat.eq_or_lt_of_le h'
              case inr h' => simp [Fin2.castSucc_succ ▸ @substVar.gt _ b₁.castSucc n.succ (Fin2.toNat_castSucc.symm ▸ h')]
              case inl h' => cases Nat.not_succ_le_self _ (h'.symm ▸ Nat.le_trans h.step h₂)
      case inl h' =>
        simp at h'
        cases h'
        simp [substVar.eq, liftVar.gt (Nat.succ_le_succ h)]
    case inl h' =>
      cases n
      case zero => cases h'
      case succ n =>
        simp [substVar.lt b₁ n.succ h', Term.lift']
        cases n.toNat.lt_or_ge b₂.toNat
        case inl h₂ => simp [liftVar.gt h₂, @liftVar.gt _ _ n.succ (Nat.succ_le_succ h₂), Fin2.castSucc_succ ▸ @substVar.lt _ b₁.castSucc n.succ.castSucc (Fin2.toNat_castSucc.symm ▸ Fin2.toNat_castSucc.symm ▸ h')]
        case inr h₂ => simp [liftVar.le h₂, @liftVar.le _ _ n.succ (Nat.succ_le_succ h₂), @substVar.lt _ _ n.succ.succ (Fin2.toNat_castSucc.symm ▸ Nat.lt.step h')]

private theorem lift_subst_ge : ∀ (M : Term (.succ f)) {b₁}, b₁.toNat ≥ b₂ → (M.subst' b₁ M').lift' b₂ = (M.lift' b₂).subst' b₁.succ (M'.lift' b₂)
  | abs M, .zero, h => congrArg abs (lift'_lift'_le (Nat.le_trans h (Nat.zero_le f)) M' ▸ lift_subst_ge M h : (M.subst' .zero (M'.lift' f)).lift' b₂ = (M.lift' b₂).subst' (.succ .zero) ((M'.lift' b₂).lift' f.succ))
  | abs M, .succ b₁, h => congrArg abs (lift'_lift'_le (Nat.le_trans h (Fin2.lt_toNat b₁)) M' ▸ lift_subst_ge M (Fin2.castSucc_succ ▸ Fin2.toNat_castSucc.symm ▸ h) : (M.subst' b₁.castSucc.succ (M'.lift' f)).lift' b₂ = (M.lift' b₂).subst' b₁.castSucc.succ.succ ((M'.lift' b₂).lift' f.succ))
  | app M N, _, h => congrArg₂ app (lift_subst_ge M h) (lift_subst_ge N h)
  | var n, b₁, h => by
    simp only [subst'.impl, impl.subst']
    cases Nat.lt_or_eq_or_gt b₁.toNat n.toNat
    case inl h' =>
      cases n
      case zero => cases h'
      case succ n => simp [substVar.lt b₁ n.succ h', Term.lift', liftVar.le (Nat.le_trans h (Nat.pred_le_pred h')), liftVar.le (Nat.le_trans h (Nat.le_of_lt h')), substVar.lt b₁.succ n.succ.succ (Nat.succ_lt_succ h')]
    case inr h' =>
      cases h'
      case inr h' =>
        cases n.last_or_castSucc
        case inl hn =>
          simp [hn] at h'
          cases Nat.not_succ_le_self f (Nat.le_trans h' (Nat.pred_le_pred (Fin2.lt_toNat b₁)))
        case inr hn =>
          have ⟨n, hn⟩ := hn
          cases hn
          simp at h'
          simp [substVar.gt b₁ n h', Term.lift']
          cases n.toNat.lt_or_ge b₂
          case inl h₂ => simp [liftVar.gt h₂, liftVar.gt (Fin2.toNat_castSucc.symm ▸ h₂), @substVar.gt _ b₁.succ _ (Fin2.toNat_castSucc.symm ▸ Nat.lt.step h')]
          case inr h₂ => simp [liftVar.le h₂, liftVar.le (Fin2.toNat_castSucc.symm ▸ h₂), Fin2.castSucc_succ ▸ @substVar.gt f.succ b₁.succ n.succ (Nat.succ_le_succ h')]
      case inl h' =>
        simp at h'
        cases h'
        simp [substVar.eq, liftVar.le h]

theorem lift_subst (M : Term (.succ f)) (M') : (M.subst M').lift = (M.lift' f).subst M'.lift :=
  lift_subst_ge M (Fin2.toNat_last ▸ .refl)

theorem lift'_subst (M : Term (.succ f)) (M') (b : Fin2 f.succ) : (M.subst M').lift' b.toNat = (M.lift' b.toNat).subst (M'.lift' b.toNat) :=
  lift_subst_ge M (Fin2.toNat_last ▸ Nat.pred_le_pred (Fin2.lt_toNat b))

theorem lift_subst' (M : Term (.succ f)) (M' b) : (M.subst' b M').lift = M.lift.subst' b.castSucc M'.lift := by
  have := @lift_subst_le  _ M' M b (@Fin2.last f) (Fin2.toNat_last ▸ Nat.pred_le_pred (Fin2.lt_toNat b))
  rw [Fin2.toNat_last] at this
  exact this

theorem subst_subst_le : ∀ (M : Term (.succ (.succ f))) {b₁ b₂} (h : b₁.toNat ≤ b₂.toNat), (M.subst' b₁.castSucc N₁).subst' b₂ N₂ = (M.subst' b₂.succ (N₂.lift' b₁.toNat)).subst' b₁ (N₁.subst' b₂ N₂)
  | var _, _, _, _ => sorry
  | abs M, .zero, .zero, h => congrArg abs sorry
  | abs M, .zero, .succ b₂, h => congrArg abs sorry
  | abs M, .succ b₁, .succ b₂, h => congrArg abs sorry
  | app M N, _, _, h => congrArg₂ app (subst_subst_le M h) (subst_subst_le N h)

theorem subst_subst_gt : ∀ (M : Term (.succ (.succ f))) {b₁ b₂} (h : b₁.toNat > b₂.toNat), (M.subst' b₁.succ N₁).subst' b₂ N₂ = (M.subst' b₂.castSucc (N₂.lift' b₁.toNat)).subst' b₁ (N₁.subst' b₂ N₂)
  | abs M, .succ b₁, .zero, h => congrArg abs (lift_subst' N₁ N₂ .zero ▸ lift'_lift'_le (Fin2.lt_toNat b₁) N₂ ▸ Fin2.toNat_castSucc ▸ subst_subst_gt M (Fin2.toNat_castSucc.symm ▸ h : b₁.castSucc.toNat.succ > .zero) : (M.subst' b₁.castSucc.succ.succ N₁.lift).subst' .zero (N₂.lift' f) = (M.subst' .zero ((N₂.lift' b₁.toNat.succ).lift' f.succ)).subst' b₁.castSucc.succ ((N₁.subst' .zero N₂).lift))
  | abs M, .succ b₁, .succ b₂, h => congrArg abs (lift_subst' N₁ N₂ b₂.succ ▸ lift'_lift'_le (Fin2.lt_toNat b₁) N₂ ▸ Fin2.toNat_castSucc ▸ subst_subst_gt M (Fin2.toNat_castSucc.symm ▸ Fin2.toNat_castSucc.symm ▸ h : b₁.castSucc.toNat.succ > b₂.castSucc.toNat.succ) : (M.subst' b₁.castSucc.succ.succ N₁.lift).subst' b₂.castSucc.succ (N₂.lift' f) = (M.subst' b₂.castSucc.castSucc.succ ((N₂.lift' b₁.toNat.succ).lift' f.succ)).subst' b₁.castSucc.succ ((N₁.subst' b₂.succ N₂).lift))
  | app M N, _, _, h => congrArg₂ app (subst_subst_gt M h) (subst_subst_gt N h)
  | var n, b₁, b₂, h => by
    simp only [subst'.impl, impl.subst']
    cases Nat.lt_or_eq_or_gt b₁.succ.toNat n.toNat
    case inl h' =>
      simp [substVar.lt _ _ h', substVar.lt _ _ (Fin2.toNat_castSucc.symm ▸ Nat.lt_trans (.step h) h')]
      cases n
      case zero => cases h'
      case succ n =>
        simp [impl.subst', substVar.lt _ _ (Nat.lt_trans h (Nat.pred_le_pred h')), substVar.lt _ _ (Nat.pred_le_pred h')]
        cases n
        case zero => cases Nat.pred_le_pred h'
        case succ n => rfl
    case inr h' =>
      cases h'
      case inr h' =>
        cases n.last_or_castSucc
        case inl hn =>
          simp [hn] at h'
          cases Nat.not_succ_le_self _ (Nat.le_trans h' (Fin2.lt_toNat b₁))
        case inr hn =>
          have ⟨n, hn⟩ := hn
          cases hn
          simp at h'
          simp [substVar.gt b₁.succ n h']
          cases n.toNat.lt_or_eq_or_gt b₂.toNat
          case inl h₂ =>
            simp [substVar.gt b₂.castSucc n (Fin2.toNat_castSucc.symm ▸ h₂), impl.subst']
            cases n.last_or_castSucc
            case inl hn =>
              cases hn
              simp at h' h₂
              have : f ≤ b₁.toNat := Nat.pred_le_pred h'
              have : b₁.toNat ≤ f := Nat.pred_le_pred (Fin2.lt_toNat b₁)
              sorry
            case inr hn =>
              have ⟨n, hn⟩ := hn
              cases hn
              simp at h' h₂
              simp [substVar.gt b₂ n h₂]
              cases Nat.eq_or_lt_of_le h'
              case inl h₃ =>
                simp at h₃
                have := Fin2.toNat_castSucc.trans h₃
                rw [Fin2.toNat.injIff] at this
                cases this
                sorry
              case inr h₃ => simp [substVar.gt _ _ (Nat.pred_le_pred h₃)]
          case inr h₂ =>
            cases h₂
            case inr h₂ =>
              sorry
            case inl h₂ =>
              sorry
      case inl h' =>
        rw [Fin2.toNat.injIff] at h'
        cases h'
        simp [substVar.eq, substVar.lt b₂.castSucc b₁.succ (Fin2.toNat_castSucc.symm ▸ .step h), impl.subst']

end Term

section Congruence

variable (r : ∀ ⦃f⦄, Term f → Term f → Prop)

class Congruence : Prop :=
  abs : r M M' → r (.abs M) (.abs M')
  app₁ {M M'} : r M M' → r (.app M N) (.app M' N)
  app₂ {N N'} : r N N' → r (.app M N) (.app M N')

inductive CongruenceClosure : ∀ ⦃f⦄, Term f → Term f → Prop
  | base : r M N → CongruenceClosure M N
  | abs : CongruenceClosure M M' → CongruenceClosure (.abs M) (.abs M')
  | app₁ {M M'} : CongruenceClosure M M' → CongruenceClosure (.app M N) (.app M' N)
  | app₂ {N N'} : CongruenceClosure N N' → CongruenceClosure (.app M N) (.app M N')

instance CongruenceClosure.instCongruence : Congruence (CongruenceClosure r) where
  abs := @abs _
  app₁ := @app₁ _
  app₂ := @app₂ _

abbrev ReflexiveTransitiveCongruenceClosure ⦃f⦄ : Term f → Term f → Prop :=
  ReflexiveTransitiveClosure (@CongruenceClosure r f)

instance ReflexiveTransitiveCongruenceClosure.instCongruence : Congruence (ReflexiveTransitiveCongruenceClosure r) where
  abs {_} := @ReflexiveTransitiveClosure.rec _ _ _
    (λ h => .base (.abs h))
    .refl
    (λ _ _ => .trans)

  app₁ {_ _} := @ReflexiveTransitiveClosure.rec _ _ _
    (λ h => .base (.app₁ h))
    .refl
    (λ _ _ => .trans)

  app₂ {_ _} := @ReflexiveTransitiveClosure.rec _ _ _
    (λ h => .base (.app₂ h))
    .refl
    (λ _ _ => .trans)

abbrev EquivalenceCongruenceClosure ⦃f⦄ : Term f → Term f → Prop :=
  EquivalenceClosure (@CongruenceClosure r f)

instance EquivalenceCongruenceClosure.instCongruence : Congruence (EquivalenceCongruenceClosure r) where
  abs {_} := @EquivalenceClosure.rec _ _ _
    (λ h => .base (.abs h))
    .refl
    (λ _ => .symm)
    (λ _ _ => .trans)

  app₁ {_ _} := @EquivalenceClosure.rec _ _ _
    (λ h => .base (.app₁ h))
    .refl
    (λ _ => .symm)
    (λ _ _ => .trans)

  app₂ {_ _} := @EquivalenceClosure.rec _ _ _
    (λ h => .base (.app₂ h))
    .refl
    (λ _ => .symm)
    (λ _ _ => .trans)

variable {r} -- TODO: make these the definition and instances refer to these

def ReflexiveTransitiveCongruenceClosure.abs : ReflexiveTransitiveCongruenceClosure r M M' → ReflexiveTransitiveCongruenceClosure r (.abs M) (.abs M') :=
  Congruence.abs

def ReflexiveTransitiveCongruenceClosure.app₁ : ReflexiveTransitiveCongruenceClosure r M M' → ReflexiveTransitiveCongruenceClosure r (.app M N) (.app M' N) :=
  Congruence.app₁

def ReflexiveTransitiveCongruenceClosure.app₂ : ReflexiveTransitiveCongruenceClosure r N N' → ReflexiveTransitiveCongruenceClosure r (.app M N) (.app M N') :=
  Congruence.app₂

def EquivalenceCongruenceClosure.abs : EquivalenceCongruenceClosure r M M' → EquivalenceCongruenceClosure r (.abs M) (.abs M') :=
  Congruence.abs

def EquivalenceCongruenceClosure.app₁ : EquivalenceCongruenceClosure r M M' → EquivalenceCongruenceClosure r (.app M N) (.app M' N) :=
  Congruence.app₁

def EquivalenceCongruenceClosure.app₂ : EquivalenceCongruenceClosure r N N' → EquivalenceCongruenceClosure r (.app M N) (.app M N') :=
  Congruence.app₂

end Congruence

section Reduction

inductive BetaReduction : Term f → Term f → Prop
  | β : BetaReduction (.app (.abs M) N) (M.subst N)

abbrev SingleStepBetaReduction := CongruenceClosure @BetaReduction
abbrev MultiStepBetaReduction := ReflexiveTransitiveCongruenceClosure @BetaReduction
abbrev BetaEquivalent := EquivalenceCongruenceClosure @BetaReduction

infix:50 " →β " => SingleStepBetaReduction
infix:50 " ↠β " => MultiStepBetaReduction
infix:50 " =β " => BetaEquivalent

def BetaNormal (M : Term f) := ∀ M', ¬M →β M'

/-
inductive EtaReduction ⦃f⦄ : Term f → Term f → Prop
  | η : EtaReduction (.abs (.app M.lift (.var .zero))) M

abbrev SingleStepEtaReduction := @CongruenceClosure @EtaReduction
abbrev MultiStepEtaReduction := @ReflexiveTransitiveCongruenceClosure @EtaReduction
abbrev EtaEquivalent := @EquivalenceCongruenceClosure @EtaReduction

infix:50 " →η " => SingleStepEtaReduction
infix:50 " ↠η " => MultiStepEtaReduction
infix:50 " =η " => EtaEquivalent

def EtaNormal (M : Term f) := ∀ M', ¬M →η M'

inductive BetaEtaReduction : Term f → Term f → Prop
  | β : BetaReduction M N → BetaEtaReduction M N
  | η : EtaReduction M N → BetaEtaReduction M N

abbrev SingleStepBetaEtaReduction := @CongruenceClosure @BetaEtaReduction
abbrev MultiStepBetaEtaReduction := @ReflexiveTransitiveCongruenceClosure @BetaEtaReduction
abbrev BetaEtaEquivalent := @EquivalenceCongruenceClosure @BetaEtaReduction

infix:50 " →βη " => SingleStepBetaEtaReduction
infix:50 " ↠βη " => MultiStepBetaEtaReduction
infix:50 " =βη " => BetaEtaEquivalent

def BetaEtaNormal (M : Term f) := ∀ M', ¬M →βη M'
-/

end Reduction

namespace Confluence

inductive BetaParallel : Term f → Term f → Prop
  | β : BetaParallel M M' → BetaParallel N N' → BetaParallel (.app (.abs M) N) (M'.subst N')
  | var : BetaParallel (.var n) (.var n)
  | abs : BetaParallel M M' → BetaParallel (.abs M) (.abs M')
  | app : BetaParallel M M' → BetaParallel N N' → BetaParallel (.app M N) (.app M' N')

abbrev MultiBetaParallel {f} := ReflexiveTransitiveClosure (@BetaParallel f)

infix:50 " ▷β " => BetaParallel
infix:50 " ▷β* " => MultiBetaParallel

namespace BetaParallel

theorem refl : {M : Term f} → M ▷β M
  | .var _ => var
  | .abs _ => abs refl
  | .app _ _ => app refl refl

theorem red : M →β M' → M ▷β M'
  | .base .β => β refl refl
  | .abs h => abs (red h)
  | .app₁ h => app (red h) refl
  | .app₂ h => app refl (red h)

theorem red_t : M ▷β M' → M ↠β M'
  | β h₁ h₂ => .trans (.trans (Congruence.app₁ (Congruence.abs (red_t h₁))) (Congruence.app₂ (red_t h₂))) (.base (.base .β))
  | var => .refl
  | abs h => .abs (red_t h)
  | app h₁ h₂ => .trans (Congruence.app₁ (red_t h₁)) (Congruence.app₂ (red_t h₂))

theorem clos₁ : {M M' : Term f} → M ↠β M' → M ▷β* M' :=
  @ReflexiveTransitiveClosure.rec _ _ _
    (λ h => .base (red h))
    .refl
    (λ _ _ => .trans)

theorem clos₂ : {M M' : Term f} → M ▷β* M' → M ↠β M' :=
  @ReflexiveTransitiveClosure.rec _ _ _
    (λ h => red_t h)
    .refl
    (λ _ _ => .trans)

theorem lift {M M' : Term f} {b : Fin2 f.succ} : M ▷β M' → M.lift' b.toNat ▷β M'.lift' b.toNat
  | β h₁ h₂ => Term.lift'_subst _ _ b ▸ .β (Fin2.toNat_castSucc ▸ lift h₁) (lift h₂)
  | var => var
  | abs h => abs (Fin2.toNat_castSucc ▸ lift h)
  | app h₁ h₂ => app (lift h₁) (lift h₂)

theorem subst {M M' : Term (.succ f)} {N N' : Term f} (hN : N ▷β N') : M ▷β M' → ∀ {b}, M.subst' b N ▷β M'.subst' b N'
  | β _ _, .zero => (sorry : .app (.abs (.subst' _ .zero N.lift)) (.subst' _ .zero N) ▷β .subst' (.subst _ _) .zero N')
  | β _ _, .succ b => (sorry : .app (.abs (.subst' _ b.castSucc.succ N.lift)) (.subst' _ b.succ N) ▷β .subst' (.subst _ _) b.succ N')
  | @var _ n, b => by
    simp [Term.subst'.impl, Term.impl.subst']
    cases Term.substVar b n <;> simp
    case zero => exact hN
    case succ => exact var
  | abs h, .zero => abs (subst (by have := @lift _ _ _ (@Fin2.last f) hN; simp at this; exact this : N.lift' f ▷β N'.lift' f) h)
  | abs h, .succ b => abs (subst (by have := @lift _ _ _ (@Fin2.last f) hN; simp at this; exact this : N.lift ▷β N'.lift) h)
  | app h₁ h₂, _ => app (subst hN h₁) (subst hN h₂)

def maxBeta : Term f → Term f
  | .var n => .var n
  | .abs M => .abs (maxBeta M)
  | .app (.abs M) N => (maxBeta M).subst (maxBeta N)
  | .app M N => .app (maxBeta M) (maxBeta N)

theorem maxBeta.max : M ▷β M' → M' ▷β maxBeta M
  | .β h₁ h₂ => .subst (max h₂) (max h₁)
  | .var => .var
  | .abs h => .abs (max h)
  | .app h₁ h₂ =>
    match h₁ with
    | .β h₁ h₁' => .app (max (.β h₁ h₁')) (max h₂)
    | .var => .app (max .var) (max h₂)
    | .app h₁ h₁' => .app (max (.app h₁ h₁')) (max h₂)
    | .abs h₁ => .β (max h₁) (max h₂)

theorem diamond (h₁ : M ▷β N) (h₂ : M ▷β N') : ∃ M', N ▷β M' ∧ N' ▷β M' :=
  ⟨maxBeta M, maxBeta.max h₁, maxBeta.max h₂⟩

theorem diamond' : M ▷β* N → M ▷β* N' → ∃ M', N ▷β* M' ∧ N' ▷β* M'
  | h₁, .refl => ⟨N, .refl, h₁⟩
  | .refl, h₂ => ⟨N', h₂, .refl⟩
  | .base h₁, .base h₂ =>
    let ⟨M', hM, hM'⟩ := diamond h₁ h₂
    ⟨M', .base hM, .base hM'⟩
  | .base h₁, .trans h₂ h₂' =>
    let ⟨M₁, hM₁, hM₁'⟩ := diamond' (.base h₁) h₂
    let ⟨M₂, hM₂, hM₂'⟩ := diamond' hM₁' h₂'
    ⟨M₂, .trans hM₁ hM₂, hM₂'⟩
  | .trans h₁ h₁', .base h₂ =>
    let ⟨M₁, hM₁, hM₁'⟩ := diamond' h₁ (.base h₂)
    let ⟨M₂, hM₂, hM₂'⟩ := diamond' h₁' hM₁
    ⟨M₂, hM₂, .trans hM₁' hM₂'⟩
  | .trans h₁ h₁', .trans h₂ h₂' =>
    let ⟨M₁, hM₁, hM₁'⟩ := diamond' h₁ h₂
    let ⟨M₂, hM₂, hM₂'⟩ := diamond' (.trans h₁ h₁') (.trans h₁ hM₁)
    let ⟨M₃, hM₃, hM₃'⟩ := diamond' (.trans h₂ hM₁') (.trans h₂ h₂')
    let ⟨M₄, hM₄, hM₄'⟩ := diamond' (.trans (.trans h₁ h₁') hM₂) (.trans (.trans h₂ h₂') hM₃')
    ⟨M₄, .trans hM₂ hM₄, .trans hM₃' hM₄'⟩

end BetaParallel

theorem betaConfluence (h₁ : M ↠β N) (h₂ : M ↠β N') : ∃ M', N ↠β M' ∧ N' ↠β M' :=
  have clos {f} {M M' : Term f} := propext ⟨@BetaParallel.clos₁ f M M', @BetaParallel.clos₂ f M M'⟩
  let ⟨M', h₁', h₂'⟩ := BetaParallel.diamond' (clos ▸ h₁) (clos ▸ h₂)
  ⟨M', clos ▸ h₁', clos ▸ h₂'⟩

end Confluence

def Θ : Term .zero :=
  let A := .abs <| .abs <| .app (.var <| .succ .zero) (.app (.app (.var .zero) (.var .zero)) (.var <| .succ .zero))
  .app A A

example : .app Θ F ↠β .app F (.app Θ F) :=
  .trans (.base <| .app₁ <| .base .β) (.base <| .base .β)

def Y : Term .zero :=
  .abs <| .app (.abs <| .app (.var .zero) (.app (.var <| .succ .zero) (.var <| .succ .zero))) (.abs <| .app (.var .zero) (.app (.var <| .succ .zero) (.var <| .succ .zero)))

example : .app Y F =β .app F (.app Y F) :=
  let h' : .app Y F =β .app (F.lift.subst _) _ := .trans (.base <| .base .β) (.base <| .base .β)
  let h := by rw [Term.subst_lift] at h'; exact h'
  .trans h (.symm <| .base <| .app₂ <| .base .β)

example : BetaNormal (.abs (.var .zero) : Term .zero) :=
  λ _ h => nomatch h

end Lambda.Untyped

def Term' := ⦃α : Type⦄ → (α → α → α) → ((α → α) → α) → α

def Term'.parametric (f : Term') :=
  ∀ {α β} {g : α → β} {app₁ : α → α → α} {app₂ : β -> β -> β} {abs₁ : (α → α) → α} {abs₂ : (β → β) → β},
    (∀ x y, g (app₁ x y) = app₂ (g x) (g y)) →
      (∀ {f₁ f₂}, (∀ x, g (f₁ x) = f₂ (g x)) → g (abs₁ f₁) = abs₂ f₂) →
        g (f app₁ abs₁) = f app₂ abs₂

def Term := Subtype Term'.parametric

def Term'.app (f g : Term') : Term' :=
  λ α app abs => app (@f α app abs) (@g α app abs)

theorem Term'.parametric_app (hf : parametric f) (hg : parametric g) : parametric (app f g) :=
  λ happ habs => happ .. ▸ congrArg₂ _ (hf happ habs) (hg happ habs)

def Term.app (M N : Term) : Term :=
  ⟨Term'.app M.val N.val, Term'.parametric_app M.property N.property⟩

def FTerm' := ⦃α : Type⦄ → (α → α → α) → ((α → α) → α) → α → α

def Term'.abs (f : FTerm') : Term' :=
  λ α app abs => abs (@f α app abs)

def FTerm'.parametric (f : FTerm') :=
  ∀ {α β} {g : α → β} {app₁ : α → α → α} {app₂ : β -> β -> β} {abs₁ : (α → α) → α} {abs₂ : (β → β) → β},
    (∀ x y, g (app₁ x y) = app₂ (g x) (g y)) →
      (∀ {f₁ f₂}, (∀ x, g (f₁ x) = f₂ (g x)) → g (abs₁ f₁) = abs₂ f₂) →
        ∀ x, g (f app₁ abs₁ x) = f app₂ abs₂ (g x)

def FTerm := Subtype FTerm'.parametric

theorem Term'.parametric_abs (hf : FTerm'.parametric f) : parametric (abs f) :=
  λ happ habs => habs (hf happ habs)

def Term.abs (M : FTerm) : Term :=
  ⟨Term'.abs M.val, Term'.parametric_abs M.property⟩

inductive UTerm
  | var : UTerm
  | app : UTerm → UTerm → UTerm
  | abs : UTerm → UTerm

def Term.cases (M' : Term) : (Σ' M N, M' = app M N) ⊕ (Σ' M, M' = abs M) := by
  have ⟨M', h⟩ := M'
  cases h' : M' UTerm.app λ f => .abs (f .var)
  case var =>
    sorry
  case app M N =>
    apply Sum.inl
    sorry
  case abs M =>
    apply Sum.inr
    sorry

syntax "parametric" : tactic
macro_rules | `(tactic| parametric) => `(tactic| intro _ _ _ _ _ _ _ habs happ; dsimp [CoeFun.coe]; repeat (first | intro _ | rw [habs] | rw [happ] | congr))

def Term.mk
  (f : {α : Type} → [CoeFun α (λ _ => α → α)] → ((α → α) → α) → α)
  (h : Term'.parametric λ _ app => @f _ ⟨app⟩ := by parametric)
: Term :=
  ⟨_, h⟩

def FTerm.mk
  (f : {α : Type} → [CoeFun α (λ _ => α → α)] → ((α → α) → α) → α → α)
  (h : FTerm'.parametric λ _ app => @f _ ⟨app⟩ := by parametric)
: FTerm :=
  ⟨_, h⟩

def Y : Term := .mk λ abs =>
  abs λ f => (abs λ x => f (x x)) (abs λ x => f (x x))

def Y' : FTerm := .mk λ abs f =>
  (abs λ x => f (x x)) (abs λ x => f (x x))

private inductive NTerm
  | var : Nat → NTerm
  | app : NTerm → NTerm → NTerm
  | abs : Nat → NTerm → NTerm

def toNTerm' (n : Nat) (f : Term') : NTerm :=
  f .app λ g => .abs n (g (.var n))

#reduce toNTerm' 0 Y.1

-- private def repr' (n : Nat) : STerm → String

def repr' (h : Term) : False :=
  let ⟨h, _⟩ := h
  sorry

/-
inductive Term' (v : Type)
  | var : v → Term' v
  | abs' : (v → Term' v) → Term' v
  | app : Term' v → Term' v → Term' v

def Term'.abs (M : Term' v → Term' v) : Term' v := abs' (M ∘ var)

instance : CoeFun (Term' v) (λ _ => Term' v → Term' v) where
  coe := .app

def Term := ∀ {v}, Term' v

def repr' (n : Nat) : Term' String → String
  | .var x => x
  | .abs' M => let x := Lambda.Untyped.Term.reprVar n; "(λ" ++ x ++ ". " ++ repr' n.succ (M x) ++ ")"
  | .app M N => "(" ++ repr' n M ++ " " ++ repr' n N ++ ")"

instance : Repr Term where
  reprPrec M _ := repr' .zero M

open Term' (abs)

def Y : Term := abs λ f => (abs λ x => f (x x)) (abs λ x => f (x x))

#eval Lambda.Untyped.Y
#eval repr @Y         

def Θ : Term :=
  let A := abs λ f => abs λ g => g (f f g)
  A A

#eval Lambda.Untyped.Θ
#eval repr @Θ         

def Fin2.pred : Fin2 n → Option (Fin2 n.pred)
  | .zero => none
  | .succ i => some i

example : {i : Fin2 n} → Fin2.pred (Fin2.succ i) = some i
  | .zero => rfl
  | .succ _ => rfl

def Fin2.castPred : ∀ {n}, Fin2 n.succ → Option (Fin2 n)
  | .zero, .zero => none
  | .succ _, .zero => some .zero
  | .succ _, .succ i => do (← i.castPred).succ

example : ∀ {n} (i : Fin2 n), Fin2.castPred (Fin2.castSucc i) = some i
  | .succ _, .zero => rfl
  | .succ (.succ _), .succ i => by dsimp [Fin2.castPred]; rw [_example i]; rfl

def Option.mapOrElse (y : β) (f : α → β) : Option α → β
  | none => y
  | some x => f x

def conv₁' (xs : Fin2 f → v) : Lambda.Untyped.Term f → Term' v
  | .var x => .var (xs x)
  | .abs M => .abs' λ x => conv₁' (Option.mapOrElse x xs ∘ Fin2.castPred) M
  | .app M N => .app (conv₁' xs M) (conv₁' xs N)

def conv₁ (M : Lambda.Untyped.Term .zero) : Term :=
  conv₁' (λ i : Fin2 .zero => nomatch i) M

/-
def I : Term := abs λ x => x
def K : Term := abs λ x => abs λ _ => x
def S : Term := abs λ x => abs λ y => abs λ z => x z (y z)
-/

def T : Term := abs λ x => abs λ _ => x
def F : Term := abs λ _ => abs λ y => y

#eval @T
#eval (.abs (.abs (.var .zero)) : @Lambda.Untyped.Term .zero)

#eval @F
#eval (.abs (.abs (.var (.succ .zero))) : @Lambda.Untyped.Term .zero)

example : ∃ M : Term, M = Term'.var () := by
  let foo : Term :=
    λ {v} => have := Classical.propDecidable; if h : v = Unit then h ▸ .var () else abs id
  apply Exists.intro
  case w => exact foo
  simp

def conv₂' (M' : Term) : Term' Nat → Lambda.Untyped.Term f
  | .var x => (sorry : Nat → _) x
  | .abs' M => .abs (conv₂' (M f))
  | .app M N => .app (conv₂' M) (conv₂' N)

/-
def conv₂' : Term' (Fin2 f) → Lambda.Untyped.Term f
  | .var x => .var x
  | .abs' M => .abs (conv₂' sorry)
  | .app M N => .app (conv₂' M) (conv₂' N)
-/

def conv₂ (M : Term) : Lambda.Untyped.Term .zero :=
  conv₂' M

#reduce conv₂ T
#reduce conv₂ F

#check (Term'.abs id : Term' Nat)
#check Term'.var 1
-/
