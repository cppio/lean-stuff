namespace Lambda.Untyped

inductive Term
  | var (x : Nat)
  | abs (M : Term)
  | app (M N : Term)

namespace Term

protected def repr : Term → String
  | var x => x.repr
  | abs M => "(λ " ++ M.repr ++ ")"
  | app M N => "(" ++ M.repr ++ " " ++ N.repr ++ ")"

instance instRepr : Repr Term where
  reprPrec M _ := M.repr

def shift' (n k : Nat) : Term → Term
  | var x => if x ≥ n then var (x + k) else var x
  | abs M => abs (shift' n.succ k M)
  | app M N => app (shift' n k M) (shift' n k N)

def shift : Nat → Term → Term :=
  shift' 0

theorem shift_zero' : ∀ {M}, shift' n 0 M = M
  | var x => (if h : x ≥ n then if_pos h ▸ rfl else if_neg h ▸ rfl : (if x ≥ n then var x else var x) = var x)
  | abs _ => congrArg abs shift_zero'
  | app _ _ => (congr (congrArg app shift_zero') shift_zero' : app _ _ = app _ _)

theorem shift_zero : shift 0 M = M :=
  shift_zero'

def subst' (n : Nat) (N' : Term) : Term → Term
  | var x => if x = n then shift n N' else if x > n then var x.pred else var x
  | abs M => abs (subst' n.succ N' M)
  | app M N => app (subst' n N' M) (subst' n N' N)

def subst : Term → Term → Term :=
  flip <| subst' 0

inductive βred : Term → Term → Prop
  | β : βred (app (abs M) N) (subst M N)
  | app₁ : βred M M' → βred (app M N) (app M' N)
  | app₂ : βred N N' → βred (app M N) (app M N')
  | ξ : βred M M' → βred (abs M) (abs M')

inductive βred_t : Term → Term → Prop
  | refl : βred_t M M
  | trans : βred_t M N → βred_t N O → βred_t M O
  | β : βred M N → βred_t M N

inductive βeq : Term → Term → Prop
  | symm : βeq M N → βeq N M
  | trans : βeq M N → βeq N O → βeq M O
  | β : βred_t M N → βeq M N

infix:50 " →ᵦ " => βred
infix:50 " ↠ᵦ " => βred_t
infix:50 " =ᵦ " => βeq

def Y := abs <| app (abs <| app (var 1) (app (var 0) (var 0))) (abs <| app (var 1) (app (var 0) (var 0)))

def Θ :=
  let A := abs <| abs <| app (var 0) (app (app (var 1) (var 1)) (var 0))
  app A A

def βred.symm : βred M N → βeq N M :=
  βeq.symm ∘ βeq.β ∘ βred_t.β

def βred.trans (h₁ : βred M N) (h₂ : βred N O) : βred_t M O :=
  (βred_t.β h₁).trans (βred_t.β h₂)

example : app Θ F ↠ᵦ app F (app Θ F) :=
  βred.β.app₁.trans <| cast
    (shift_zero ▸ rfl : (_ →ᵦ app (shift 0 F) (app Θ (shift 0 F))) = (_ →ᵦ _))
    (βred.β : app (abs (app (var 0) (app Θ (var 0)))) F →ᵦ _)

example : app Y F =ᵦ app F (app Y F) :=
  (βeq.β <| (βred_t.β βred.β).trans <| βred_t.β (βred.β : app (abs <| app (shift 1 F) (app (var 0) (var 0))) (abs <| app (shift 1 F) (app (var 0) (var 0))) →ᵦ _) : app Y F =ᵦ app F (app (abs <| app (shift 1 F) (app (var 0) (var 0))) (abs <| app (shift 1 F) (app (var 0) (var 0))))).trans
  (βred.β.app₂ : app F (app Y F) →ᵦ app F (app (abs <| app (shift 1 F) (app (var 0) (var 0))) (abs <| app (shift 1 F) (app (var 0) (var 0))))).symm

section

instance : OfNat Term n where
  ofNat := var n

instance : CoeFun Term λ _ => Term → Term where
  coe := app

prefix:50 "λ. " => abs

def foo : Term := 2
def bar : Term := 3
#eval λ.λ.1
#eval λ.λ.λ.var 2 0 (var 1 0)

end

def beta : Term → Term
  | var x => var x
  | abs M => abs (beta M)
  | app (abs M) N => subst (beta M) (beta N)
  | app M N => app (beta M) (beta N)

def beta_normal : Term → Prop :=
  λ t => beta t = t

def dec (n : Nat) : Term → Option Term
  | var x => if x = n then none else if x > n then var x.pred else var x
  | abs M => abs <$> dec n.succ M
  | app M N => app <$> dec n M <*> dec n N

def eta : Term → Term
  | var x => var x
  | abs (app M (var 0)) => let M' := eta M; (dec 0 M').getD <| abs (app (eta M) (var 0))
  | abs M => abs (eta M)
  | app M N => app (eta M) (eta N)

def eta_normal : Term → Prop :=
  λ t => eta t = t

def K := abs <| abs <| var 1
def S := abs <| abs <| abs <| app (app (var 2) (var 0)) (app (var 1) (var 0))
def I := app (app S K) K

def ex := app (abs <| abs <| app (app (var 3) (var 1)) (abs <| app (var 0) (var 2))) (abs <| app (var 4) (var 0))
#eval ex
#eval shift 100 ex

#eval beta ex
--                  (λ ((2 (λ (5 0))) (λ (0 (λ (6 0))))))

def ω := abs (app (app (var 0) (var 0)) (var 0))
#eval app (abs <| var 1) (app ω ω)
#eval beta <| app (abs <| var 1) (app ω ω)
