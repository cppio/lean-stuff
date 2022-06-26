namespace Lambda.Untyped

inductive Term
  | var (x : Nat)
  | abs (M : Term)
  | app (M N : Term)

namespace Term

protected def repr : Term → String
  | var x => x.repr
  | abs M => "(λ " ++ Term.repr M ++ ")"
  | app M N => "(" ++ Term.repr M ++ " " ++ Term.repr N ++ ")"

instance instRepr : Repr Term where
  reprPrec M _ := M.repr

def shift' (n k : Nat) : Term → Term
  | var x => if n ≤ x then var (x + k) else var x
  | abs M => abs (shift' (n + 1) k M)
  | app M N => app (shift' n k M) (shift' n k N)

def shift : Nat → Term → Term :=
  shift' 0

def subst' (n : Nat) (N : Term) : Term → Term
  | var x => sorry
  | abs M => sorry
  | app M N => sorry

def subst : Term → Term → Term :=
  flip <| subst' 0

#eval abs <| abs <| var 1
#eval abs <| abs <| abs <| app (app (var 2) (var 0)) (app (var 1) (var 0))
 
def ex := app (abs <| abs <| app (app (var 3) (var 1)) <| abs <| app (var 0) <| var 2) <| abs <| app (var 4) <| var 0
#eval ex
#eval shift 100 ex


-- (λ (3 (λ (6 1))) (λ (1 (λ (7 1)))))
