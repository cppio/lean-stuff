inductive nat'
| zero
| succ (n : nat')

example {m n} : nat'.succ m = nat'.succ n → m = n :=
@eq.rec nat' m.succ (@nat'.rec (λ _, Prop) false (λ n' _, m = n')) rfl n.succ

example (n) : nat'.succ n ≠ nat'.zero :=
@eq.rec nat' n.succ (@nat'.rec (λ _, Prop) false (λ _ _, true)) true.intro nat'.zero
