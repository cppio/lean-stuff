inductive Ordinal
  | zero : Ordinal
  | succ : Ordinal → Ordinal
  | limit : (Nat → Ordinal) → Ordinal

variable
  {motive : Ordinal → Sort u}
  (zero : motive .zero)
  (succ : (o : Ordinal) → motive o → motive (.succ o))
  (limit : (f : Nat → Ordinal) → ((n : Nat) → motive (f n)) → motive (.limit f))
in
def Ordinal.rec' : (o : Ordinal) → motive o
  | .zero => zero
  | .succ o => succ o (rec' o)
  | .limit f => limit f λ n => rec' (f n)

@[csimp]
def Ordinal.rec_eq_rec' : @rec = @rec' := by
  funext motive zero succ limit o
  induction o with
  | zero => rfl
  | succ o ho => exact congrArg _ ho
  | limit f hf => exact congrArg _ (funext hf)

#eval @Ordinal.rec (λ _ => Option Nat) (some .zero) (λ _ => Option.map .succ) (λ _ _ => none) (.succ <| .succ .zero)
