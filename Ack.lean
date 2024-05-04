def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

def ack' : Nat → Nat → Nat :=
  Nat.rec
    (fun n => n + 1)
    fun _m ack_m => Nat.rec
      (ack_m 1)
      fun _n ack_sm_n => ack_m ack_sm_n

def ack'' : Nat → Nat → Nat
  | 0 => fun n => n + 1
  | m + 1 =>
    let ack_m := ack'' m
    let rec ack_sm
      | 0 => ack_m 1
      | n + 1 => ack_m (ack_sm n)
    ack_sm

example : ack 0 n = n + 1 := rfl
example : ack (m + 1) 0 = ack m 1 := rfl
example : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := rfl

example : ack' 0 n = n + 1 := rfl
example : ack' (m + 1) 0 = ack' m 1 := rfl
example : ack' (m + 1) (n + 1) = ack' m (ack' (m + 1) n) := rfl

example : ack'' 0 n = n + 1 := rfl
example : ack'' (m + 1) 0 = ack'' m 1 := rfl
example : ack'' (m + 1) (n + 1) = ack'' m (ack'' (m + 1) n) := rfl
