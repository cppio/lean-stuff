def Var := Nat deriving DecidableEq

namespace Var

protected def toString (x : Var) : String :=
  ⟨toString x []⟩
where
  toString x l :=
    let l := Char.ofNat ('a'.toNat + x % 26) :: l
    match h : x / 26 with
    | 0 => l
    | q + 1 =>
      have := h ▸ Nat.div_le_self ..
      toString q l

instance instToString : ToString Var := ⟨Var.toString⟩

instance instOfNat : OfNat Var n := ⟨n⟩

def ofString : String → Var
  | ⟨l⟩ =>
    l.foldl (λ x c => (x + 1) * 26 + (c.toNat - 'a'.toNat) % 26) 0 - 26 ^ l.length

instance instCoeString : Coe String Var := ⟨ofString⟩

end Var
