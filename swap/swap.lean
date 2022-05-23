import rust

namespace rust

namespace swap

def map_zero_to_none (x : u128) : option u128 :=
  if x = 0
  then none
  else some x

structure swap_without_fees_result := (source_amount_swapped : u128) (destination_amount_swapped : u128)

end swap

end rust
