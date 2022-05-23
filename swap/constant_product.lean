import swap

namespace rust

namespace swap

namespace constant_product

def swap
  (source_amount : u128)
  (swap_source_amount : u128)
  (swap_destination_amount : u128)
: option swap_without_fees_result := do
  invariant ← swap_source_amount.checked_mul swap_destination_amount,
  new_swap_source_amount ← swap_source_amount.checked_add source_amount,
  (new_swap_destination_amount, new_swap_source_amount) ← invariant.checked_ceil_div new_swap_source_amount,
  source_amount_swapped ← new_swap_source_amount.checked_sub swap_source_amount,
  destination_amount_swapped ← swap_destination_amount.checked_sub new_swap_destination_amount,
  destination_amount_swapped ← map_zero_to_none destination_amount_swapped,
  some ({
    source_amount_swapped := source_amount_swapped,
    destination_amount_swapped := destination_amount_swapped,
  })

end constant_product

end swap

end rust
