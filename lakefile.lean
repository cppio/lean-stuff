import Lake
open Lake DSL

package common

@[default_target]
lean_lib Common

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
require rec from "rec"
