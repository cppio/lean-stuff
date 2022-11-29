import Lake
open Lake DSL

package common

@[default_target]
lean_lib Common

require std from git "https://github.com/leanprover/std4.git" @ "main"
require rec from "rec"
