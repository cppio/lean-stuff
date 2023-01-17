import Lake
open Lake DSL

package ipasir

lean_lib Ipasir

@[default_target]
lean_exe ipasir where
  root := `Main

require bindgen from "../bindgen"
require resource from "../resource"

extern_lib cadical pkg := inputFile <| pkg.dir / "libcadical.a"
