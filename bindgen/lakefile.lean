import Lake
open Lake DSL

package bindgen

@[default_target]
lean_lib Bindgen

lean_exe dlopen where
  root := `Dlopen
