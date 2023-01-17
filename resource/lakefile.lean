import Lake
open Lake DSL

package resource

@[default_target]
lean_lib Resource

target resource.o pkg : FilePath := do
  let oFile := pkg.buildDir / "resource.o"
  let srcJob ← inputFile <| pkg.dir / "resource.c"
  let args := pkg.buildType.leancArgs.push "-FPIC"
  buildLeanO "resource.c" oFile srcJob args

extern_lib libresource pkg := do
  let libFile := pkg.libDir / nameToStaticLib "resource"
  let oFileJob ← fetch <| pkg.target ``resource.o
  buildStaticLib libFile #[oFileJob]

lean_exe dlopen where
  root := `Dlopen
