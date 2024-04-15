import Lake
open Lake DSL

package cont

lean_lib Cont

lean_exe cont where
  root := `Main

target cont.o pkg : FilePath := do
  buildO "cont.c" (pkg.buildDir / "c" / "cont.o") (← inputFile <| pkg.dir / "cont.c") #["-I", (← getLeanIncludeDir).toString]

extern_lib libleancont pkg := do
  buildStaticLib (pkg.nativeLibDir / nameToStaticLib "leancont") #[← fetch <| pkg.target ``cont.o]
