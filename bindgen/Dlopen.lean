import Bindgen

namespace System

extern "C" {
  void *dlopen(const char *file, int mode);
  void *dlsym(void *handle, const char *name);
  char *dlerror(void);
}

end System

private unsafe def dlerror : IO α := λ w =>
  .error (.userError <| .fromCstr! <| System.dlerror ()) w

private unsafe def dlsym (handle : Pointer) (name : String) : IO Pointer := λ w =>
  match name.withCstr <| System.dlsym handle with
  | .null => dlerror w
  | sym => .ok sym w

safe opaque dlopen (file : Option String) : IO (String → IO Pointer) := λ w =>
  match String.withOptCstr (System.dlopen · 0) file with
  | .null => dlerror w
  | handle => .ok (dlsym handle) w

@[never_extract, extern c inline "((double(*)(double)) #1)(#2)"]
unsafe opaque apply_f64_f64 : Pointer → Float → Float

safe extern "C" {
  double acos(double x);
}

def pi := acos (-1)

unsafe def main : IO Unit := do
  try
    _ ← dlopen "nonexistent"
  catch e =>
    IO.eprintln e
  let dlsym ← dlopen none
  try
    _ ← dlsym "nonexistent"
  catch e =>
    IO.eprintln e
  let sin ← dlsym "sin"
  IO.println s!"sin = {sin}"
  let sin := apply_f64_f64 sin
  IO.println s!"sin({pi}) = {sin pi}"
