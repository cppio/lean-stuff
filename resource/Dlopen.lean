import Resource

namespace System

@[noinline, never_extract, extern "dlopen"] unsafe opaque dlopen (file : USize) (mode : UInt32) : USize
@[noinline, never_extract, extern "dlsym"] unsafe opaque dlsym (handle name : USize) : USize
@[noinline, never_extract, extern "dlclose"] unsafe opaque dlclose (handle : USize) : UInt32
@[noinline, never_extract, extern "dlerror"] unsafe opaque dlerror (void : Unit) : USize

@[noinline, never_extract, extern c inline "lean_mk_string((const char *) #1)"] unsafe opaque mkString (s : USize) : String
@[noinline, never_extract, extern c inline "(size_t) lean_string_cstr(#1)"] unsafe opaque cstr (o : String) : USize

end System

/-
macro_rules
  | `(unsafe opaque $name:ident $[($argName* : $argTy)]* : $ty := $val) =>
    let name' := Lean.mkIdent <| name.getId.str "_imp"
    `(private unsafe def $name' $[($argName* : $argTy)]* : $ty := $val
      @[implemented_by $name'] opaque $name $[($argName* : $argTy)]* : $ty)

unsafe opaque dlopen (file : USize) (mode : UInt32) : BaseIO USize := return System.dlopen file mode
unsafe opaque dlsym (handle name : USize) : BaseIO USize := return System.dlsym handle name
unsafe opaque dlclose (handle : USize) : BaseIO UInt32 := return System.dlclose handle
unsafe opaque dlerror (void : Unit) : BaseIO USize := return System.dlerror void

unsafe opaque Handle.error : BaseIO String := do
  let error ← dlerror ()
  return Lean.mkString error

def Handle.open (file : Option String) : IO Handle := do
  let file :=
    match file with
    | some file => Lean.cstr file
    | none => 0
  let handle ← dlopen file 0
  match handle.toNat with
  | 0 => throw <| .userError <| ← Handle.error
  | _ => return .mk handle
-/

structure Handle where
  intro ::
  handle : Resource USize

unsafe def Handle.openImp (file : String) : IO Handle := do
  let file := System.cstr file
  match System.dlopen file 4 with
  | 0 => throw <| .userError <| System.mkString <| System.dlerror ()
  | handle => return ⟨.mk handle System.dlclose⟩

@[implemented_by Handle.openImp]
opaque Handle.open (file : String) : IO Handle

def main : IO Unit := do
  let act : IO Unit := do
    let handle ← Handle.open "dylib.dylib"
    IO.println handle.handle.data
  act
  IO.println "sleeping..."
  IO.sleep 2000
  IO.println "done"
