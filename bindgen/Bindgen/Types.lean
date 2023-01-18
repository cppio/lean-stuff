@[extern c inline "#4"]
def seq {α : Sort u} {β : Sort v} (_ : @& α) (x : β) : β := x

structure Pointer where
  addr : USize

def Pointer.null : Pointer where
  addr := 0

instance : Inhabited Pointer where
  default := .null

def Pointer.toString (p : Pointer) : String :=
  hexRepr System.Platform.numBits p.addr
where
  hexRepr : Nat → USize → String
    | n + 4, x => hexRepr n (x / 16) ++ hexDigitRepr (x.toNat % 16)
    | _, _ => "0x"

instance : ToString Pointer where
  toString := Pointer.toString

@[never_extract, extern c inline "(size_t) #2"]
unsafe opaque Pointer.of {α : Sort u} : α → Pointer

@[never_extract, extern c inline "(lean_object *) #3"]
unsafe opaque Pointer.to {α : Sort u} [Nonempty α] : Pointer → α

@[never_extract, extern c inline "lean_apply_1(#2, lean_box_usize((size_t) lean_string_cstr(#3)))"]
unsafe opaque String.withCstr {α : Sort u} (f : Pointer → α) (s : @& String) : α := f .null

unsafe def String.withOptCstr {α : Sort u} (f : Pointer → α) (s? : Option String) : α :=
  match s? with
  | none => f .null
  | some s => s.withCstr f

@[never_extract, extern c inline "lean_mk_string((char const *) #1)"]
unsafe opaque String.fromNonNullCstr : Pointer → String

unsafe def String.fromCstr? : Pointer → Option String
  | .null => none
  | s => fromNonNullCstr s

unsafe def String.fromCstr! (s : Pointer) : String :=
  fromCstr? s |>.get!

-- TODO: Int32
