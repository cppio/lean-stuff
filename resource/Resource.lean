private structure Resource.Sig where
  intro ::
  Resource : Type u → Type u
  mk : α → Resource α
  data : Resource α → α

private opaque Resource.Imp : Sig := {
  Resource := id
  mk := id
  data := id
}

variable (α : Type u)

def Resource : Type u := Resource.Imp.Resource α

variable {α}

@[never_extract, extern "lean_resource_mk"]
opaque Resource.mk {β : Sort v} (data : α) (finalizer : α → β) : Resource α := Resource.Imp.mk data

@[extern "lean_resource_data"]
opaque Resource.data (resource : @& Resource α) : α := Resource.Imp.data resource
