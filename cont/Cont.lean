axiom Cont.{u} (α : Type u) : Type u
@[never_extract, extern "Cont_callcc"] axiom Cont.callcc.{u} {α : Type u} (f : (k : Cont α) → α) : α
@[never_extract, extern "Cont_throw"] axiom Cont.throw.{u, v} {α : Type u} {β : Type v} (k : Cont α) (x : α) : β
