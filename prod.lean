universes u v

structure prod₁ (α : Type u) (β : Type v) :=
(fst : α) (snd : β)

inductive prod₂ (α : Type u) (β : Type v)
| mk : α → β → prod₂

set_option eqn_compiler.lemmas false

@[reducible]
def prod₂.fst : Π {α : Type u} {β : Type v}, prod₂.{u v} α β → α :=
λ (α : Type u) (β : Type v),
  @prod₂.rec.{u+1 u v} α β (λ (self : prod₂.{u v} α β), α) (λ (fst : α) (snd : β), fst)

@[reducible]
def prod₂.snd : Π {α : Type u} {β : Type v}, prod₂.{u v} α β → β :=
λ (α : Type u) (β : Type v),
  @prod₂.rec.{v+1 u v} α β (λ (self : prod₂.{u v} α β), β) (λ (fst : α) (snd : β), snd)

set_option pp.all true

#print prod₁.fst
#print prod₂.fst
#print prod₁.snd
#print prod₂.snd
