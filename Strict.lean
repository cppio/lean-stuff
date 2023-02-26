import Mathlib.Logic.Function.Basic

unsafe inductive A
  | intro : ((A → Prop) → Prop) → A

unsafe def A.intro.inj : intro x = intro y → x = y :=
  @Eq.rec A (intro x) (rec λ y _ => x = y) rfl (intro y)

unsafe def f : (A → Prop) → A := (⟨Eq ·⟩)

unsafe def f.inj (h : f x = f y) : x = y :=
  congrFun (A.intro.inj h) y ▸ rfl

#check Function.cantor_injective f @f.inj
