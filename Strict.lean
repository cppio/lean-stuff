import Mathlib.Logic.Function.Basic

unsafe inductive A
  | intro : ((A → Prop) → Prop) → A

unsafe def A.intro.inj : intro x = intro y → x = y :=
  @Eq.rec A (intro x) (rec λ y _ => x = y) rfl (intro y)

unsafe def f (s : Set A) : A := ⟨Set.singleton s⟩

unsafe def f.inj (h : f x = f y) : x = y :=
  cast (congrFun (A.intro.inj h) x) rfl

unsafe def False.intro := Function.cantor_injective f @f.inj
