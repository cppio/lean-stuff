namespace Logic.Propositional.Linear.Intuitionistic

opaque BasePropn : Type

inductive Propn
  | base (P : BasePropn)
  | one
  | zero
  | top
  | tensor (A B : Propn)
  | plus (A B : Propn)
  | with (A B : Propn)
  | lolli (A B : Propn)

inductive Ctx
  | nil
  | cons (Γ : Ctx) (A : Propn)

def Ctx.append (Γ : Ctx) : (Γ' : Ctx) → Ctx
  | nil => Γ
  | cons Γ' A => (Γ.append Γ').cons A

theorem Ctx.nil_append : ∀ {Γ}, nil.append Γ = Γ
  | nil => rfl
  | cons .. => congrArg (cons · _) nil_append

theorem Ctx.append_append : ∀ {Γ''}, append Γ (append Γ' Γ'') = append (append Γ Γ') Γ''
  | nil => rfl
  | cons .. => congrArg (cons · _) append_append

inductive Mem (A : Propn) : (Γ : Ctx) → Type
  | here : Mem A (.cons Γ A)
  | there (u : Mem A Γ) : Mem A (Γ.cons B)

def Ctx.del : ∀ {Γ}, (u : Mem A Γ) → Ctx
  | cons Γ _, .here => Γ
  | cons Γ A, .there u => (Γ.del u).cons A

def Mem.ofMemDel : {u : Mem B Γ} → (v : Mem A (Γ.del u)) → Mem A Γ
  | here, v => there v
  | there (B := .(A)) (Γ := Γ) u, here => here
  | there (B := C) (Γ := Γ) u, there v => (ofMemDel v).there

def Mem.del : (u : Mem A Γ) → (v : Mem B (Γ.del u)) → Mem A (Γ.del (ofMemDel v))
  | here, _ => here
  | there (B := .(B)) (Γ := Γ) u, here => u
  | there (B := C) (Γ := Γ) u, there v => (u.del v).there

theorem Ctx.del_del : {u : Mem A Γ} → (v : Mem B (Γ.del u)) → (Γ.del u).del v = (Γ.del (.ofMemDel v)).del (u.del v)
  | .here, _ => rfl
  | .there (B := .(B)) (Γ := Γ) u, .here => rfl
  | .there (B := C) (Γ := Γ) u, .there v => congrArg (cons · C) (del_del v)

inductive Rename : (Γ Γ' : Ctx) → Type
  | nil : Rename .nil .nil
  | cons (u : Mem A Γ') (γ : Rename Γ (Γ'.del u)) : Rename (Γ.cons A) Γ'

def Rename.cons' (γ : Rename Γ Γ') {A} : Rename (Γ.cons A) (Γ'.cons A) :=
  cons .here γ

def Rename.consAppend : ∀ {Γ₂}, (γ : Rename (.append Γ₁ Γ₂) Γ') → Rename ((Γ₁.cons A).append Γ₂) (Γ'.cons A)
  | .nil, γ => γ.cons'
  | .cons .., cons u γ => cons u.there γ.consAppend

def Rename.append (γ : Rename (.append Γ₁ Γ₂) Γ') : ∀ {Γ}, Rename ((Γ₁.append Γ).append Γ₂) (Γ'.append Γ)
  | .nil => γ
  | .cons .. => γ.append.consAppend

def Rename.id : ∀ {Γ}, Rename Γ Γ
  | .nil => nil
  | .cons .. => id.cons'

def Rename.exchange : Rename (Ctx.cons Γ A |>.cons B) (Γ.cons B |>.cons A) :=
  cons (.there .here) id

def Rename.exchange₂ : Rename (Ctx.cons Γ A |>.cons B |>.cons C) (Γ.cons B |>.cons C |>.cons A) :=
  cons (.there .here) (cons (.there .here) id)

def Rename.appendSwap : ∀ {Γ₁}, Rename (.append Γ₁ Γ₂) (Γ₂.append Γ₁)
  | .nil => Ctx.nil_append ▸ .id
  | .cons .. => consAppend appendSwap

def Mem.rename : (γ : Rename Γ Γ') → ∀ {A}, (u : Mem A Γ) → Mem A Γ'
  | .cons u _, _, here => u
  | .cons _ γ, _, there u => ofMemDel (u.rename γ)

def Rename.del : (γ : Rename Γ Γ') → ∀ {A}, (u : Mem A Γ) → Rename (Γ.del u) (Γ'.del (u.rename γ))
  | cons _ γ, _, .here => γ
  | cons u' γ, _, .there u => cons (u'.del (u.rename γ)) (Ctx.del_del (u.rename γ) ▸ γ.del u)

def Rename.comp : (γ : Rename Γ Γ') → (γ' : Rename Γ' Γ'') → Rename Γ Γ''
  | nil, γ' => γ'
  | cons u γ, γ' => cons (u.rename γ') (γ.comp (γ'.del u))

inductive Split : (Γ Γ₁ Γ₂ : Ctx) → Type
  | nil : Split .nil .nil .nil
  | cons₁ (h : Split Γ Γ₁ Γ₂) : Split (Γ.cons A) (Γ₁.cons A) Γ₂
  | cons₂ (h : Split Γ Γ₁ Γ₂) : Split (Γ.cons A) Γ₁ (Γ₂.cons A)

def Split.triv₁ : ∀ {Γ}, Split Γ Γ .nil
  | .nil => nil
  | .cons .. => triv₁.cons₁

def Split.triv₂ : ∀ {Γ}, Split Γ .nil Γ
  | .nil => nil
  | .cons .. => triv₂.cons₂

theorem Split.eq_triv₁ : ∀ h, (⟨Γ₁, h⟩ : Σ Γ₁, Split Γ Γ₁ _) = ⟨Γ, .triv₁⟩
  | nil => rfl
  | cons₁ h => match h.eq_triv₁ with | rfl => rfl

theorem Split.eq_triv₂ : ∀ h, (⟨Γ₂, h⟩ : Σ Γ₂, Split Γ _ Γ₂) = ⟨Γ, .triv₂⟩
  | nil => rfl
  | cons₂ h => match h.eq_triv₂ with | rfl => rfl

def Split.flip : (h : Split Γ Γ₁ Γ₂) → Split Γ Γ₂ Γ₁
  | nil => nil
  | cons₁ h => h.flip.cons₂
  | cons₂ h => h.flip.cons₁

def Split.shift₁ : (h : Split Γ Γ₁ Γ₂) → (h₁ : Split Γ₁ Γ₁₁ Γ₁₂) → Σ Γ', Split Γ Γ₁₁ Γ' × Split Γ' Γ₁₂ Γ₂
  | h, nil => ⟨Γ, triv₂, h⟩
  | cons₁ h, cons₁ h₁ => let ⟨Γ', h', h''⟩ := h.shift₁ h₁; ⟨Γ', h'.cons₁, h''⟩
  | cons₁ h, cons₂ h₁ => let ⟨Γ', h', h''⟩ := h.shift₁ h₁; ⟨Γ'.cons _, h'.cons₂, h''.cons₁⟩
  | cons₂ h, h₁ => let ⟨Γ', h', h''⟩ := h.shift₁ h₁; ⟨Γ'.cons _, h'.cons₂, h''.cons₂⟩

def Split.shift₂ : (h : Split Γ Γ₁ Γ₂) → (h₂ : Split Γ₂ Γ₂₁ Γ₂₂) → Σ Γ', Split Γ Γ' Γ₂₂ × Split Γ' Γ₁ Γ₂₁
  | h, nil => ⟨Γ, triv₁, h⟩
  | cons₂ h, cons₁ h₂ => let ⟨Γ', h', h''⟩ := h.shift₂ h₂; ⟨Γ'.cons _, h'.cons₁, h''.cons₂⟩
  | cons₂ h, cons₂ h₂ => let ⟨Γ', h', h''⟩ := h.shift₂ h₂; ⟨Γ', h'.cons₂, h''⟩
  | cons₁ h, h₂ => let ⟨Γ', h', h''⟩ := h.shift₂ h₂; ⟨Γ'.cons _, h'.cons₁, h''.cons₁⟩

def Split.ofMem : (u : Mem A Γ) → Split Γ (.cons .nil A) (Γ.del u)
  | .here => triv₂.cons₁
  | .there u => (ofMem u).cons₂

def Split.rename : (h : Split Γ Γ₁ Γ₂) → Rename (Γ₁.append Γ₂) Γ
  | nil => .nil
  | cons₁ h => h.rename.consAppend
  | cons₂ h => .cons .here h.rename

def Rename.split : (γ : Rename Γ Γ') → ∀ {Γ₁ Γ₂}, (h : Split Γ Γ₁ Γ₂) → Σ Γ₁' Γ₂', Rename Γ₁ Γ₁' × Rename Γ₂ Γ₂' × Split Γ' Γ₁' Γ₂'
  | nil, _, _, .nil => ⟨.nil, .nil, nil, nil, .nil⟩
  | cons u γ, _, _, .cons₁ h => let ⟨_, Γ₂', γ₁, γ₂, h⟩ := γ.split h; let ⟨Γ₁', h, h'⟩ := (Split.ofMem u).shift₂ h; ⟨Γ₁', Γ₂', γ₁.cons'.comp h'.flip.rename, γ₂, h⟩
  | cons u γ, _, _, .cons₂ h => let ⟨Γ₁', _, γ₁, γ₂, h⟩ := γ.split h; let ⟨Γ₂', h, h'⟩ := (Split.ofMem u).flip.shift₁ h; ⟨Γ₁', Γ₂', γ₁, γ₂.cons'.comp h'.rename, h⟩

def Mem.ofSplit₁ : (u : Mem A Γ₁) → (h : Split Γ Γ₁ Γ₂) → Mem A Γ
  | here, .cons₁ _ => here
  | there u, .cons₁ h | u, .cons₂ h => (u.ofSplit₁ h).there

def Mem.ofSplit₂ : (u : Mem A Γ₂) → (h : Split Γ Γ₁ Γ₂) → Mem A Γ
  | here, .cons₂ h => here
  | there u, .cons₂ h | u, .cons₁ h => (u.ofSplit₂ h).there

def Split.del₁ : (u : Mem A Γ₁) → (h : Split Γ Γ₁ Γ₂) → Split (Γ.del (u.ofSplit₁ h)) (Γ₁.del u) Γ₂
  | .here, cons₁ h => h
  | .there u, cons₁ h => (h.del₁ u).cons₁
  | .here, cons₂ h | .there _, cons₂ h => (h.del₁ _).cons₂

def Split.del₂ : (u : Mem A Γ₂) → (h : Split Γ Γ₁ Γ₂) → Split (Γ.del (u.ofSplit₂ h)) Γ₁ (Γ₂.del u)
  | .here, cons₂ h => h
  | .there u, cons₂ h => (h.del₂ u).cons₂
  | .here, cons₁ h | .there _, cons₁ h => (h.del₂ _).cons₁

def Split.append : ∀ {Γ₂}, Split (Γ₁.append Γ₂) Γ₁ Γ₂
  | .nil => triv₁
  | .cons .. => append.cons₂

class Judge (J : (Γ : Ctx) → (A : Propn) → Type) where
  hyp : J (.cons .nil A) A

inductive Subst (J : (Γ : Ctx) → (A : Propn) → Type) : (Γ Γ' : Ctx) → Type
  | nil : Subst J .nil .nil
  | cons (h : Split Γ' Γ₁ Γ₂) (D : J Γ₁ A) (γ : Subst J Γ Γ₂) : Subst J (Γ.cons A) Γ'

def Subst.cons' [Judge J] : (γ : Subst J Γ Γ') → Subst J (Γ.cons A) (Γ'.cons A) :=
  cons (.cons₁ .triv₂) Judge.hyp

def Subst.id [Judge J] : ∀ {Γ}, Subst J Γ Γ
  | .nil => nil
  | .cons .. => id.cons'

def Subst.split : (γ : Subst J Γ Γ') → ∀ {Γ₁ Γ₂}, (h : Split Γ Γ₁ Γ₂) → Σ Γ₁' Γ₂', Subst J Γ₁ Γ₁' × Subst J Γ₂ Γ₂' × Split Γ' Γ₁' Γ₂'
  | nil, _, _, .nil => ⟨.nil, .nil, nil, nil, .nil⟩
  | cons h' D γ, _, _, .cons₁ h => let ⟨_, Γ₂', γ₁, γ₂, h⟩ := γ.split h; let ⟨Γ₁', h, h'⟩ := h'.shift₂ h; ⟨Γ₁', Γ₂', cons h' D γ₁, γ₂, h⟩
  | cons h' D γ, _, _, .cons₂ h => let ⟨Γ₁', _, γ₁, γ₂, h⟩ := γ.split h; let ⟨Γ₂', h, h'⟩ := h'.flip.shift₁ h; ⟨Γ₁', Γ₂', γ₁, cons h'.flip D γ₂, h⟩

def Subst.map (f : ∀ {Γ A}, J Γ A → J' Γ A) {Γ Γ'} : (γ : Subst J Γ Γ') → Subst J' Γ Γ'
  | nil => nil
  | cons h D γ => cons h (f D) (γ.map f)

-- Natural Deduction
namespace ND

inductive True : (Γ : Ctx) → (A : Propn) → Type
  | hyp : True (.cons .nil A) A
  | oneI : True .nil .one
  | oneE (h : Split Γ Γ₁ Γ₂) (D : True Γ₁ .one) (D₁ : True Γ₂ C) : True Γ C
  | zeroE (h : Split Γ Γ₁ Γ₂) (D : True Γ₁ .zero) : True Γ C
  | topI : True Γ .top
  | tensorI (h : Split Γ Γ₁ Γ₂) (D₁ : True Γ₁ A) (D₂ : True Γ₂ B) : True Γ (A.tensor B)
  | tensorE (h : Split Γ Γ₁ Γ₂) (D : True Γ₁ (A.tensor B)) (D₁ : True (Γ₂.cons A |>.cons B) C) : True Γ C
  | plusI₁ (D : True Γ A) : True Γ (A.plus B)
  | plusI₂ (D : True Γ B) : True Γ (.plus A B)
  | plusE (h : Split Γ Γ₁ Γ₂) (D : True Γ₁ (A.plus B)) (D₁ : True (Γ₂.cons A) C) (D₂ : True (Γ₂.cons B) C) : True Γ C
  | withI (D₁ : True Γ A) (D₂ : True Γ B) : True Γ (A.with B)
  | withE₁ (D : True Γ (A.with B)) : True Γ A
  | withE₂ (D : True Γ (.with A B)) : True Γ B
  | lolliI (D : True (Γ.cons A) B) : True Γ (A.lolli B)
  | lolliE (h : Split Γ Γ₁ Γ₂) (D : True Γ₁ (A.lolli B)) (D₁ : True Γ₂ A) : True Γ B

def True.rename (γ : Rename Γ Γ') {A} : (D : True Γ A) → True Γ' A
  | hyp => let .cons u γ := γ; match u, γ with | .here (Γ := .nil), .nil => hyp
  | oneI => let .nil := γ; oneI
  | oneE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; oneE h (D.rename γ₁) (D₁.rename γ₂)
  | zeroE h D => let ⟨_, _, γ₁, _, h⟩ := γ.split h; zeroE h (D.rename γ₁)
  | topI => topI
  | tensorI h D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; tensorI h (D₁.rename γ₁) (D₂.rename γ₂)
  | tensorE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; tensorE h (D.rename γ₁) (D₁.rename γ₂.cons'.cons')
  | plusI₁ D => plusI₁ (D.rename γ)
  | plusI₂ D => plusI₂ (D.rename γ)
  | plusE h D D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; plusE h (D.rename γ₁) (D₁.rename γ₂.cons') (D₂.rename γ₂.cons')
  | withI D₁ D₂ => withI (D₁.rename γ) (D₂.rename γ)
  | withE₁ D => withE₁ (D.rename γ)
  | withE₂ D => withE₂ (D.rename γ)
  | lolliI D => lolliI (D.rename γ.cons')
  | lolliE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; lolliE h (D.rename γ₁) (D₁.rename γ₂)

instance True.instJudge : Judge True where
  hyp := hyp

def True.subst (γ : Subst True Γ Γ') {A} : (D : True Γ A) → True Γ' A
  | hyp => let .cons h D .nil := γ; match h.eq_triv₁ with | rfl => D
  | oneI => let .nil := γ; oneI
  | oneE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; oneE h (D.subst γ₁) (D₁.subst γ₂)
  | zeroE h D => let ⟨_, _, γ₁, _, h⟩ := γ.split h; zeroE h (D.subst γ₁)
  | topI => topI
  | tensorI h D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; tensorI h (D₁.subst γ₁) (D₂.subst γ₂)
  | tensorE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; tensorE h (D.subst γ₁) (D₁.subst γ₂.cons'.cons')
  | plusI₁ D => plusI₁ (D.subst γ)
  | plusI₂ D => plusI₂ (D.subst γ)
  | plusE h D D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; plusE h (D.subst γ₁) (D₁.subst γ₂.cons') (D₂.subst γ₂.cons')
  | withI D₁ D₂ => withI (D₁.subst γ) (D₂.subst γ)
  | withE₁ D => withE₁ (D.subst γ)
  | withE₂ D => withE₂ (D.subst γ)
  | lolliI D => lolliI (D.subst γ.cons')
  | lolliE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; lolliE h (D.subst γ₁) (D₁.subst γ₂)

end ND

-- Verifications and Uses
namespace VU

mutual

inductive Verif : (Γ : Ctx) → (A : Propn) → Type
  | uv (D : Use Γ (.base P)) : Verif Γ (.base P)
  | oneI : Verif .nil .one
  | oneE (h : Split Γ Γ₁ Γ₂) (D : Use Γ₁ .one) (D₁ : Verif Γ₂ C) : Verif Γ C
  | zeroE (h : Split Γ Γ₁ Γ₂) (D : Use Γ₁ .zero) : Verif Γ C
  | topI : Verif Γ .top
  | tensorI (h : Split Γ Γ₁ Γ₂) (D₁ : Verif Γ₁ A) (D₂ : Verif Γ₂ B) : Verif Γ (A.tensor B)
  | tensorE (h : Split Γ Γ₁ Γ₂) (D : Use Γ₁ (A.tensor B)) (D₁ : Verif (Γ₂.cons A |>.cons B) C) : Verif Γ C
  | plusI₁ (D : Verif Γ A) : Verif Γ (A.plus B)
  | plusI₂ (D : Verif Γ B) : Verif Γ (.plus A B)
  | plusE (h : Split Γ Γ₁ Γ₂) (D : Use Γ₁ (A.plus B)) (D₁ : Verif (Γ₂.cons A) C) (D₂ : Verif (Γ₂.cons B) C) : Verif Γ C
  | withI (D₁ : Verif Γ A) (D₂ : Verif Γ B) : Verif Γ (A.with B)
  | lolliI (D : Verif (Γ.cons A) B) : Verif Γ (A.lolli B)

inductive Use : (Γ : Ctx) → (A : Propn) → Type
  | hyp : Use (.cons .nil A) A
  | withE₁ (D : Use Γ (A.with B)) : Use Γ A
  | withE₂ (D : Use Γ (.with A B)) : Use Γ B
  | lolliE (h : Split Γ Γ₁ Γ₂) (D : Use Γ₁ (A.lolli B)) (D₁ : Verif Γ₂ A) : Use Γ B

end

mutual

def Verif.rename (γ : Rename Γ Γ') {A} : (D : Verif Γ A) → Verif Γ' A
  | .uv D => .uv (D.rename γ)
  | .oneI => let .nil := γ; .oneI
  | .oneE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .oneE h (D.rename γ₁) (D₁.rename γ₂)
  | .zeroE h D => let ⟨_, _, γ₁, _, h⟩ := γ.split h; .zeroE h (D.rename γ₁)
  | .topI => .topI
  | .tensorI h D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .tensorI h (D₁.rename γ₁) (D₂.rename γ₂)
  | .tensorE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .tensorE h (D.rename γ₁) (D₁.rename γ₂.cons'.cons')
  | .plusI₁ D => .plusI₁ (D.rename γ)
  | .plusI₂ D => .plusI₂ (D.rename γ)
  | .plusE h D D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .plusE h (D.rename γ₁) (D₁.rename γ₂.cons') (D₂.rename γ₂.cons')
  | .withI D₁ D₂ => .withI (D₁.rename γ) (D₂.rename γ)
  | .lolliI D => .lolliI (D.rename γ.cons')

def Use.rename (γ : Rename Γ Γ') {A} : (D : Use Γ A) → Use Γ' A
  | .hyp => let .cons u γ := γ; match u, γ with | .here (Γ := .nil), .nil => .hyp
  | .withE₁ D => .withE₁ (D.rename γ)
  | .withE₂ D => .withE₂ (D.rename γ)
  | .lolliE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .lolliE h (D.rename γ₁) (D₁.rename γ₂)

end

instance Use.instJudge : Judge Use where
  hyp := hyp

mutual

def Verif.subst (γ : Subst Use Γ Γ') {A} : (D : Verif Γ A) → Verif Γ' A
  | .uv D => .uv (D.subst γ)
  | .oneI => let .nil := γ; .oneI
  | .oneE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .oneE h (D.subst γ₁) (D₁.subst γ₂)
  | .zeroE h D => let ⟨_, _, γ₁, _, h⟩ := γ.split h; .zeroE h (D.subst γ₁)
  | .topI => .topI
  | .tensorI h D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .tensorI h (D₁.subst γ₁) (D₂.subst γ₂)
  | .tensorE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .tensorE h (D.subst γ₁) (D₁.subst γ₂.cons'.cons')
  | .plusI₁ D => .plusI₁ (D.subst γ)
  | .plusI₂ D => .plusI₂ (D.subst γ)
  | .plusE h D D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .plusE h (D.subst γ₁) (D₁.subst γ₂.cons') (D₂.subst γ₂.cons')
  | .withI D₁ D₂ => .withI (D₁.subst γ) (D₂.subst γ)
  | .lolliI D => .lolliI (D.subst γ.cons')

def Use.subst (γ : Subst Use Γ Γ') {A} : (D : Use Γ A) → Use Γ' A
  | .hyp => let .cons h D .nil := γ; match h.eq_triv₁ with | rfl => D
  | .withE₁ D => .withE₁ (D.subst γ)
  | .withE₂ D => .withE₂ (D.subst γ)
  | .lolliE h D D₁ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; .lolliE h (D.subst γ₁) (D₁.subst γ₂)

end

def Verif.uv' (D : Use Γ A) : Verif Γ A :=
  match A with
  | .base _ => uv D
  | .one => oneE .triv₁ D oneI
  | .zero => zeroE .triv₁ D
  | .top => topI
  | .tensor .. => tensorE .triv₁ D (tensorI (.cons₂ (.cons₁ .nil)) (uv' .hyp) (uv' .hyp))
  | .plus .. => plusE .triv₁ D (plusI₁ (uv' .hyp)) (plusI₂ (uv' .hyp))
  | .with .. => withI (uv' (.withE₁ D)) (uv' (.withE₂ D))
  | .lolli .. => lolliI (uv' (.lolliE (.cons₂ .triv₁) D (uv' .hyp)))

mutual

def Verif.toTrue : (D : Verif Γ A) → ND.True Γ A
  | .uv D => D.toTrue
  | .oneI => .oneI
  | .oneE h D D₁ => .oneE h D.toTrue D₁.toTrue
  | .zeroE h D => .zeroE h D.toTrue
  | .topI => .topI
  | .tensorI h D₁ D₂ => .tensorI h D₁.toTrue D₂.toTrue
  | .tensorE h D D₁ => .tensorE h D.toTrue D₁.toTrue
  | .plusI₁ D => .plusI₁ D.toTrue
  | .plusI₂ D => .plusI₂ D.toTrue
  | .plusE h D D₁ D₂ => .plusE h D.toTrue D₁.toTrue D₂.toTrue
  | .withI D₁ D₂ => .withI D₁.toTrue D₂.toTrue
  | .lolliI D => .lolliI D.toTrue

def Use.toTrue : (D : Use Γ A) → ND.True Γ A
  | .hyp => .hyp
  | .withE₁ D => .withE₁ D.toTrue
  | .withE₂ D => .withE₂ D.toTrue
  | .lolliE h D D₁ => .lolliE h D.toTrue D₁.toTrue

end

end VU

-- Sequent Calculus
namespace SC

inductive Seq : (Γ : Ctx) → (A : Propn) → Type
  | id : Seq (.cons .nil (.base P)) (.base P)
  | oneR : Seq .nil .one
  | oneL (u : Mem .one Γ) (D : Seq (Γ.del u) C) : Seq Γ C
  | zeroL (u : Mem .zero Γ) : Seq Γ C
  | topR : Seq Γ .top
  | tensorR (h : Split Γ Γ₁ Γ₂) (D₁ : Seq Γ₁ A) (D₂ : Seq Γ₂ B) : Seq Γ (A.tensor B)
  | tensorL (u : Mem (A.tensor B) Γ) (D : Seq (Γ.del u |>.cons A |>.cons B) C) : Seq Γ C
  | plusR₁ (D : Seq Γ A) : Seq Γ (A.plus B)
  | plusR₂ (D : Seq Γ B) : Seq Γ (.plus A B)
  | plusL (u : Mem (A.plus B) Γ) (D₁ : Seq (Γ.del u |>.cons A) C) (D₂ : Seq (Γ.del u |>.cons B) C) : Seq Γ C
  | withR (D₁ : Seq Γ A) (D₂ : Seq Γ B) : Seq Γ (A.with B)
  | withL₁ (u : Mem (A.with B) Γ) (D : Seq (Γ.del u |>.cons A) C) : Seq Γ C
  | withL₂ (u : Mem (.with A B) Γ) (D : Seq (Γ.del u |>.cons B) C) : Seq Γ C
  | lolliR (D : Seq (Γ.cons A) B) : Seq Γ (A.lolli B)
  | lolliL (u : Mem (A.lolli B) Γ) (h : Split (Γ.del u) Γ₁ Γ₂) (D₁ : Seq Γ₁ A) (D₂ : Seq (Γ₂.cons B) C) : Seq Γ C

def Seq.rename (γ : Rename Γ Γ') {A} : (D : Seq Γ A) → Seq Γ' A
  | id => let .cons u γ := γ; match u, γ with | .here (Γ := .nil), .nil => id
  | oneR => let .nil := γ; oneR
  | oneL u D => oneL (u.rename γ) (D.rename (γ.del u))
  | zeroL u => zeroL (u.rename γ)
  | topR => topR
  | tensorR h D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := γ.split h; tensorR h (D₁.rename γ₁) (D₂.rename γ₂)
  | tensorL u D => tensorL (u.rename γ) (D.rename (γ.del u).cons'.cons')
  | plusR₁ D => plusR₁ (D.rename γ)
  | plusR₂ D => plusR₂ (D.rename γ)
  | plusL u D₁ D₂ => plusL (u.rename γ) (D₁.rename (γ.del u).cons') (D₂.rename (γ.del u).cons')
  | withR D₁ D₂ => withR (D₁.rename γ) (D₂.rename γ)
  | withL₁ u D => withL₁ (u.rename γ) (D.rename (γ.del u).cons')
  | withL₂ u D => withL₂ (u.rename γ) (D.rename (γ.del u).cons')
  | lolliR D => lolliR (D.rename γ.cons')
  | lolliL u h D₁ D₂ => let ⟨_, _, γ₁, γ₂, h⟩ := (γ.del u).split h; lolliL (u.rename γ) h (D₁.rename γ₁) (D₂.rename γ₂.cons')

def Seq.id' : Seq (.cons .nil A) A :=
  match A with
  | .base _ => id
  | .one => oneL .here oneR
  | .zero => zeroL .here
  | .top => topR
  | .tensor .. => tensorL .here (tensorR (.cons₂ (.cons₁ .nil)) id' id')
  | .plus .. => plusL .here (plusR₁ id') (plusR₂ id')
  | .with .. => withR (withL₁ .here id') (withL₂ .here id')
  | .lolli .. => lolliR (lolliL (.there .here) (.cons₁ .nil) id' id')

@[simp]
def Seq.sizeOf : (D : Seq Γ A) → Nat
  | id | oneR | zeroL _ | topR => 0
  | oneL _ D | tensorL _ D | plusR₁ D | plusR₂ D | withL₁ _ D | withL₂ _ D | lolliR D => D.sizeOf + 1
  | tensorR _ D₁ D₂ | plusL _ D₁ D₂ | withR D₁ D₂ | lolliL _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename {γ : Rename Γ Γ'} (D : Seq Γ A) : (D.rename γ).sizeOf = D.sizeOf := by
  induction D generalizing Γ' <;> simp! only [*]
  case id => let .cons u γ := γ; match u, γ with | .here (Γ := .nil), .nil => rfl
  case oneR => let .nil := γ; rfl

def Seq.cut (h : Split Γ Γ₁ Γ₂) : (D : Seq Γ₁ A) → (E : Seq (Γ₂.cons A) C) → Seq Γ C
  | D, id => match h.eq_triv₁ with | rfl => D
  | oneR, oneL .here E => match h.eq_triv₂ with | rfl => E
  | tensorR h₁ D₁ D₂, tensorL .here E => let ⟨_, h', h''⟩ := h.shift₁ h₁; cut h' D₁ (cut h''.cons₂ D₂ E)
  | plusR₁ D, plusL .here E₁ _ => cut h D E₁
  | plusR₂ D, plusL .here _ E₂ => cut h D E₂
  | withR D₁ _, withL₁ .here E => cut h D₁ E
  | withR _ D₂, withL₂ .here E => cut h D₂ E
  | lolliR D, lolliL .here h₂ E₁ E₂ => let ⟨_, h', h''⟩ := h.shift₂ h₂; cut h' (cut h''.flip E₁ D) E₂
  | oneL u D, E => oneL (u.ofSplit₁ h) (cut (h.del₁ u) D E)
  | zeroL u, _ => zeroL (u.ofSplit₁ h)
  | tensorL u D, E => tensorL (u.ofSplit₁ h) (cut (h.del₁ u).cons₁.cons₁ D E)
  | plusL u D₁ D₂, E => plusL (u.ofSplit₁ h) (cut (h.del₁ u).cons₁ D₁ E) (cut (h.del₁ u).cons₁ D₂ E)
  | withL₁ u D, E => withL₁ (u.ofSplit₁ h) (cut (h.del₁ u).cons₁ D E)
  | withL₂ u D, E => withL₂ (u.ofSplit₁ h) (cut (h.del₁ u).cons₁ D E)
  | lolliL u h₁ D₁ D₂, E => let ⟨_, h', h''⟩ := (h.del₁ u).shift₁ h₁; lolliL (u.ofSplit₁ h) h' D₁ (cut h''.cons₁ D₂ E)
  | D, oneL (.there u) E => oneL (u.ofSplit₂ h) (cut (h.del₂ u) D E)
  | _, zeroL (.there u) => zeroL (u.ofSplit₂ h)
  | _, topR => topR
  | D, tensorR (.cons₁ h₂) E₁ E₂ => let ⟨_, h', h''⟩ := h.shift₂ h₂; tensorR h' (cut h'' D E₁) E₂
  | D, tensorR (.cons₂ h₂) E₁ E₂ => let ⟨_, h', h''⟩ := h.flip.shift₁ h₂; tensorR h' E₁ (cut h''.flip D E₂)
  | D, tensorL (.there u) E => tensorL (u.ofSplit₂ h) (cut (h.del₂ u).cons₂.cons₂ D (E.rename .exchange₂))
  | D, plusR₁ E => plusR₁ (cut h D E)
  | D, plusR₂ E => plusR₂ (cut h D E)
  | D, plusL (.there u) E₁ E₂ => plusL (u.ofSplit₂ h) (cut (h.del₂ u).cons₂ D (E₁.rename .exchange)) (cut (h.del₂ u).cons₂ D (E₂.rename .exchange))
  | D, withR E₁ E₂ => withR (cut h D E₁) (cut h D E₂)
  | D, withL₁ (.there u) E => withL₁ (u.ofSplit₂ h) (cut (h.del₂ u).cons₂ D (E.rename .exchange))
  | D, withL₂ (.there u) E => withL₂ (u.ofSplit₂ h) (cut (h.del₂ u).cons₂ D (E.rename .exchange))
  | D, lolliR E => lolliR (cut h.cons₂ D (E.rename .exchange))
  | D, lolliL (.there u) h₂ E₁ E₂ =>
    match h₂ with
    | .cons₁ h₂ => let ⟨_, h', h''⟩ := (h.del₂ u).shift₂ h₂; lolliL (u.ofSplit₂ h) h' (cut h'' D E₁) E₂
    | .cons₂ h₂ => let ⟨_, h', h''⟩ := (h.del₂ u).flip.shift₁ h₂; lolliL (u.ofSplit₂ h) h' E₁ (cut h''.flip.cons₂ D (E₂.rename .exchange))
  termination_by D E => (A, D.sizeOf, E.sizeOf)

def Seq.multicut : (γ : Subst Seq Γ₂ Γ₂') → ∀ {Γ₁ A}, (D : Seq (.append Γ₁ Γ₂) A) → Seq (Γ₁.append Γ₂') A
  | .nil, _, _, D => D
  | .cons h D' γ, _, _, D => (multicut γ (Ctx.append_append ▸ cut .append D' D)).rename (h.rename.append.comp .appendSwap)

def Seq.subst (γ : Subst Seq Γ Γ') {A} (D : Seq Γ A) : Seq Γ' A :=
  (Ctx.nil_append ▸ multicut γ (Γ₁ := .nil) (A := A) (Ctx.nil_append ▸ D) :)

def Seq.toVerif : (D : Seq Γ A) → VU.Verif Γ A
  | id => .uv .hyp
  | oneR => .oneI
  | oneL u D => .oneE (.ofMem u) .hyp D.toVerif
  | zeroL u => .zeroE (.ofMem u) .hyp
  | topR => .topI
  | tensorR h D₁ D₂ => .tensorI h D₁.toVerif D₂.toVerif
  | tensorL u D => .tensorE (.ofMem u) .hyp D.toVerif
  | plusR₁ D => .plusI₁ D.toVerif
  | plusR₂ D => .plusI₂ D.toVerif
  | plusL u D₁ D₂ => .plusE (.ofMem u) .hyp D₁.toVerif D₂.toVerif
  | withR D₁ D₂ => .withI D₁.toVerif D₂.toVerif
  | withL₁ u D => D.toVerif.subst (.cons (.ofMem u) (.withE₁ .hyp) .id)
  | withL₂ u D => D.toVerif.subst (.cons (.ofMem u) (.withE₂ .hyp) .id)
  | lolliR D => .lolliI D.toVerif
  | lolliL u h D₁ D₂ => let ⟨_, h, h'⟩ := (Split.ofMem u).shift₂ h; D₂.toVerif.subst (.cons h (.lolliE h' .hyp D₁.toVerif) .id)

end SC

def ND.True.toSeq : (D : True Γ A) → SC.Seq Γ A
  | hyp => .id'
  | oneI => .oneR
  | oneE h D D₁ => .cut h D.toSeq (.oneL .here D₁.toSeq)
  | zeroE h D => .cut h D.toSeq (.zeroL .here)
  | topI => .topR
  | tensorI h D₁ D₂ => .tensorR h D₁.toSeq D₂.toSeq
  | tensorE h D D₁ => .cut h D.toSeq (.tensorL .here D₁.toSeq)
  | plusI₁ D => .plusR₁ D.toSeq
  | plusI₂ D => .plusR₂ D.toSeq
  | plusE h D D₁ D₂ => .cut h D.toSeq (.plusL .here D₁.toSeq D₂.toSeq)
  | withI D₁ D₂ => .withR D₁.toSeq D₂.toSeq
  | withE₁ D => .cut .triv₁ D.toSeq (.withL₁ .here .id')
  | withE₂ D => .cut .triv₁ D.toSeq (.withL₂ .here .id')
  | lolliI D => .lolliR D.toSeq
  | lolliE h D D₁ => .cut h D.toSeq (.lolliL .here .triv₁ D₁.toSeq .id')

def VU.Verif.subst' (γ : Subst Verif Γ Γ') {A} (D : Verif Γ A) : Verif Γ' A :=
  (D.toTrue.toSeq.subst (γ.map fun D => D.toTrue.toSeq)).toVerif
