inductive Propn
  | base (P : Nat)
  | one
  | zero
  | top
  | tensor (A B : Propn)
  | plus (A B : Propn)
  | with (A B : Propn)
  | lolli (A B : Propn)

inductive Ctx
  | nil
  | cons (Δ : Ctx) (A : Propn)

def Ctx.append (Δ : Ctx) : (Δ' : Ctx) → Ctx
  | nil => Δ
  | cons Δ' A => cons (Δ.append Δ') A

inductive Mem (A : Propn) : (Δ : Ctx) → Type
  | here : Mem A (.cons Δ A)
  | there (u : Mem A Δ) : Mem A (Δ.cons B)

def Ctx.del : (Δ : Ctx) → (u : Mem A Δ) → Ctx
   | cons Δ _, .here => Δ
   | cons Δ A, .there u => cons (Δ.del u) A

inductive Split : (Δ Δ₁ Δ₂ : Ctx) → Type
  | nil : Split .nil .nil .nil
  | cons₁ (h : Split Δ Δ₁ Δ₂) : Split (Δ.cons A) (Δ₁.cons A) Δ₂
  | cons₂ (h : Split Δ Δ₁ Δ₂) : Split (Δ.cons A) Δ₁ (Δ₂.cons A)

def Split.triv₁ : ∀ {Δ}, Split Δ Δ .nil
  | .nil => nil
  | .cons .. => cons₁ triv₁

def Split.triv₂ : ∀ {Δ}, Split Δ .nil Δ
  | .nil => nil
  | .cons .. => cons₂ triv₂

def Split.flip : (h : Split Δ Δ₁ Δ₂) → Split Δ Δ₂ Δ₁
  | nil => nil
  | cons₁ h => cons₂ h.flip
  | cons₂ h => cons₁ h.flip

def Split.append : ∀ {Δ₂}, Split (Δ₁.append Δ₂) Δ₁ Δ₂
  | .nil => triv₁
  | .cons .. => cons₂ append

def Split.revAppend : ∀ {Δ₂}, Split (Δ₁.append Δ₂) Δ₂ Δ₁
  | .nil => triv₂
  | .cons .. => cons₁ revAppend

def Split.shift₁ : (h : Split Δ Δ₁ Δ₂) → (h₁ : Split Δ₁ Δ₁₁ Δ₁₂) → Σ Δ', Split Δ' Δ₁₂ Δ₂ × Split Δ Δ₁₁ Δ'
  | h, nil => ⟨_, h, triv₂⟩
  | cons₁ h, cons₁ h₁ => let ⟨_, h', h''⟩ := h.shift₁ h₁; ⟨_, h', cons₁ h''⟩
  | cons₁ h, cons₂ h₁ => let ⟨_, h', h''⟩ := h.shift₁ h₁; ⟨_, cons₁ h', cons₂ h''⟩
  | cons₂ h, h₁ => let ⟨_, h', h''⟩ := h.shift₁ h₁; ⟨_, cons₂ h', cons₂ h''⟩

def Split.shift₂ : (h : Split Δ Δ₁ Δ₂) → (h₂ : Split Δ₂ Δ₂₁ Δ₂₂) → Σ Δ', Split Δ' Δ₂₁ Δ₁ × Split Δ Δ' Δ₂₂
  | h, nil => ⟨_, triv₂, h⟩
  | cons₁ h, h₂ => let ⟨_, h', h''⟩ := h.shift₂ h₂; ⟨_, cons₂ h', cons₁ h''⟩
  | cons₂ h, cons₁ h₂ => let ⟨_, h', h''⟩ := h.shift₂ h₂; ⟨_, cons₁ h', cons₁ h''⟩
  | cons₂ h, cons₂ h₂ => let ⟨_, h', h''⟩ := h.shift₂ h₂; ⟨_, h', cons₂ h''⟩

@[elab_as_elim]
def Split.rec₁
  {motive : ∀ Δ Δ₁, (h : Split Δ Δ₁ .nil) → Sort u}
  (nil : motive .nil .nil nil)
  (cons₁ : ∀ {Δ Δ₁ A} h, motive Δ Δ₁ h → motive (Δ.cons A) (Δ₁.cons A) h.cons₁)
  {Δ Δ₁}
: ∀ h, motive Δ Δ₁ h
  | .nil => nil
  | .cons₁ h => cons₁ h (rec₁ nil @cons₁ h)

@[elab_as_elim]
def Split.rec₂
  {motive : ∀ Δ Δ₂, (h : Split Δ .nil Δ₂) → Sort u}
  (nil : motive .nil .nil nil)
  (cons₂ : ∀ {Δ Δ₂ A} h, motive Δ Δ₂ h → motive (Δ.cons A) (Δ₂.cons A) h.cons₂)
  {Δ Δ₂}
: ∀ h, motive Δ Δ₂ h
  | .nil => nil
  | .cons₂ h => cons₂ h (rec₂ nil @cons₂ h)

def Split.rec_triv₁ {motive : ∀ Δ Δ₁, (h : Split Δ Δ₁ .nil) → Sort u} (triv₁ : ∀ {Δ}, motive Δ Δ triv₁) {Δ Δ₁} h : motive Δ Δ₁ h :=
  match (rec₁ rfl (fun | _, rfl => rfl) h : (⟨Δ₁, h⟩ : Σ Δ₁, Split _ Δ₁ _) = ⟨Δ, .triv₁⟩) with
  | rfl => triv₁

def Split.rec_triv₂ {motive : ∀ Δ Δ₂, (h : Split Δ .nil Δ₂) → Sort u} (triv₂ : ∀ {Δ}, motive Δ Δ triv₂) {Δ Δ₂} h : motive Δ Δ₂ h :=
  match (rec₂ rfl (fun | _, rfl => rfl) h : Sigma.mk Δ₂ h = ⟨Δ, .triv₂⟩) with
  | rfl => triv₂

def Mem.split₁ : (u : Mem A Δ₁) → (h : Split Δ Δ₁ Δ₂) → Mem A Δ
  | here, .cons₁ _ => here
  | there u, .cons₁ h => there (u.split₁ h)
  | u, .cons₂ h => there (u.split₁ h)

def Mem.split₂ : (u : Mem A Δ₂) → (h : Split Δ Δ₁ Δ₂) → Mem A Δ
  | u, .cons₁ h => there (split₂ u h)
  | here, .cons₂ h => here
  | there u, .cons₂ h => there (split₂ u h)

def Split.del₁ : (h : Split Δ Δ₁ Δ₂) → (u : Mem A Δ₁) → Split (Δ.del (u.split₁ h)) (Δ₁.del u) Δ₂
  | cons₁ h, .here => h
  | cons₁ h, .there u => cons₁ (h.del₁ u)
  | cons₂ h, .here => cons₂ (h.del₁ .here)
  | cons₂ h, .there u => cons₂ (h.del₁ (.there u))

def Split.del₂ : (h : Split Δ Δ₁ Δ₂) → (u : Mem A Δ₂) → Split (Δ.del (u.split₂ h)) Δ₁ (Δ₂.del u)
  | cons₁ h, .here => cons₁ (h.del₂ .here)
  | cons₁ h, .there u => cons₁ (h.del₂ (.there u))
  | cons₂ h, .here => h
  | cons₂ h, .there u => cons₂ (h.del₂ u)

def Mem.del : (u : Mem B Δ) → (v : Mem A (Δ.del u)) → Mem A Δ
  | here, v => .there v
  | there u, v => by cases v with | here => exact here | there v => exact there (u.del v)

def Mem.del' : (u : Mem A Δ) → (v : Mem B (Δ.del u)) → Mem A (Δ.del (u.del v))
  | here, _ => here
  | there u, v => by cases v with | here => exact u | there v => exact there (u.del' v)

theorem Ctx.del_del : {u : Mem A Δ} → {v : Mem B (Δ.del u)} → (Δ.del u).del v = (Δ.del (u.del v)).del (u.del' v)
  | .here, _ => rfl
  | .there u, v => by cases v with | here => exact rfl | there v => exact congrArg (cons · _) del_del

def Rename : (Δ Δ' : Ctx) → Type
  | .nil, .nil => Unit
  | .nil, .cons .. => Empty
  | .cons Δ A, Δ' => (u : Mem A Δ') × Rename Δ (Δ'.del u)

def Rename.cons (δ : Rename Δ Δ') {A} : Rename (Δ.cons A) (Δ'.cons A) :=
  ⟨.here, δ⟩

def Rename.id : ∀ {Δ}, Rename Δ Δ
  | .nil => ()
  | .cons .. => ⟨.here, id⟩

def Rename.exchange : Rename (Ctx.cons Δ A |>.cons B) (Δ.cons B |>.cons A) :=
  ⟨.there .here, .here, id⟩

def Rename.exchange₂ : Rename (Ctx.cons Δ A |>.cons B |>.cons C) (Δ.cons B |>.cons C |>.cons A) :=
  ⟨.there .here, .there .here, .here, id⟩

def Mem.rename (δ : Rename Δ Δ') {A} : (u : Mem A Δ) → Mem A Δ'
  | here => δ.fst
  | there u => δ.fst.del (u.rename δ.snd)

def Rename.del (δ : Rename Δ Δ') {A} (u : Mem A Δ) : Rename (Δ.del u) (Δ'.del (u.rename δ)) :=
  match Δ, u with
  | _, .here => δ.snd
  | _, .there u => ⟨δ.fst.del' (u.rename δ.snd), Eq.ndrec (δ.snd.del u) Ctx.del_del⟩

def Rename.comp (δ : Rename Δ Δ') (δ' : Rename Δ' Δ'') : Rename Δ Δ'' :=
  match Δ with
  | .nil => let .nil := Δ'; let .nil := Δ''; ()
  | .cons .. => ⟨δ.fst.rename δ', δ.snd.comp (δ'.del δ.fst)⟩

def Split.insert₁ : (u : Mem A Δ) → (h : Split (Δ.del u) Δ₁ Δ₂) → Ctx
  | .here, h => Δ₁.cons A
  | .there (B := B) u, h => match h with | .cons₁ h => (h.insert₁ u).cons B | .cons₂ h => h.insert₁ u

def Split.rename_insert₁ : (u : Mem A Δ) → (h : Split (Δ.del u) Δ₁ Δ₂) → Rename (Δ₁.cons A) (h.insert₁ u)
  | .here, h => ⟨.here, .id⟩
  | .there u, h => match h with | .cons₁ h => ⟨.there (h.rename_insert₁ u).fst, .here, (h.rename_insert₁ u).snd⟩ | .cons₂ h => h.rename_insert₁ u

def Split.split_insert₁ : (u : Mem A Δ) → (h : Split (Δ.del u) Δ₁ Δ₂) → Split Δ (h.insert₁ u) Δ₂
  | .here, h => h.cons₁
  | .there u, h => match h with | .cons₁ h => (h.split_insert₁ u).cons₁ | .cons₂ h => (h.split_insert₁ u).cons₂

def Split.insert₂ : (u : Mem A Δ) → (h : Split (Δ.del u) Δ₁ Δ₂) → Ctx
  | .here, h => Δ₂.cons A
  | .there (B := B) u, h => match h with | .cons₁ h => h.insert₂ u | .cons₂ h => (h.insert₂ u).cons B

def Split.rename_insert₂ : (u : Mem A Δ) → (h : Split (Δ.del u) Δ₁ Δ₂) → Rename (Δ₂.cons A) (h.insert₂ u)
  | .here, h => ⟨.here, .id⟩
  | .there u, h => match h with | .cons₁ h => h.rename_insert₂ u | .cons₂ h => ⟨.there (h.rename_insert₂ u).fst, .here, (h.rename_insert₂ u).snd⟩

def Split.split_insert₂ : (u : Mem A Δ) → (h : Split (Δ.del u) Δ₁ Δ₂) → Split Δ Δ₁ (h.insert₂ u)
  | .here, h => h.cons₂
  | .there u, h => match h with | .cons₁ h => (h.split_insert₂ u).cons₁ | .cons₂ h => (h.split_insert₂ u).cons₂

def Split.rename (δ : Rename Δ Δ') : (h : Split Δ Δ₁ Δ₂) → Σ Δ₁' Δ₂', Rename Δ₁ Δ₁' × Rename Δ₂ Δ₂' × Split Δ' Δ₁' Δ₂'
  | nil => match Δ' with | .nil => ⟨.nil, .nil, (), (), nil⟩
  | cons₁ h => let ⟨Δ₁', _, δ₁, δ₂, h'⟩ := h.rename δ.snd; ⟨_, _, .comp ⟨.here, by dsimp! only; exact δ₁⟩ (h'.rename_insert₁ _), δ₂, h'.split_insert₁ δ.fst⟩
  | cons₂ h => let ⟨_, Δ₂', δ₁, δ₂, h'⟩ := h.rename δ.snd; ⟨_, _, δ₁, .comp ⟨.here, by dsimp! only; exact δ₂⟩ (h'.rename_insert₂ _), h'.split_insert₂ δ.fst⟩

theorem Rename.singleton : ∀ {Δ}, (δ : Rename (.cons .nil A) Δ) → Sigma.mk Δ δ = ⟨.cons .nil A, .here, ()⟩
  | .cons .nil _, ⟨.here, _⟩ => rfl
  | .cons (.cons ..) _, ⟨.here, δ⟩ => nomatch δ

def Split.toRename : (h : Split Δ Δ₁ (.cons .nil A)) → Rename (Δ₁.cons A) Δ
  | cons₁ h => ⟨.there h.toRename.fst, .here, h.toRename.snd⟩
  | cons₂ h => ⟨.here, by induction h using Split.rec_triv₁; exact .id⟩

-- Sequent Calculus
namespace SC

inductive Seq : (Δ : Ctx) → (A : Propn) → Type
  | id : Seq (.cons .nil (.base P)) (.base P)
  | oneR : Seq .nil .one
  | oneL (u : Mem .one Δ) (D : Seq (Δ.del u) C) : Seq Δ C
  | zeroL (u : Mem .zero Δ) : Seq Δ C
  | topR : Seq Δ .top
  | tensorR (h : Split Δ Δ₁ Δ₂) (D₁ : Seq Δ₁ A) (D₂ : Seq Δ₂ B) : Seq Δ (A.tensor B)
  | tensorL (u : Mem (A.tensor B) Δ) (D : Seq (Δ.del u |>.cons A |>.cons B) C) : Seq Δ C
  | plusR₁ (D : Seq Δ A) : Seq Δ (A.plus B)
  | plusR₂ (D : Seq Δ B) : Seq Δ (.plus A B)
  | plusL (u : Mem (A.plus B) Δ) (D₁ : Seq (Δ.del u |>.cons A) C) (D₂ : Seq (Δ.del u |>.cons B) C) : Seq Δ C
  | withR (D₁ : Seq Δ A) (D₂ : Seq Δ B) : Seq Δ (A.with B)
  | withL₁ (u : Mem (A.with B) Δ) (D : Seq (Δ.del u |>.cons A) C) : Seq Δ C
  | withL₂ (u : Mem (.with A B) Δ) (D : Seq (Δ.del u |>.cons B) C) : Seq Δ C
  | lolliR (D : Seq (Δ.cons A) B) : Seq Δ (A.lolli B)
  | lolliL (u : Mem (A.lolli B) Δ) (h : Split (Δ.del u) Δ₁ Δ₂) (D₁ : Seq Δ₁ A) (D₂ : Seq (Δ₂.cons B) C) : Seq Δ C

def Seq.rename (δ : Rename Δ Δ') {A} : (D : Seq Δ A) → Seq Δ' A
  | id => by cases δ.singleton; exact id
  | oneR => let .nil := Δ'; oneR
  | oneL u D => oneL (u.rename δ) (D.rename (δ.del u))
  | zeroL u => zeroL (u.rename δ)
  | topR => topR
  | tensorR h D₁ D₂ => let ⟨_, _, δ₁, δ₂, h'⟩ := h.rename δ; tensorR h' (D₁.rename δ₁) (D₂.rename δ₂)
  | tensorL u D => tensorL (u.rename δ) (D.rename (δ.del u).cons.cons)
  | plusR₁ D => plusR₁ (D.rename δ)
  | plusR₂ D => plusR₂ (D.rename δ)
  | plusL u D₁ D₂ => plusL (u.rename δ) (D₁.rename (δ.del u).cons) (D₂.rename (δ.del u).cons)
  | withR D₁ D₂ => withR (D₁.rename δ) (D₂.rename δ)
  | withL₁ u D => withL₁ (u.rename δ) (D.rename (δ.del u).cons)
  | withL₂ u D => withL₂ (u.rename δ) (D.rename (δ.del u).cons)
  | lolliR D => lolliR (D.rename δ.cons)
  | lolliL u h D₁ D₂ => let ⟨_, _, δ₁, δ₂, h'⟩ := h.rename (δ.del u); lolliL (u.rename δ) h' (D₁.rename δ₁) (D₂.rename δ₂.cons)

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
def Seq.sizeOf : (D : Seq Δ A) → Nat
  | id => 0
  | oneR => 0
  | oneL _ D => D.sizeOf + 1
  | zeroL _ => 0
  | topR => 0
  | tensorR _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1
  | tensorL _ D => D.sizeOf + 1
  | plusR₁ D => D.sizeOf + 1
  | plusR₂ D => D.sizeOf + 1
  | plusL _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1
  | withR D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1
  | withL₁ _ D => D.sizeOf + 1
  | withL₂ _ D => D.sizeOf + 1
  | lolliR D => D.sizeOf + 1
  | lolliL _ _ D₁ D₂ => D₁.sizeOf + D₂.sizeOf + 1

@[simp]
theorem Seq.sizeOf_rename {δ : Rename Δ Δ'} (D : Seq Δ A) : (D.rename δ).sizeOf = D.sizeOf :=
  by induction D generalizing Δ' <;> simp [*]; cases δ.singleton; rfl; let .nil := Δ'; rfl

def Seq.cut (h : Split Δ Δ₁ Δ₂) : (D : Seq Δ₁ A) → (E : Seq (Δ₂.cons A) C) → Seq Δ C
  | .id, E => E.rename h.flip.toRename
  | D, .id => by cases h using Split.rec_triv₁; exact D
  | oneR, oneL .here E => by cases h using Split.rec_triv₂; exact E
  | tensorR h₁ D₁ D₂, tensorL .here E => let ⟨_, h', h''⟩ := h.shift₁ h₁; cut h'' D₁ (cut h'.cons₂ D₂ E)
  | plusR₁ D, plusL .here E₁ _ => cut h D E₁
  | plusR₂ D, plusL .here _ E₂ => cut h D E₂
  | withR D₁ _, withL₁ .here E => cut h D₁ E
  | withR _ D₂, withL₂ .here E => cut h D₂ E
  | lolliR D, lolliL .here h₂ E₁ E₂ => let ⟨_, h', h''⟩ := h.shift₂ h₂; cut h'' (cut h' E₁ D) E₂
  | oneL u D, E => oneL (u.split₁ h) (cut (h.del₁ u) D E)
  | zeroL u, _ => zeroL (u.split₁ h)
  | tensorL u D, E => tensorL (u.split₁ h) (cut (h.del₁ u).cons₁.cons₁ D E)
  | plusL u D₁ D₂, E => plusL (u.split₁ h) (cut (h.del₁ u).cons₁ D₁ E) (cut (h.del₁ u).cons₁ D₂ E)
  | withL₁ u D, E => withL₁ (u.split₁ h) (cut (h.del₁ u).cons₁ D E)
  | withL₂ u D, E => withL₂ (u.split₁ h) (cut (h.del₁ u).cons₁ D E)
  | lolliL u h₁ D₁ D₂, E => let ⟨_, h', h''⟩ := h.del₁ u |>.shift₁ h₁; lolliL (u.split₁ h) h'' D₁ (cut h'.cons₁ D₂ E)
  | D, oneL (.there u) E => oneL (u.split₂ h) (cut (h.del₂ u) D E)
  | D, zeroL (.there u) => zeroL (u.split₂ h)
  | _, topR => topR
  | D, tensorR (.cons₁ h₂) E₁ E₂ => let ⟨_, h', h''⟩ := h.shift₂ h₂; tensorR h'' (cut h'.flip D E₁) E₂
  | D, tensorR (.cons₂ h₂) E₁ E₂ => let ⟨_, h', h''⟩ := h.flip.shift₁ h₂; tensorR h'' E₁ (cut h'.flip D E₂)
  | D, tensorL (.there u) E => tensorL (u.split₂ h) (cut (h.del₂ u).cons₂.cons₂ D (E.rename .exchange₂))
  | D, plusR₁ E => plusR₁ (cut h D E)
  | D, plusR₂ E => plusR₂ (cut h D E)
  | D, plusL (.there u) E₁ E₂ => plusL (u.split₂ h) (cut (h.del₂ u).cons₂ D (E₁.rename .exchange)) (cut (h.del₂ u).cons₂ D (E₂.rename .exchange))
  | D, withR E₁ E₂ => withR (cut h D E₁) (cut h D E₂)
  | D, withL₁ (.there u) E => withL₁ (u.split₂ h) (cut (h.del₂ u).cons₂ D (E.rename .exchange))
  | D, withL₂ (.there u) E => withL₂ (u.split₂ h) (cut (h.del₂ u).cons₂ D (E.rename .exchange))
  | D, lolliR E => lolliR (cut h.cons₂ D (E.rename .exchange))
  | D, lolliL (.there u) h₂ E₁ E₂ => match h₂ with | .cons₁ h₂ => let ⟨_, h', h''⟩ := h.del₂ u |>.shift₂ h₂; lolliL (u.split₂ h) h'' (cut h'.flip D E₁) E₂ | .cons₂ h₂ => let ⟨_, h', h''⟩ := h.del₂ u |>.flip.shift₁ h₂; lolliL (u.split₂ h) h'' E₁ (cut h'.flip.cons₂ D (E₂.rename .exchange))
  termination_by D E => (A, D.sizeOf, E.sizeOf)

end SC
