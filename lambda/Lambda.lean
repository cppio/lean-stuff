import Mathlib

def heq_of_cast_eq : (h : α = β) → cast h x = y → HEq x y
  | rfl, rfl => cast_heq rfl x

def Nat.lt_trans' {n m l : Nat} : n ≤ m → m < l → n < l :=
  Nat.le_trans ∘ Nat.succ_le_succ

def Fin.zero {n : Nat} : Fin n.succ :=
  ⟨0, n.zero_lt_succ⟩

def Fin.pred : (i : Fin n.succ) → i ≠ Fin.zero → Fin n
  | ⟨i, h⟩, hi => ⟨i.pred, Nat.pred_lt_pred (hi ∘ @Fin.eq_of_val_eq _ _ Fin.zero) h⟩

theorem Fin.succ_pred : ∀ {i} {h : i ≠ @Fin.zero n}, (Fin.pred i h).succ = i
  | ⟨_ + 1, _⟩, _ => rfl

def Fin.last (n : Nat) : Fin n.succ :=
  ⟨n, Nat.lt.base n⟩

def Fin.castSucc : Fin n → Fin n.succ
  | ⟨i, h⟩ => ⟨i, Nat.lt.step h⟩

instance : ∀ {n} (p : Fin n → Prop) [DecidablePred p], Decidable (∃ i, p i)
  | 0, _, _ => isFalse λ ⟨i, _⟩ => i.elim0
  | n + 1, p, _ =>
    if hl : p (Fin.last n)
    then isTrue ⟨Fin.last n, hl⟩
    else have : DecidablePred (p ∘ Fin.castSucc) := λ i => inferInstanceAs (Decidable (p i.castSucc))
         match instForAllNatForAllFinPropDecidablePredDecidableExists (p ∘ Fin.castSucc) with
           | isTrue h => isTrue (let ⟨i, hp⟩ := h; ⟨i.castSucc, hp⟩)
           | isFalse h => isFalse λ ⟨⟨i, hi⟩, hp⟩ =>
             if hn : Fin.val ⟨i, hi⟩ = n
             then hl (cast (congrArg p <| Fin.eq_of_val_eq hn) hp)
             else h ⟨⟨i, Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ hi) hn⟩, hp⟩

def Fin.foldr : ∀ {n}, (α → β → β) → β → (Fin n → α) → β
  | 0, _, y, _ => y
  | _ + 1, f, y, t => f (t zero) <| foldr f y (t ∘ succ)

def List.ofFun : ∀ {n}, (Fin n → α) → List α
  | 0, _ => []
  | _ + 1, t => t Fin.zero :: ofFun (t ∘ Fin.succ)

theorem List.length_ofFun : ∀ {n} {t : Fin n → α}, (ofFun t).length = n
  | 0, _ => rfl
  | _ + 1, _ => congrArg _ length_ofFun

theorem List.map_ofFun : ∀ {n} {t : Fin n → α}, (ofFun t).map f = ofFun (f ∘ t)
  | 0, _ => rfl
  | _ + 1, _ => congrArg _ map_ofFun

theorem List.foldr_ofFun : ∀ {n} {t : Fin n → α}, (ofFun t).foldr f x = Fin.foldr f x t
  | 0, _ => rfl
  | _ + 1, _ => congrArg _ foldr_ofFun

theorem List.zip_ofFun : ∀ {n} {t₁ : Fin n → α} {t₂ : Fin n → β}, (ofFun t₁).zip (ofFun t₂) = ofFun λ i => (t₁ i, t₂ i)
  | 0, _, _ => rfl
  | _ + 1, _, _ => congrArg _ zip_ofFun

theorem List.zip_ofFun' (h : n₂ = n₁) {t₁ : Fin n₁ → α} {t₂ : Fin n₂ → β} : (ofFun t₁).zip (ofFun t₂) = ofFun λ i => (t₁ <| cast (congrArg Fin h) i, t₂ i) := by
  cases h
  exact zip_ofFun

theorem List.mem_ofFun : ∀ {n} {t : Fin n → α}, (x ∈ ofFun t) = ∃ i, x = t i
  | 0, _ => propext ⟨λ h => nomatch h, λ ⟨i, _⟩ => i.elim0⟩
  | _ + 1, t =>
    have : (x ∈ ofFun (t ∘ Fin.succ)) = _ := mem_ofFun
    propext ⟨by intro h; cases h with
                 | head => exact ⟨Fin.zero, rfl⟩
                 | tail _ h => let ⟨i, hi⟩ := this.mp h; exact ⟨i.succ, hi⟩,
     λ ⟨i, hi⟩ =>
       (if h0 : i = Fin.zero
        then h0 ▸ hi ▸ Mem.head x _
        else Mem.tail _ <| this.mpr ⟨i.pred h0, (Fin.succ_pred ▸ hi : x = t (i.pred h0).succ)⟩
        : x ∈ t Fin.zero :: ofFun (t ∘ Fin.succ))⟩

theorem List.foldr_map : {l : List α} → (l.map g).foldr f x = l.foldr (f ∘ g) x
  | [] => rfl
  | _ :: _ => congrArg _ foldr_map

theorem Fin.foldr_map : ∀ {n} {t : Fin n → α}, foldr f x (g ∘ t) = foldr (f ∘ g) x t
  | 0, _ => rfl
  | _ + 1, _ => congrArg _ foldr_map

theorem List.foldr_append : ∀ {l₁ : List α}, (l₁ ++ l₂).foldr f x = l₁.foldr f (l₂.foldr f x)
  | [] => rfl
  | _ :: _ => congrArg (f _) foldr_append

theorem List.map_fst_zip : {l₁ : List α} → {l₂ : List β} → l₁.length ≤ l₂.length → (l₁.zip l₂).map Prod.fst = l₁
  | [], _, _ => rfl
  | _ :: _, _ :: _, h => congrArg _ <| map_fst_zip <| Nat.le_of_succ_le_succ h

theorem List.length_union_ge [DecidableEq α] : {l₁ l₂ : List α} → (l₁ ∪ l₂).length ≥ l₂.length
  | [], _ => Nat.le.refl
  | x :: xs, l => (
    if h : x ∈ xs ∪ l
    then if_pos h ▸ length_union_ge
    else if_neg h ▸ (length_union_ge).step
    : length (if x ∈ xs ∪ l then xs ∪ l else x :: (xs ∪ l)) ≥ length l)

theorem List.nodup_insert [DecidableEq α] {l : List α} (h : l.Nodup) : (l.insert x).Nodup :=
  (if hx : x ∈ l
   then if_pos hx ▸ h
   else if_neg hx ▸ Pairwise.cons (λ _ hy hxy => hx <| hxy ▸ hy) h
   : (if x ∈ l then l else x :: l).Nodup)

theorem List.nodup_remove [DecidableEq α] : {l : List α} → l.Nodup → (l.remove x).Nodup
  | [], _ => Pairwise.nil
  | y :: _, Pairwise.cons h₁ h₂ =>
    (if h : x = y
     then if_pos h ▸ nodup_remove h₂
     else if_neg h ▸ Pairwise.cons (λ z hz => h₁ z <| mem_of_mem_remove hz) (nodup_remove h₂)
     : (if x = y then remove x _ else y :: remove x _).Nodup)

theorem List.nodup_union [DecidableEq α] (h : l.Nodup) : {l' : List α} → (l' ∪ l).Nodup
  | [] => h
  | _ :: _ => nodup_insert <| nodup_union h

theorem List.nil_union' [DecidableEq α] : {l : List α} → l.Nodup → l.union [] = l
  | [], _ => rfl
  | h :: t, Pairwise.cons h₁ h₂ => ((nil_union' h₂).symm ▸ if_neg (λ h' => h₁ h h' rfl) ▸ rfl : (if h ∈ t.union [] then _ else h :: t.union []) = h :: t)

theorem List.union_assoc [DecidableEq α] {l₁ l₂ l₃ : List α} : l₁ ∪ l₂ ∪ l₃ = l₁ ∪ (l₂ ∪ l₃) := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
  cases l₂ with
  | nil =>
    show (xs.union []).insert x ∪ l₃ = (xs.union l₃).insert x
    by_cases hx : x ∈ xs <;> simp [insert, hx]
    exact ih
    show ((xs.union []).union l₃).insert x = if x ∈ l₃ then xs ∪ l₃ else x :: (xs ∪ l₃)
    simp [insert, hx]
    show (if x ∈ l₃ then xs ∪ [] ∪ l₃ else x :: (xs ∪ [] ∪ l₃)) = if x ∈ l₃ then xs ∪ l₃ else x :: (xs ∪ l₃)
    rw [ih]
    rfl
  | cons y ys =>
  show ((x :: xs).union (y :: ys)) ∪ l₃ = ((x :: xs).union (y :: ys ∪ l₃))
  by_cases hxxs : x ∈ xs <;> simp [insert, hxxs]
  exact ih
  show (if x = y ∨ x ∈ ys then xs ∪ y :: ys else x :: (xs ∪ y :: ys)) ∪ l₃ = if x ∈ (y :: ys).union l₃ then xs ∪ (y :: ys ∪ l₃) else x :: (xs ∪ (y :: ys ∪ l₃))
  by_cases hxy : x = y <;> simp [hxy]
  exact ih
  by_cases hxys : x ∈ ys <;> simp [hxys]
  exact ih
  show (x :: (xs.union (y :: ys))).union l₃ = if x ∈ l₃ then xs ∪ (y :: ys ∪ l₃) else x :: (xs ∪ (y :: ys ∪ l₃))
  simp [insert, hxxs, hxy, hxys]
  by_cases hx : x ∈ l₃ <;> simp [hx] <;> exact ih

theorem List.sum_append : ∀ {l₁ : List Nat}, (l₁ ++ l₂).foldr Nat.add 0 = l₁.foldr Nat.add 0 + l₂.foldr Nat.add 0
  | [] => (Nat.zero_add _).symm
  | _ :: _ => Nat.add_assoc _ _ _ ▸ congrArg _ sum_append

theorem List.union_append [DecidableEq α] : ∀ {l₁ : List (List α)}, (l₁ ++ l₂).foldr List.union [] = l₁.foldr List.union [] ∪ l₂.foldr List.union []
  | [] => rfl
  | _ :: _ => List.union_assoc ▸ congrArg _ union_append

theorem List.nodup_singleton : [x].Nodup :=
  Pairwise.cons (λ _ h => nomatch h) Pairwise.nil

theorem List.length_remove [DecidableEq α] : {l : List α} → (l.remove x).length ≤ l.length
  | [] => Nat.le.refl
  | y :: xs =>
    (if h : x = y
     then if_pos h ▸ Nat.le.step length_remove
     else if_neg h ▸ Nat.succ_le_succ length_remove
     : (if x = y then xs.remove x else y :: xs.remove x).length ≤ xs.length.succ)

theorem List.length_remove' [DecidableEq α] {l : List α} : x ∈ l → (l.remove x).length < l.length
  | Mem.head _ l => (if_pos rfl ▸ Nat.succ_le_succ length_remove : (if x = x then l.remove x else x :: l.remove x).length.succ ≤ l.length.succ)
  | Mem.tail y h' =>
    (if h : x = y
     then if_pos h ▸ Nat.lt.step (length_remove' h')
     else if_neg h ▸ Nat.succ_lt_succ (length_remove' h')
     : (if x = y then remove x _ else y :: remove x _).length < (length _).succ)

theorem List.length_remove'' [DecidableEq α] {l : List α} : x ∈ l → l.Nodup → (l.remove x).length + 1 = l.length
  | Mem.head _ l, Pairwise.cons h _ => (if_pos rfl ▸ (remove_eq_of_not_mem λ h' => h x h' rfl).symm ▸ rfl : (if x = x then l.remove x else x :: l.remove x).length.succ = l.length.succ)
  | Mem.tail y h', Pairwise.cons h₁ h₂ =>
    (if h : x = y
     then (h₁ x h' h.symm).elim
     else if_neg h ▸ congrArg Nat.succ (length_remove'' h' h₂)
     : (if x = y then remove x _ else y :: remove x _).length.succ = (length _).succ)

theorem List.length_subset [DecidableEq α] : ∀ {l : List α}, l.Nodup → l ⊆ l' → l.length ≤ l'.length
  | [], _, _ => Nat.zero_le _
  | x :: xs, Pairwise.cons h₁ h₂, h =>
    let ⟨hl, hr⟩ := cons_subset.mp h
    have : xs ⊆ l'.remove x := λ y hy => mem_remove_iff.mpr ⟨hr hy, (h₁ y hy).symm⟩
    Nat.le_trans (Nat.succ_le_succ <| length_subset h₂ this) <| length_remove' hl

theorem List.exists_of_not_subset [DecidableEq α] : {l : List α} → ¬l ⊆ l' → ∃ x ∈ l, x ∉ l'
  | [], h => (h λ _ h' => nomatch h').elim
  | hd :: _, h =>
    if h' : hd ∈ l'
    then let ⟨x, hx₁, hx₂⟩ := exists_of_not_subset <| h ∘ cons_subset.mpr ∘ And.intro h'; ⟨x, Mem.tail hd hx₁, hx₂⟩
    else ⟨hd, Mem.head hd _, h'⟩

theorem List.length_subset' [DecidableEq α] {l l' : List α} (hl : l.Nodup) (h₁ : l ⊆ l') (h₂ : ¬l' ⊆ l) : l.length < l'.length :=
  let ⟨x, hx₁, hx₂⟩ := exists_of_not_subset h₂
  length_subset (Pairwise.cons (λ y hy (hxy : x = y) => hx₂ (hxy ▸ hy)) hl) <| cons_subset.mpr ⟨hx₁, h₁⟩

theorem List.length_eq_of_subset [DecidableEq α] : {l₁ l₂ : List α} → l₁ ⊆ l₂ → l₂ ⊆ l₁ → l₁.Nodup → l₂.Nodup → l₁.length = l₂.length
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => nomatch h <| Mem.head _ _
  | x :: xs, ys, h₁, h₂, Pairwise.cons hx₁ hx₂, hy =>
    have : xs.length = (ys.remove x).length := length_eq_of_subset
      (λ y hy => mem_remove_iff.mpr ⟨(cons_subset.mp h₁).right hy, (hx₁ y hy).symm⟩)
      (λ _ hy =>
        let ⟨hy₁, hy₂⟩ := mem_remove_iff.mp hy
        match h₂ hy₁ with
        | Mem.head _ _ => (hy₂ rfl).elim
        | Mem.tail _ h => h)
      hx₂ (nodup_remove hy)
    (this.symm ▸ length_remove'' (cons_subset.mp h₁).left hy : xs.length + 1 = ys.length)

theorem List.length_union_eq_of [DecidableEq α] {l₁ l₂ l : List α} (hl : l.Nodup) (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₁) : (l₁ ∪ l).length = (l₂ ∪ l).length := by
  have h : l₁ ∪ l ⊆ l₂ ∪ l
  intro x hx
  apply mem_union_iff.mpr
  cases mem_union_iff.mp hx with
  | inr hx => exact Or.inr hx
  | inl hx => exact Or.inl <| h₁ hx
  have h' : l₂ ∪ l ⊆ l₁ ∪ l
  intro x hx
  apply mem_union_iff.mpr
  cases mem_union_iff.mp hx with
  | inr hx => exact Or.inr hx
  | inl hx => exact Or.inl <| h₂ hx
  exact length_eq_of_subset h h' (nodup_union hl) (nodup_union hl)

inductive Term (F : Nat → Type _) (V : Type _)
  | var (x : V)
  | app (n) (f : F n) (t : (i : Fin n) → Term F V)

variable {F}

def Term.subst (σ : V → Term F W) : Term F V → Term F W
  | var x => σ x
  | app n f t => app n f λ i => (t i).subst σ

def Term.mg (t : Term F V) (u : Term F W) : Prop :=
  ∃ σ, t.subst σ = u

def Term.subst.mg (σ : V → Term F W) (τ : V → Term F U) : Prop :=
  ∀ t, (subst σ t).mg (subst τ t)

def Term.contains (x : V) : Term F V → Prop
  | var y => y = x
  | app _ _ t => ∃ i, (t i).contains x

theorem Term.subst_var : (t : Term F V) → t.subst var = t
  | var _ => rfl
  | app _ _ t => congrArg _ <| funext λ i => subst_var (t i)

theorem Term.var_mg (σ : V → Term F W) : Term.subst.mg var σ :=
  λ t => ⟨σ, congrArg (subst σ) (subst_var t)⟩

open Term (var app)

def Term.apps : Term F V → Nat
  | var _ => 0
  | app _ _ t => Fin.foldr Nat.add 0 (λ i => (t i).apps) + 1

variable {V} [DecidableEq V]

def Term.subst' (x : V) (t : Term F V) : Term F V → Term F V :=
  Term.subst λ y => if y = x then t else var y

theorem Term.subst'_notin : {t' : Term F V} → ¬t'.contains x → Term.subst' x t t' = t'
  | var _, h => if_neg h
  | app _ _ _, h => congrArg _ <| funext λ i => subst'_notin λ h' => h ⟨i, h'⟩

instance : (t : Term F V) → Decidable (t.contains x)
  | var y => inferInstanceAs <| Decidable (y = x)
  | app _ _ t =>
    have : ∀ i, Decidable ((t i).contains x) := λ i => instForAllTermDecidableContains (t i)
    inferInstanceAs <| Decidable (∃ i, (t i).contains x)

def Term.vars : Term F V → List V
  | var x => [x]
  | app _ _ t => Fin.foldr List.union [] λ i => (t i).vars

theorem nodup_foldr_union : ∀ {n} {t : Fin n → List V}, (Fin.foldr List.union [] t).Nodup
  | 0, _ => List.Pairwise.nil
  | _ + 1, _ => List.nodup_union nodup_foldr_union

theorem nodup_foldr_union' : {l : List (List V)} → (l.foldr List.union []).Nodup
  | [] => List.Pairwise.nil
  | _ :: _ => List.nodup_union nodup_foldr_union'

theorem Term.nodup_vars : {t : Term F V} → t.vars.Nodup
  | var _ => List.nodup_singleton
  | app _ _ _ => nodup_foldr_union

theorem le_foldr_sum (t : Fin n → Nat) : t i ≤ Fin.foldr Nat.add 0 t := by
  cases i with | _ i hi =>
  induction i generalizing n with
  | zero =>
    cases n with
    | zero => cases hi
    | succ n => apply Nat.le_add_right
  | succ i ih =>
  cases n with
  | zero => cases hi
  | succ n =>
  transitivity
  exact ih (t ∘ Fin.succ) (Nat.lt_of_succ_lt_succ hi)
  apply Nat.le_add_left

theorem mem_foldr_union_of_mem {t : Fin n → List V} : x ∈ t i → x ∈ Fin.foldr List.union [] t := by
  intro h
  cases i with | _ i hi =>
  induction i generalizing n with
  | zero =>
    cases n with
    | zero => cases hi
    | succ n =>
    apply List.mem_union_iff.mpr <| Or.inl h
  | succ i ih =>
  cases n with
  | zero => cases hi
  | succ n =>
  apply List.mem_union_iff.mpr ∘ Or.inr
  exact ih (Nat.lt_of_succ_lt_succ hi) h

theorem mem_of_mem_foldr_union {t : Fin n → List V} : x ∈ Fin.foldr List.union [] t → ∃ i, x ∈ t i := by
  intro h
  induction n with
  | zero =>
    cases h
  | succ n ih =>
  have := List.mem_union_iff.mp h
  cases this with
  | inl hm =>
    exact ⟨_, hm⟩
  | inr hm =>
  cases ih hm with | _ i hi =>
  exact ⟨_, hi⟩

theorem Term.in_vars_of_contains {x : V} : {t : Term F V} → t.contains x → x ∈ t.vars
  | var _, rfl => List.Mem.head x []
  | app _ _ _, ⟨_, h⟩ => mem_foldr_union_of_mem <| in_vars_of_contains h

theorem Term.contains_of_in_vars {x : V} : {t : Term F V} → x ∈ t.vars → t.contains x
  | var _, List.Mem.head _ _ => rfl
  | app _ _ _, h => let ⟨i, hi⟩ := mem_of_mem_foldr_union h; ⟨i, contains_of_in_vars hi⟩

theorem Term.subst_vars {t t' : Term F V} : (Term.subst' x t t').vars ⊆ t'.vars.remove x ∪ t.vars := by
  intro y hy
  induction t' with
  | var z =>
    by_cases hzx : z = x <;> simp [subst', subst, hzx] at hy
    exact List.mem_union_iff.mpr <| Or.inr hy
    apply List.mem_union_iff.mpr ∘ Or.inl ∘ List.mem_remove_iff.mpr ∘ And.intro hy
    simp [vars] at hy
    exact hy.symm ▸ hzx
  | app n f t ih =>
    cases contains_of_in_vars hy with | _ i hi =>
    cases List.mem_union_iff.mp <| ih i <| in_vars_of_contains hi with
    | inr h' =>
      exact List.mem_union_iff.mpr <| Or.inr h'
    | inl h' =>
    cases List.mem_remove_iff.mp h' with | _ h₁ h₂ =>
    apply List.mem_union_iff.mpr <| Or.inl <| List.mem_remove_iff.mpr ⟨_, h₂⟩
    apply in_vars_of_contains
    exact ⟨i, contains_of_in_vars h₁⟩

private abbrev List.subst (x : V) (t : Term F V) : List (Term F V × Term F V) → List (Term F V × Term F V) :=
  map <| Prod.map (Term.subst' x t) (Term.subst' x t)

private abbrev replace (x : V) (t : Term F V) (σ : V → Term F V) (y : V) : Term F V :=
  if y = x then t.subst σ else σ y

private theorem subst_replace : {t' : Term F V} → t'.subst (replace x t σ) = (Term.subst' x t t').subst σ
  | var y => by by_cases h : y = x <;> simp [replace, Term.subst', Term.subst, h]
  | app _ _ _ => congrArg _ <| funext λ i => subst_replace

theorem subst_subst' (h : t.subst σ = σ x) : (t' : Term F V) → (Term.subst' x t t').subst σ = t'.subst σ
  | var y =>
    (if h' : y = x
     then if_pos h' ▸ h' ▸ h
     else if_neg h' ▸ rfl
     : (if y = x then t else var y).subst σ = σ y)
  | app _ _ _ => congrArg (app _ _) <| funext λ i => subst_subst' h _

theorem replace_mg {x : V} (h : t.subst σ = σ x) (h' : Term.subst.mg σ' σ) : Term.subst.mg (replace x t σ') σ :=
  λ t' => subst_replace ▸ subst_subst' h t' ▸ h' (Term.subst' x t t')

private abbrev List.vars' : List (Term F V × Term F V) → List V :=
  foldr (λ (t₁, t₂) => (t₁.vars.union t₂.vars).union) []

theorem List.subst_vars' {G : List (Term F V × Term F V)} : (G.subst x t).vars' ⊆ G.vars'.remove x ∪ t.vars := by
  intro y hy
  induction G with
  | nil => simp [subst] at hy
  | cons hd tl ih =>
  apply mem_union_iff.mpr
  cases mem_union_iff.mp hy with
  | inr h' =>
    specialize ih h'
    cases mem_union_iff.mp ih with
    | inr ih' => exact Or.inr ih'
    | inl ih' =>
    have := mem_remove_iff.mp ih'
    exact Or.inl <| mem_remove_iff.mpr ⟨mem_union_iff.mpr <| Or.inr this.left, this.right⟩
  | inl h' =>
  cases mem_union_iff.mp h' with
  | inl h' =>
    cases mem_union_iff.mp <| Term.subst_vars h' with
    | inr h' => exact Or.inr h'
    | inl h' =>
    have := mem_remove_iff.mp h'
    exact Or.inl <| mem_remove_iff.mpr ⟨mem_union_iff.mpr <| Or.inl <| mem_union_iff.mpr <| Or.inl this.left, this.right⟩
  | inr h' =>
    cases mem_union_iff.mp <| Term.subst_vars h' with
    | inr h' => exact Or.inr h'
    | inl h' =>
    have := mem_remove_iff.mp h'
    exact Or.inl <| mem_remove_iff.mpr ⟨mem_union_iff.mpr <| Or.inl <| mem_union_iff.mpr <| Or.inr this.left, this.right⟩

theorem List.nodup_vars' {G : List (Term F V × Term F V)} : G.vars'.Nodup :=
  (foldr_map.symm ▸ nodup_foldr_union' : Nodup (G.foldr (List.union ∘ λ (t₁, t₂) => t₁.vars.union t₂.vars) []))

theorem Term.occurs_check (h : (app n f t).contains x) : σ x ≠ (app n f t).subst σ := by
  cases h with | _ i h =>
  suffices : (σ x).apps ≤ ((t i).subst σ).apps
  exact λ h => rfl |> h ▸ (Nat.ne_of_lt <| Nat.lt_succ_of_le <| trans this <| le_foldr_sum _)
  generalize ht' : t i = t'
  rw [ht'] at h
  clear ht' t
  induction t' with
  | var y =>
    cases h
    exact Nat.le.refl
  | app n f t ih =>
  let ⟨i, h⟩ := h
  exact Nat.le.step <| trans (ih i h) <| le_foldr_sum _

private abbrev List.vars : List (Term F V × Term F V) → Nat :=
  length ∘ vars'

private abbrev List.apps : List (Term F V × Term F V) → Nat :=
  foldr Nat.add 0 ∘ map λ (t, _) => t.apps

private theorem assign_vars₁ {x : V} {t : Term F V} (h : ¬t.contains x) : (G.subst x t).vars < ((t, var x) :: G).vars := by
  apply Nat.lt_trans'
  exact List.length_subset List.nodup_vars' List.subst_vars'
  show (G.vars'.remove x ∪ t.vars).length < (t.vars ∪ [x] ∪ G.vars').length
  have h₁ : G.vars'.remove x ∪ t.vars ⊆ t.vars ∪ [x] ∪ G.vars'
  intro y hy
  apply List.mem_union_iff.mpr
  cases List.mem_union_iff.mp hy with
  | inl hy => exact Or.inr <| List.mem_of_mem_remove hy
  | inr hy => exact Or.inl <| List.mem_union_iff.mpr <| Or.inl hy
  have h₂ : ¬t.vars ∪ [x] ∪ G.vars' ⊆ G.vars'.remove x ∪ t.vars
  intro h'
  apply h
  apply Term.contains_of_in_vars
  cases List.mem_union_iff.mp <| h' <| List.mem_union_iff.mpr <| Or.inl <| List.mem_union_iff.mpr <| Or.inr <| List.mem_singleton_self x with
  | inl h' => exact ((List.mem_remove_iff.mp h').right rfl).elim
  | inr h' => exact h'
  exact List.length_subset' (List.nodup_union Term.nodup_vars) h₁ h₂

private theorem assign_vars₂ {x : V} {t : Term F V} (h : ¬t.contains x) : (G.subst x t).vars < ((var x, t) :: G).vars := by
  apply Nat.lt_trans'
  exact List.length_subset List.nodup_vars' List.subst_vars'
  show (G.vars'.remove x ∪ t.vars).length < (t.vars.insert x ∪ G.vars').length
  have h₁ : G.vars'.remove x ∪ t.vars ⊆ t.vars.insert x ∪ G.vars'
  intro y hy
  apply List.mem_union_iff.mpr
  cases List.mem_union_iff.mp hy with
  | inl hy => exact Or.inr <| List.mem_of_mem_remove hy
  | inr hy => exact Or.inl <| List.mem_insert_iff.mpr <| Or.inr hy
  have h₂ : ¬t.vars.insert x ∪ G.vars' ⊆ G.vars'.remove x ∪ t.vars
  intro h'
  apply h
  apply Term.contains_of_in_vars
  cases List.mem_union_iff.mp <| h' <| List.mem_union_iff.mpr <| Or.inl <| List.mem_insert_self x _ with
  | inl h' => exact ((List.mem_remove_iff.mp h').right rfl).elim
  | inr h' => exact h'
  exact List.length_subset' (List.nodup_union Term.nodup_vars) h₁ h₂

private theorem unwrap_vars {t₁ t₂ : Fin n → Term F V} : ((List.ofFun t₁).zip (List.ofFun t₂) ++ G).vars = ((app n f₁ t₁, app n f₂ t₂) :: G).vars := by
  show (((List.ofFun t₁).zip (List.ofFun t₂) ++ G).foldr (List.union ∘ λ (t₁, t₂) => t₁.vars.union t₂.vars) _).length = ((app n f₁ t₁).vars ∪ (app n f₂ t₂).vars ∪ G.vars').length
  rw [← List.foldr_map, List.map_append, List.union_append, List.foldr_map, List.foldr_map]
  show (((List.ofFun t₁).zip (List.ofFun t₂)).vars' ∪ G.vars').length = _
  apply List.length_union_eq_of List.nodup_vars'

  intro x hx
  rw [List.vars', List.zip_ofFun, List.foldr_ofFun] at hx
  have : x ∈ Fin.foldr List.union [] ((λ (t₁, t₂) => t₁.vars.union t₂.vars) ∘ λ i => (t₁ i, t₂ i)) := Fin.foldr_map ▸ hx
  let ⟨i, hi⟩ := mem_of_mem_foldr_union this
  apply List.mem_union_iff.mpr
  cases List.mem_union_iff.mp hi with
  | inl hi => exact Or.inl <| mem_foldr_union_of_mem hi
  | inr hi => exact Or.inr <| mem_foldr_union_of_mem hi

  intro x hx
  rw [List.vars', List.zip_ofFun, List.foldr_ofFun]
  show x ∈ Fin.foldr (List.union ∘ _) [] _
  rw [← Fin.foldr_map]
  simp
  cases List.mem_union_iff.mp hx with
  | inl hx =>
    let ⟨i, hi⟩ := mem_of_mem_foldr_union hx
    exact mem_foldr_union_of_mem <| List.mem_union_iff.mpr <| Or.inl hi
  | inr hx =>
    let ⟨i, hi⟩ := mem_of_mem_foldr_union hx
    exact mem_foldr_union_of_mem <| List.mem_union_iff.mpr <| Or.inr hi

private theorem unwrap_apps {t₁ t₂ : Fin n → Term F V} : ((List.ofFun t₁).zip (List.ofFun t₂) ++ G).apps < ((app n f₁ t₁, app n f₂ t₂) :: G).apps := by
  show (((List.ofFun t₁).zip (List.ofFun t₂) ++ G).map _).foldr _ _ < _
  rw [List.map_append, List.sum_append]
  apply Nat.add_lt_add_right
  show (((List.ofFun t₁).zip (List.ofFun t₂)).map (Term.apps ∘ Prod.fst)).foldr _ _ < Fin.foldr _ _ (Term.apps ∘ t₁) + 1
  rw [← List.map_map, List.map_fst_zip <| List.length_ofFun ▸ List.length_ofFun ▸ Nat.le.refl, List.map_ofFun, List.foldr_ofFun]
  apply Nat.lt_succ_self

def unify [∀ n, DecidableEq (F n)] : List (Term F V × Term F V) → Option (V → Term F V)
  | [] => some var
  | (var x, var y) :: G => let G₁ := (var x, var y) :: G
    if hxy : x = y
    then
         have h₁ : G.vars ≤ G₁.vars := List.length_union_ge
         have h₂ : G.apps ≤ G₁.apps := Nat.le_of_eq (Nat.zero_add _).symm
         have h₃ : G.length < G₁.length := G.length.lt_succ_self
         have := Prod.Lex.right' _ h₁ <| Prod.Lex.right' _ h₂ h₃
         unify G
    else let G' := G.subst y (var x)
         have : G'.vars < G₁.vars := assign_vars₁ hxy
         (unify G').map (replace y (var x))
  | (var x, t) :: G => let G₁ := (var x, t) :: G
    if hxt : t.contains x
    then none
    else let G' := G.subst x t
         have : G'.vars < G₁.vars := assign_vars₂ hxt
         (unify G').map (replace x t)
  | (t, var x) :: G => let G₁ := (t, var x) :: G
    if hxt : t.contains x
    then none
    else let G' := G.subst x t
         have : G'.vars < G₁.vars := assign_vars₁ hxt
         (unify G').map (replace x t)
  | (app n₁ f₁ t₁, app n₂ f₂ t₂) :: G => let G₁ := (app n₁ f₁ t₁, app n₂ f₂ t₂) :: G
    if hn : n₁ = n₂
    then if hf : cast (congrArg F hn) f₁ = f₂
         then let G' := (List.ofFun t₁).zip (List.ofFun t₂) ++ G
              have h₁ : G'.vars = G₁.vars := by cases hn; exact unwrap_vars
              have h₂ : G'.apps < G₁.apps := by cases hn; exact unwrap_apps
              have : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (G'.vars, _, _) (G₁.vars, G₁.apps, G₁.length) := h₁ ▸ (Prod.Lex.right _ <| Prod.Lex.left G'.length G₁.length h₂)
              unify G'
         else none
    else none
termination_by _ G => (G.vars, G.apps, G.length)
decreasing_by first | decreasing_tactic | assumption

theorem unify_soundness [∀ n, DecidableEq (F n)] : {G : List (Term F V × Term F V)} → unify G = some σ → ∀ t ∈ G, t.fst.subst σ = t.snd.subst σ
  | [], _, _, ht => nomatch ht
  | (var x, var y) :: G, h, t, ht => let G₁ := (var x, var y) :: G; by
    by_cases hxy : x = y <;> simp [unify, hxy] at h
    case pos =>
      cases ht with
      | head => exact hxy ▸ rfl
      | tail _ ht =>
        have h₁ : G.vars ≤ G₁.vars := List.length_union_ge
        have h₂ : G.apps ≤ G₁.apps := Nat.le_of_eq (Nat.zero_add _).symm
        have h₃ : G.length < G₁.length := G.length.lt_succ_self
        have := Prod.Lex.right' _ h₁ <| Prod.Lex.right' _ h₂ h₃
        exact unify_soundness h t ht
    case neg =>
      let ⟨σ', hσ₁, hσ₂⟩ := h
      cases ht with
      | head => simp [← hσ₂, Term.subst, replace]
      | tail _ ht =>
        cases hσ₂
        rw [subst_replace, subst_replace]
        let G' := G.subst y (var x)
        have : G'.vars < G₁.vars := assign_vars₁ hxy
        exact unify_soundness hσ₁ _ <| List.mem_map_of_mem (Prod.map (Term.subst' y (var x)) (Term.subst' y (var x))) ht
  | (var x, app n₁ f₁ t₁) :: G, h, t, ht => let t := app n₁ f₁ t₁; let G₁ := (var x, t) :: G; by
    by_cases hxt : t.contains x <;> simp [unify, hxt] at h
    let ⟨σ', hσ₁, hσ₂⟩ := h
    cases ht with
    | head =>
      rw [← hσ₂, subst_replace, subst_replace, Term.subst'_notin hxt]
      simp [Term.subst', Term.subst]
    | tail _ ht =>
      cases hσ₂
      rw [subst_replace, subst_replace]
      let G' := G.subst x t
      have : G'.vars < G₁.vars := assign_vars₂ hxt
      exact unify_soundness hσ₁ _ <| List.mem_map_of_mem (Prod.map (Term.subst' x t) (Term.subst' x t)) ht
  | (app n₁ f₁ t₁, var x) :: G, h, t, ht => let t := app n₁ f₁ t₁; let G₁ := (t, var x) :: G; by
    by_cases hxt : t.contains x <;> simp [unify, hxt] at h
    let ⟨σ', hσ₁, hσ₂⟩ := h
    cases ht with
    | head =>
      rw [← hσ₂, subst_replace, subst_replace, Term.subst'_notin hxt]
      simp [Term.subst', Term.subst]
    | tail _ ht =>
      cases hσ₂
      rw [subst_replace, subst_replace]
      let G' := G.subst x t
      have : G'.vars < G₁.vars := assign_vars₁ hxt
      exact unify_soundness hσ₁ _ <| List.mem_map_of_mem (Prod.map (Term.subst' x t) (Term.subst' x t)) ht
  | (app n₁ f₁ t₁, app n₂ f₂ t₂) :: G, h, t, ht => let G₁ := (app n₁ f₁ t₁, app n₂ f₂ t₂) :: G; by
    by_cases hn : n₁ = n₂ <;> simp [unify, hn] at h
    by_cases hf : cast (congrArg F hn) f₁ = f₂ <;> simp [cast_eq, hf] at h
    let G' := (List.ofFun t₁).zip (List.ofFun t₂) ++ G
    have h₁ : G'.vars = G₁.vars := by cases hn; exact unwrap_vars
    have h₂ : G'.apps < G₁.apps := by cases hn; exact unwrap_apps
    have : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (G'.vars, _, _) (G₁.vars, G₁.apps, G₁.length) := h₁ ▸ (Prod.Lex.right _ <| Prod.Lex.left G'.length G₁.length h₂)
    cases ht with
    | tail _ ht => exact unify_soundness h t (List.mem_append_of_mem_right _ ht)
    | head =>
      simp [Term.subst, hn, heq_of_cast_eq (congrArg F hn) hf]
      apply heq_of_cast_eq <| hn ▸ rfl
      funext i
      apply Eq.trans
      show _ = (t₁ <| cast (congrArg Fin hn.symm) i).subst σ
      cases hn
      exact rfl
      exact unify_soundness h (t₁ <| cast (congrArg Fin hn.symm) i, t₂ i) (List.zip_ofFun' hn.symm ▸ List.mem_append_of_mem_left _ (List.mem_ofFun ▸ ⟨i, rfl⟩))
termination_by _ G _ _ _ => (G.vars, G.apps, G.length)
decreasing_by first | decreasing_tactic | assumption

theorem unify_completeness [∀ n, DecidableEq (F n)] : {G : List (Term F V × Term F V)} → (∀ t ∈ G, t.fst.subst σ = t.snd.subst σ) → ∃ σ', unify G = some σ' ∧ Term.subst.mg σ' σ
  | [], _ => ⟨var, rfl, Term.var_mg σ⟩
  | (var x, var y) :: G, h => let G₁ := (var x, var y) :: G; by
    by_cases hxy : x = y <;> simp [unify, hxy]
    case pos =>
      have h₁ : G.vars ≤ G₁.vars := List.length_union_ge
      have h₂ : G.apps ≤ G₁.apps := Nat.le_of_eq (Nat.zero_add _).symm
      have h₃ : G.length < G₁.length := G.length.lt_succ_self
      have := Prod.Lex.right' _ h₁ <| Prod.Lex.right' _ h₂ h₃
      exact unify_completeness λ t => h t ∘ List.Mem.tail _
    case neg =>
      let G' := G.subst y (var x)
      have : G'.vars < G₁.vars := assign_vars₁ hxy
      have h₁ := h _ <| List.Mem.head _ G
      have h' : ∀ t ∈ G', t.fst.subst σ = t.snd.subst σ
      case h' =>
        intro t ht
        let ⟨t', ht', ht⟩ := List.mem_map.mp ht
        simp [ht]
        rw [subst_subst' h₁ t'.fst, subst_subst' h₁ t'.snd]
        exact h t' <| List.Mem.tail _ ht'
      let ⟨σ', hσ₁, hσ₂⟩ := unify_completeness h'
      exact ⟨_, ⟨σ', hσ₁, rfl⟩, replace_mg h₁ hσ₂⟩
  | (var x, app n₁ f₁ t₁) :: G, h => let t := app n₁ f₁ t₁; let G₁ := (var x, t) :: G; by
    by_cases hxt : t.contains x <;> simp [unify, hxt]
    case pos => exact Term.occurs_check hxt <| h (var x, t) <| List.Mem.head _ G
    case neg =>
      let G' := G.subst x t
      have : G'.vars < G₁.vars := assign_vars₂ hxt
      have h₁ := Eq.symm <| h _ <| List.Mem.head _ G
      have h' : ∀ t ∈ G', t.fst.subst σ = t.snd.subst σ
      case h' =>
        intro t ht
        let ⟨t', ht', ht⟩ := List.mem_map.mp ht
        simp [ht]
        rw [subst_subst' h₁ t'.fst, subst_subst' h₁ t'.snd]
        exact h t' <| List.Mem.tail _ ht'
      let ⟨σ', hσ₁, hσ₂⟩ := unify_completeness h'
      exact ⟨_, ⟨σ', hσ₁, rfl⟩, replace_mg h₁ hσ₂⟩
  | (app n₁ f₁ t₁, var x) :: G, h => let t := app n₁ f₁ t₁; let G₁ := (t, var x) :: G; by
    by_cases hxt : t.contains x <;> simp [unify, hxt]
    case pos => exact Term.occurs_check hxt <| Eq.symm <| h (t, var x) <| List.Mem.head _ G
    case neg =>
      let G' := G.subst x t
      have : G'.vars < G₁.vars := assign_vars₁ hxt
      have h₁ := h _ <| List.Mem.head _ G
      have h' : ∀ t ∈ G', t.fst.subst σ = t.snd.subst σ
      case h' =>
        intro t ht
        let ⟨t', ht', ht⟩ := List.mem_map.mp ht
        simp [ht]
        rw [subst_subst' h₁ t'.fst, subst_subst' h₁ t'.snd]
        exact h t' <| List.Mem.tail _ ht'
      let ⟨σ', hσ₁, hσ₂⟩ := unify_completeness h'
      exact ⟨_, ⟨σ', hσ₁, rfl⟩, replace_mg h₁ hσ₂⟩
  | (app n₁ f₁ t₁, app n₂ f₂ t₂) :: G, h => let G₁ := (app n₁ f₁ t₁, app n₂ f₂ t₂) :: G; by
    by_cases hn : n₁ = n₂ <;> simp [unify, hn]
    case neg =>
      specialize h (app n₁ f₁ t₁, app n₂ f₂ t₂) <| List.Mem.head _ G
      simp [Term.subst] at h
      exact hn h.left
    case pos =>
      by_cases hf : cast (congrArg F hn) f₁ = f₂ <;> simp [cast_eq, hf]
      case neg =>
        specialize h (app n₁ f₁ t₁, app n₂ f₂ t₂) <| List.Mem.head _ G
        cases hn
        simp [Term.subst] at h
        exact hf h.left
      case pos =>
        let G' := (List.ofFun t₁).zip (List.ofFun t₂) ++ G
        have h₁ : G'.vars = G₁.vars := by cases hn; exact unwrap_vars
        have h₂ : G'.apps < G₁.apps := by cases hn; exact unwrap_apps
        have : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (G'.vars, _, _) (G₁.vars, G₁.apps, G₁.length) := h₁ ▸ (Prod.Lex.right _ <| Prod.Lex.left G'.length G₁.length h₂)
        apply unify_completeness
        intro t ht
        cases List.mem_append.mp ht with
        | inr ht => exact h t <| List.Mem.tail _ ht
        | inl ht =>
          cases hn
          rw [cast_eq] at hf
          cases hf
          rw [List.zip_ofFun, List.mem_ofFun] at ht
          let ⟨i, ht⟩ := ht
          cases ht
          specialize h _ <| List.Mem.head _ G
          simp [Term.subst] at h
          rw [congrFun h i]
termination_by _ G _ => (G.vars, G.apps, G.length)
decreasing_by first | decreasing_tactic | assumption

/-\===============================================================================\-/

open Std (Format)

namespace Fin

def tail {n : Nat} {α : Fin n.succ → Sort _} (t : ∀ i, α i) : ∀ i : Fin n, α i.succ :=
λ i => t i.succ

protected def reprTuple : ∀ {n} {α : Fin n → Type _} [∀ i, Repr (α i)], (∀ i, α i) → List Format
  | 0, _, _, _ => []
  | _ + 1, _, _, t => repr (t 0) :: Fin.reprTuple (Fin.tail t)

end Fin

instance {n} {α : Fin n → Type _} [∀ i, Repr (α i)] : Repr (∀ i, α i) where
  reprPrec t _ := Format.bracket "(" (Format.joinSep (Fin.reprTuple t) ("," ++ Format.line)) ")"

instance : Repr Format where
  reprPrec f _ := f

protected def Term.repr [∀ n, Repr (F n)] [Repr V] : Term F V → Format
  | var x => repr x
  | app 0 f _ => repr f
  | app _ f t => repr f ++ repr (λ i => Term.repr (t i))

instance [∀ n, Repr (F n)] [Repr V] : Repr (Term F V) where
  reprPrec t _ := t.repr

def V' := Nat

protected def V'.repr (x : V') : String := "?" ++ Nat.repr x

instance : Repr V' where
  reprPrec x _ := x.repr

instance : DecidableEq V' := inferInstanceAs <| DecidableEq Nat

def F' : Nat → Type
  | 0 => Unit
  | 2 => Unit
  | _ => Empty

protected def F'.repr : ∀ {n}, F' n → String
  | 0, () => "o"
  | 2, () => "fn"

instance {n} : Repr (F' n) where
  reprPrec f _ := f.repr

instance : ∀ n, DecidableEq (F' n)
  | 0, (), () => isTrue rfl
  | 2, (), () => isTrue rfl

def var' : Nat → Term F' V' := Term.var

def o : Term F' V' := Term.app 0 () Fin.elim0
def fn (a b : Term F' V') : Term F' V' := Term.app 2 () λ | 0 => a | 1 => b

#eval fn (fn (var' 0) o) (fn o (var' 1))

def L := fn (var' 0) (var' 1)
def R := fn (var' 1) (fn (var' 2) (var' 3))

#eval (unify [(L, R)]).map λ σ => L.subst σ
#eval (unify [(L, R)]).map λ σ => R.subst σ
