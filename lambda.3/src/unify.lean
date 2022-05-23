import data.fin.fin2
import logic.basic
import tactic.interactive

open fin2

-- ▶· := (∘) pure
-- ·◀ := flip (>>=) -- (=<<)
-- ▶·◀ := (<$>)
-- ▶·◀² := (∘) (<*>) ∘ (<$>) -- liftA2

inductive term (n : ℕ)
| ι (x : fin2 n) : term
| leaf : term
| fork (s t : term) : term

open term

@[simp]
def term.bind {m n} : term m → (fin2 m → term n) → term n
| (ι x) f := f x
| leaf f := leaf
| (fork s t) f := fork (s.bind f) (t.bind f)

@[simp]
def term.fish {l m n} (f : fin2 l → term m) (g : fin2 m → term n) : fin2 l → term n :=
λ x, (f x).bind g

local infix ` ⟫= `:55 := term.bind
local infix ` >=> `:55 := term.fish

-- ▷· := (∘) ι
-- ·◁ := flip (⟫=)
-- ·◇· := flip (>=>) -- <=<

@[simp]
theorem term.bind_iota {n} : ∀ (t : term n), t ⟫= ι = t
| (ι x) := rfl
| leaf := rfl
| (fork s t) := congr_arg2 fork s.bind_iota t.bind_iota

@[simp]
theorem term.bind_fish {l m n} (f : fin2 l → term m) (g : fin2 m → term n) : ∀ t, t ⟫= (f >=> g) = t ⟫= f ⟫= g
| (ι x) := rfl
| leaf := rfl
| (fork s t) := congr_arg2 fork s.bind_fish t.bind_fish

@[simp]
theorem term.iota_fish {l m n} (r : fin2 l → fin2 m) (f : fin2 m → term n) (t) : ((ι ∘ r) >=> f) t = f (r t) := rfl

@[simp]
def thin : ∀ {n}, fin2 (n + 1) → fin2 n → fin2 (n + 1)
| n fz y := fs y
| (n + 1) (fs x) fz := fz
| (n + 1) (fs x) (fs y) := fs (thin x y)

@[simp]
lemma thin_fz : ∀ {n} {y : fin2 n}, thin fz y = fs y
| (n + 1) y := rfl

theorem thin_inj : ∀ {n x} {y z : fin2 n}, thin x y = thin x z → y = z
| (n + 1) fz y z h := fs.inj h
| (n + 1) (fs x) fz fz h := rfl
| (n + 1) (fs x) (fs y) (fs z) h := congr_arg fs $ thin_inj (fs.inj h)

@[simp]
theorem thin_nsur : ∀ {n x} {y : fin2 n}, thin x y ≠ x
| (n + 1) (fs x) (fs y) h := thin_nsur (fs.inj h)

theorem thin_sur : ∀ {n} {x y : fin2 (n + 1)}, x ≠ y → ∃ y', thin x y' = y
| n fz fz h := absurd rfl h
| (n + 1) (fs x) fz h := ⟨fz, rfl⟩
| (n + 1) fz (fs y) h := ⟨y, rfl⟩
| (n + 1) (fs x) (fs y) h := let ⟨y', h'⟩ := thin_sur (h ∘ congr_arg fs) in ⟨fs y', congr_arg fs h'⟩

@[simp]
def thick : ∀ {n}, fin2 (n + 1) → fin2 (n + 1) → option (fin2 n)
| n fz fz := none
| n fz (fs y) := some y
| (n + 1) (fs x) fz := some fz
| (n + 1) (fs x) (fs y) := fs <$> thick x y

@[simp]
lemma thick_fz_fz : ∀ {n}, @thick n fz fz = none
| 0 := rfl
| (n + 1) := rfl

@[simp]
lemma thick_fz_fs : ∀ {n} {y : fin2 n}, thick fz (fs y) = some y
| 0 y := rfl
| (n + 1) y := rfl

@[simp]
theorem thick_irrefl : ∀ {n} (x : fin2 (n + 1)), thick x x = none
| 0 fz := rfl
| (n + 1) fz := rfl
| (n + 1) (fs x) := congr_arg ((<$>) fs) $ thick_irrefl x

theorem thick_inv : ∀ {n} {x y : fin2 (n + 1)}, x ≠ y → ∃ y', thick x y = some y' ∧ y = thin x y'
| n fz fz h := absurd rfl h
| (n + 1) (fs x) fz h := ⟨fz, rfl, rfl⟩
| (n + 1) fz (fs y) h := ⟨y, rfl, rfl⟩
| (n + 1) (fs x) (fs y) h := let ⟨y', h₁, h₂⟩ := thick_inv (h ∘ congr_arg fs) in ⟨fs y', congr_arg ((<$>) fs) h₁, congr_arg fs h₂⟩

@[simp]
theorem thin_inv : ∀ {n} (x) (y : fin2 n), thick x (thin x y) = some y
| (n + 1) fz y := rfl
| (n + 1) (fs x) fz := rfl
| (n + 1) (fs x) (fs y) := congr_arg ((<$>) fs) $ thin_inv x y

@[simp]
def check {n} (x : fin2 (n + 1)) : term (n + 1) → option (term n) 
| (ι y) := ι <$> thick x y
| leaf := some leaf
| (fork s t) := fork <$> check s <*> check t

@[simp]
def for {n} (t : term n) (x : fin2 (n + 1)) (y : fin2 (n + 1)) : term n :=
match thick x y with
| some y' := ι y'
| none := t
end

@[simp]
theorem for_thin {n} {t : term n} {x y} : for t x (thin x y) = ι y :=
by simp

theorem bind_for {n x t} {t₁ t₂ : term n} (h : check x t = some t₁) : t ⟫= for t₂ x = t₁ :=
begin
  induction t generalizing t₁,
  case ι : y {
    simp at ⊢ h,
    cases thick x y with y',
      contradiction,
    injection h,
  },
  case leaf {
    injection h,
  },
  case fork : s t hs ht {
    simp at h,
    cases check x s with s',
      contradiction,
    cases check x t with t',
      contradiction,
    replace h := option.some.inj h,
    subst h,
    simp [hs rfl, ht rfl],
  },
end

inductive alist : ℕ → ℕ → Type
| anil {n} : alist n n
| asnoc {m n} : alist m n → term m → fin2 (m + 1) → alist (m + 1) n

open alist

@[simp]
def sub : ∀ {m n}, alist m n → fin2 m → term m
| m n anil y := ι y
| (m + 1) n (asnoc σ t x) y := for t x y ⟫= sub σ ⟫= ι ∘ thin x

@[simp]
def asnoc' {m} (a : Σ n, alist m n) (t : term m) (x : fin2 (m + 1)) : Σ n, alist (m + 1) n :=
⟨a.fst, asnoc a.snd t x⟩

@[simp]
def flexFlex : ∀ {m}, fin2 m → fin2 m → Σ n, alist m n
| (m + 1) x y :=
  match thick x y with
  | some y' := ⟨m, asnoc anil (ι y') x⟩
  | none := ⟨m + 1, anil⟩
  end

@[simp]
def flexRigid : ∀ {m}, fin2 m → term m → option (Σ n, alist m n)
| (m + 1) x t :=
  match check x t with
  | some t' := some ⟨m, asnoc anil t' x⟩
  | none := none
  end

@[simp]
def amgu : ∀ {m}, term m → term m → (Σ n, alist m n) → option (Σ n, alist m n)
| m leaf leaf ⟨n, anil⟩ := some ⟨n, anil⟩
| m leaf leaf acc := some acc
| m leaf (fork t₁ t₂) ⟨n, anil⟩ := none
| m leaf (fork t₁ t₂) acc := none
| m (fork s₁ s₂) leaf ⟨n, anil⟩ := none
| m (fork s₁ s₂) leaf acc := none
| m (fork s₁ s₂) (fork t₁ t₂) ⟨n, anil⟩ := amgu s₁ t₁ ⟨n, anil⟩ >>= amgu s₂ t₂
| m (fork s₁ s₂) (fork t₁ t₂) acc := amgu s₁ t₁ acc >>= amgu s₂ t₂
| m (ι x) (ι y) ⟨n, anil⟩ := some (flexFlex x y)
| m (ι x) t ⟨n, anil⟩ := flexRigid x t
| m t (ι x) ⟨n, anil⟩ := flexRigid x t
| (m + 1) s t ⟨n, asnoc σ r z⟩ := (λ σ, asnoc' σ r z) <$> amgu (s ⟫= for r z) (t ⟫= for r z) ⟨n, σ⟩

#print prefix amgu.equations

@[simp]
lemma amgu_leaf_leaf : ∀ {m acc}, @amgu m leaf leaf acc = some acc
| m ⟨n, anil⟩ := rfl

example {m} {acc} : @amgu m leaf leaf acc = some acc := rfl

def mgu {m} (s t : term m) : option (fin2 m → term m) := (amgu s t ⟨m, anil⟩).map $ λ σ, sub' σ.snd

set_option pp.implicit true

variables (m n : ℕ) (t₁ t₂ : term (m + 1)) (σ : alist m n) (r : term m) (z : fin2 (m + 1))
#check @amgu (m + 1) (@leaf (m + 1)) (t₁.fork t₂) (@sigma.mk ℕ (λ (n : ℕ), alist (m + 1) n) n (σ.asnoc r z))

lemma aunifier : ∀ {m} (s t : term m) (acc) {σ}, amgu s t acc = some σ → term.lift (sub' σ.snd) s = term.lift (sub' σ.snd) t
| m leaf leaf ⟨n, anil⟩ σ' h := rfl
| (m + 1) leaf leaf ⟨n, asnoc σ r z⟩ σ' h := rfl

| 0 leaf (fork t₁ t₂) ⟨n, anil⟩ σ' h := by simp [amgu] at h; contradiction
| (m + 1) leaf (fork t₁ t₂) ⟨n, anil⟩ σ' h := by simp [amgu] at h; contradiction
| (m + 1) leaf (fork t₁ t₂) ⟨n, asnoc σ r z⟩ σ' h := false.elim (option.no_confusion (h : none = some σ'))
| (m + 1) leaf (fork t₁ t₂) ⟨n + 1, asnoc σ r z⟩ σ' h := by simp [amgu] at h; contradiction

| 0 (fork s₁ s₂) leaf ⟨n, anil⟩ σ' h := by simp [amgu] at h; contradiction
| (m + 1) (fork s₁ s₂) leaf ⟨n, anil⟩ σ' h := by simp [amgu] at h; contradiction
-- | (m + 1) (fork s₁ s₂) leaf ⟨0, asnoc σ r z⟩ σ' h := by simp [amgu] at h; contradiction
-- | (m + 1) (fork s₁ s₂) leaf ⟨n + 1, asnoc σ r z⟩ σ' h := by simp [amgu] at h; contradiction

/-
| (m + 1) (ι x) (ι y) ⟨n, anil⟩ σ' h := by {
  simp [amgu, flexFlex] at h,
  cases hxy : thick x y; rw hxy at h,
  {
    simp [flexFlex._match_1] at h,
    cases h,
    simp,
    by_cases heq : x = y,
      cases heq,
      refl,
    have := thick.inv heq,
    cases this with y' this,
    simp [hxy] at this,
    contradiction,
  },
  {
    simp [flexFlex._match_1] at h,
    cases h,
    simp,
    by_cases heq : x = y,
      cases heq,
      refl,
    have := thick.inv heq,
    cases this with y' this,
    simp [hxy] at this,
    cases this.left,
    simp [term.lift],
    cases m; simp [sub', for_refl, lift_iota, for, hxy, thick.irrefl],
  },
}
-/

theorem unifier {m} (s t : term m) {f} : mgu s t = some f → term.lift f s = term.lift f t :=
begin
  intro h,
  dsimp [mgu] at h,
  generalize hσ : amgu s t ⟨m, anil⟩ = σ,
  rw hσ at h,
  cases σ,
  case none {
    contradiction,
  },
  cases σ with n σ,
  simp [option.map, option.bind] at h,
  generalize hσ' : sigma.mk m anil = σ',
  rw hσ' at hσ,
  clear hσ',
  cases σ' with n' σ',
  induction σ',
  case anil : m' {
    clear n' m,
    rename m' m,
    induction s,
    case leaf {
      cases t,
      case leaf {
        refl,
      },
      case fork : t₁ t₂ {
        cases m; simp [amgu] at hσ; contradiction,
      },
      case ι : x {
        cases m,
        cases x,
        simp [amgu, flexRigid, check] at hσ,
        cases hσ.left,
        cases hσ.right,
        cases n; dsimp [sub'] at h; cases h; simp [term.lift, for, thick.irrefl],
      },
    },
    case ι : x {
      cases m,
      cases x,
      cases t,
      case leaf {
        simp [amgu, flexRigid, check] at hσ,
        cases hσ.left,
        cases hσ.right,
        cases n; dsimp [sub'] at h; cases h; simp [term.lift, for, thick.irrefl],
      },
      case ι : y {
        simp [amgu, flexFlex] at hσ,
        cases hst : thick x y; rw hst at hσ; simp [flexFlex._match_1] at hσ,

        by_cases x = y,
          cases h,
          refl,
        have := thick.inv h,
        simp [hst] at this,
        cases this,
        contradiction,

        cases hσ.left,
        cases hσ.right,
        cases n; dsimp [sub'] at h; cases h; simp [term.lift, for, thick.irrefl, hst],
      },
      case fork : t₁ t₂ {
        simp [amgu, flexRigid] at hσ,
        cases hck : check x (t₁.fork t₂) with t'; rw hck at hσ; simp [flexRigid._match_1] at hσ,
          contradiction,
        cases hσ.left,
        cases hσ.right,
        simp [check] at hck,
        cases hck₁ : check x t₁ with t₁'; rw hck₁ at hck,
          contradiction,
        cases hck₂ : check x t₂ with t₂'; rw hck₂ at hck,
          contradiction,
        simp [has_bind.bind, option.bind] at hck,
        cases hck,
        cases n;
        {
          dsimp [sub'] at h,
          cases h,
          simp [term.lift, thick.irrefl, lift_iota, for_refl],
          split,
          {
            show term.lift (ι ∘ thin x) t₁' = term.lift (term.lift (ι ∘ thin x) ∘ for (t₁'.fork t₂') x) t₁,
            rw lift_comp,
            dsimp,
            congr,
            rw lift_for,
            assumption,
          },
          {
            show term.lift (ι ∘ thin x) t₂' = term.lift (term.lift (ι ∘ thin x) ∘ for (t₁'.fork t₂') x) t₂,
            rw lift_comp,
            dsimp,
            congr,
            rw lift_for,
            assumption,
          },
        },
      },
    },
    case fork : s₁ s₂ hs₁ hs₂ {
      induction t,
      case leaf {
        cases m; simp [amgu] at hσ; contradiction,
      },
      case ι : y {
        cases m,
        cases y,
        simp [amgu, flexRigid] at hσ,
        cases hck : check y (s₁.fork s₂) with s'; rw hck at hσ; simp [flexRigid._match_1] at hσ,
          contradiction,
        cases hσ.left,
        cases hσ.right,
        simp [check] at hck,
        cases hck₁ : check y s₁ with s₁'; rw hck₁ at hck,
          contradiction,
        cases hck₂ : check y s₂ with s₂'; rw hck₂ at hck,
          contradiction,
        simp [has_bind.bind, option.bind] at hck,
        cases hck,
        cases n;
        {
          dsimp [sub'] at h,
          cases h,
          simp [term.lift, thick.irrefl, lift_iota, for_refl],
          split,
          {
            show term.lift (term.lift (ι ∘ thin y) ∘ for (s₁'.fork s₂') y) s₁ = term.lift (ι ∘ thin y) s₁',
            rw lift_comp,
            dsimp,
            congr,
            rw lift_for,
            assumption,
          },
          {
            show term.lift (term.lift (ι ∘ thin y) ∘ for (s₁'.fork s₂') y) s₂ = term.lift (ι ∘ thin y) s₂',
            rw lift_comp,
            dsimp,
            congr,
            rw lift_for,
            assumption,
          },
        },
      },
      case fork : t₁ t₂ ht₁ ht₂ {
        cases m,
        {
          simp [amgu] at hσ,
          cases hσ' : amgu s₁ t₁ ⟨0, anil⟩ with σ'; rw hσ' at hσ,
            contradiction,
          simp [has_bind.bind, option.bind] at hσ,
          simp [term.lift],
        },
      },
    },
  },
end
