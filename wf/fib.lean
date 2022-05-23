def fib' : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib' n + fib' (n + 1)

def fib : ℕ → ℕ :=
well_founded.fix has_well_founded.wf $
  @nat.rec (λ n, (∀ m < n, ℕ) → ℕ) (λ ih, 0) $
    @nat.rec (λ n, ((∀ m < n, ℕ) → ℕ) → (∀ m < n.succ, ℕ) → ℕ) (λ _ ih, 1) $
      λ n _ _ ih, ih n (nat.lt.base n).step + ih n.succ (nat.lt.base n.succ)

@[simp]
def accessible (ac : acc (<) 0) : acc (inv_image (<) id) 0 :=
(acc.rec_on ac (λ x acx ih z e, acc.intro z (λ y lt, eq.rec_on e (λ acx ih, ih y lt y rfl) acx ih))
  : ∀ (x : ℕ), x = 0 → acc (inv_image (<) id) x) 0 rfl

@[simp]
lemma lt_wf : nat.lt_wf.apply =
nat.rec
  (acc.intro 0 (λ n h, absurd h (nat.not_lt_zero n)))
  (λ n ih, acc.intro (nat.succ n) (λ m h,
     or.elim (nat.eq_or_lt_of_le (nat.le_of_succ_le_succ h))
        (λ e, eq.substr e ih) (acc.inv ih))) := rfl

theorem fib0 : fib 0 = 0 :=
begin
  change @acc.rec _ _ _ _ _ (@accessible (nat.lt_wf.apply 0)) = _,
  dsimp [fib, well_founded.fix, well_founded.fix_F, has_well_founded_of_has_sizeof, sizeof_measure, measure, sizeof, inv_image, has_sizeof.sizeof, nat.sizeof, has_lt.lt, sizeof_measure_wf, nat.has_sizeof],
  refl,
end

#reduce fib0
#reduce fib 0 = 0
theorem fib0' : fib 0 = 0 := eq.refl 0
