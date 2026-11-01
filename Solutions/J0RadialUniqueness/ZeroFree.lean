import Solutions.J0RadialUniqueness.Series

noncomputable section

namespace J0RadialUniqueness

/-- Infinite Eneström--Kakeya lemma for summable nonnegative decreasing coefficients. -/
theorem decreasing_series_ne_zero (b : ℕ → ℝ) (hb : Summable b)
    (hn : ∀ n, 0 ≤ b n) (hd : ∀ n, b (n + 1) ≤ b n) (h₀ : b 0 = 1)
    (u : ℂ) (hu : ‖u‖ < 1) :
    (∑' n : ℕ, (b n : ℂ) * u ^ n) ≠ 0 := by
  let d : ℕ → ℝ := fun n => b n - b (n + 1)
  have hdpos : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (hd n)
  have hbshift : Summable (fun n => b (n + 1)) :=
    (summable_nat_add_iff 1).mpr hb
  have hds : Summable d := hb.sub hbshift
  have hdt : ∑' n, d n = 1 := by
    rw [show (∑' n, d n) = (∑' n, b n) - ∑' n, b (n + 1) from
      hb.tsum_sub hbshift]
    have he := hb.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at he
    linarith
  have hupow : ∀ n : ℕ, ‖u‖ ^ n ≤ 1 :=
    fun n => pow_le_one₀ (norm_nonneg _) hu.le
  have hs : Summable (fun n => (b n : ℂ) * u ^ n) := by
    apply hb.of_norm_bounded
    intro n
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn n), norm_pow]
    exact mul_le_of_le_one_right (hn n) (hupow n)
  have hD : Summable (fun n => (d n : ℂ) * u ^ (n + 1)) := by
    apply hds.of_norm_bounded
    intro n
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hdpos n), norm_pow]
    exact mul_le_of_le_one_right (hdpos n) (hupow (n + 1))
  have ht : Summable (fun n => (b (n + 1) : ℂ) * u ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hmul : (∑' n, (d n : ℂ) * u ^ (n + 1)) =
      u * (∑' n, (b n : ℂ) * u ^ n) -
        ∑' n, (b (n + 1) : ℂ) * u ^ (n + 1) := by
    rw [← tsum_mul_left, ← (hs.mul_left u).tsum_sub ht]
    apply tsum_congr
    intro n
    simp only [d, Complex.ofReal_sub, pow_succ]
    ring
  have hbound : ‖∑' n, (d n : ℂ) * u ^ (n + 1)‖ ≤ ‖u‖ := by
    have hbnd : ∀ n, ‖(d n : ℂ) * u ^ (n + 1)‖ ≤ d n * ‖u‖ := by
      intro n
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hdpos n), norm_pow, pow_succ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg _) (hupow n)) (hdpos n)
    have hh := hD.hasSum.norm_le_of_bounded (hds.mul_right ‖u‖).hasSum hbnd
    simpa [hds.tsum_mul_right, hdt] using hh
  intro hz
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, mul_one, h₀, Complex.ofReal_one, hz] at he
  rw [hz, mul_zero] at hmul
  have hdvalue : (∑' n, (d n : ℂ) * u ^ (n + 1)) = 1 := by
    linear_combination hmul - he
  rw [hdvalue, norm_one] at hbound
  exact (not_le_of_gt hu) hbound

def qScaledCoeff (n : ℕ) : ℝ := 4 ^ n / ((n + 1).factorial : ℝ) ^ 2

theorem qScaledCoeff_summable : Summable qScaledCoeff := by
  apply (Real.summable_pow_div_factorial 4).of_norm_bounded
  intro n
  have hp : (0 : ℝ) < n.factorial := by positivity
  have hge : (1 : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
  have hle : (n.factorial : ℝ) ≤ (n + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 1)
  have hnonneg : 0 ≤ qScaledCoeff n := by unfold qScaledCoeff; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  unfold qScaledCoeff
  exact div_le_div_of_nonneg_left (by positivity) hp (by nlinarith)

theorem qScaledCoeff_decreasing (n : ℕ) : qScaledCoeff (n + 1) ≤ qScaledCoeff n := by
  have hp : (0 : ℝ) < (n + 1).factorial := by positivity
  have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hratio : qScaledCoeff (n + 1) = qScaledCoeff n * (4 / ((n : ℝ) + 2) ^ 2) := by
    unfold qScaledCoeff
    rw [Nat.factorial_succ (n + 1), Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ring
  rw [hratio]
  apply mul_le_of_le_one_right (by unfold qScaledCoeff; positivity)
  apply (div_le_one (by positivity)).mpr
  nlinarith

/-- Lemma 2.3, for the concrete factorial series Q. -/
theorem Q_ne_zero_of_norm_lt_four (w : ℂ) (hw : ‖w‖ < 4) : Q w ≠ 0 := by
  have hu : ‖w / 4‖ < 1 := by simpa [norm_div] using (div_lt_one (by norm_num : (0 : ℝ) < 4)).mpr hw
  have hh := decreasing_series_ne_zero qScaledCoeff qScaledCoeff_summable
    (fun n => by unfold qScaledCoeff; positivity) qScaledCoeff_decreasing (by norm_num [qScaledCoeff])
    (w / 4) hu
  convert hh using 1
  unfold Q
  apply tsum_congr
  intro n
  simp only [qScaledCoeff, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, div_pow]
  field_simp

/-- The zero-free disk part of Proposition 2.4, with no localization assumption. -/
theorem one_point_norm_ge_four (z : ℂ) (hz : z ≠ 0) (hJ : J0 z = 1) : 4 ≤ ‖z‖ := by
  by_contra! hsmall
  have hw : ‖-z ^ 2 / 4‖ < 4 := by
    rw [norm_div, norm_neg, norm_pow]
    norm_num
    nlinarith [norm_nonneg z]
  have hn : -z ^ 2 / 4 ≠ 0 := by exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hz)) (by norm_num)
  have he := F_sub_one (-z ^ 2 / 4)
  change J0 z - 1 = _ at he
  rw [hJ, sub_self] at he
  exact (mul_ne_zero hn (Q_ne_zero_of_norm_lt_four _ hw)) he.symm

end J0RadialUniqueness
