import Solutions.J0RadialUniqueness.CompactHelmholtzResolvent
import Solutions.J0RadialUniqueness.BesselExponentialType

/-! Exponential growth bounds for the actual entire coefficient series.

The shifted harmonic-number series is proved equal to the analytic divided
difference, including its value at zero. Its coefficients, and those of Q,
are bounded by the positive coefficients of F. The sharp order in the square
root of the argument follows from the actual Bessel circle integral. Thus
substitution of a quadratic spectral parameter gives order one, not order two.
-/

noncomputable section

namespace J0RadialUniqueness

def positiveFTerm (t : ℝ) (n : ℕ) : ℝ := t ^ n / (n.factorial : ℝ) ^ 2

theorem fTerm_ofReal_eq (t : ℝ) (n : ℕ) :
    fTerm (t : ℂ) n = (positiveFTerm t n : ℂ) := by
  simp [fTerm, positiveFTerm]

theorem positiveFTerm_hasSum (t : ℝ) :
    HasSum (positiveFTerm t) (F (t : ℂ)).re := by
  have h := Complex.hasSum_re (fTerm_summable (t : ℂ)).hasSum
  change HasSum (fun n : ℕ => (fTerm (t : ℂ) n).re) (F (t : ℂ)).re at h
  convert! h using 1
  funext n
  rw [fTerm_ofReal_eq, Complex.ofReal_re]

theorem F_ofReal_eq_positive_sum (t : ℝ) :
    F (t : ℂ) = ((∑' n : ℕ, positiveFTerm t n : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact tsum_congr (fTerm_ofReal_eq t)

theorem F_ofReal_re_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (F (t : ℂ)).re := by
  rw [F_ofReal_eq_positive_sum, Complex.ofReal_re]
  exact tsum_nonneg (fun n => div_nonneg (pow_nonneg ht n) (sq_nonneg _))

theorem norm_F_ofReal_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ‖F (t : ℂ)‖ = (F (t : ℂ)).re := by
  rw [F_ofReal_eq_positive_sum, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  apply abs_of_nonneg
  exact tsum_nonneg (fun n => div_nonneg (pow_nonneg ht n) (sq_nonneg _))

theorem norm_series_le_F_positive {a : ℕ → ℂ} (w : ℂ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ positiveFTerm ‖w‖ n) :
    ‖∑' n : ℕ, a n‖ ≤ (F (‖w‖ : ℂ)).re :=
  tsum_of_norm_bounded (positiveFTerm_hasSum ‖w‖) ha

theorem norm_F_le_positive_F (w : ℂ) :
    ‖F w‖ ≤ (F (‖w‖ : ℂ)).re := by
  apply norm_series_le_F_positive w
  intro n
  simp only [fTerm, positiveFTerm, norm_div, norm_pow, Complex.norm_natCast]
  exact le_rfl

theorem positive_F_le_exp_sqrt {t : ℝ} (ht : 0 ≤ t) :
    (F (t : ℂ)).re ≤ Real.exp (2 * Real.sqrt t) := by
  let z : ℂ := 2 * Complex.I * (Real.sqrt t : ℂ)
  have hsq : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt ht
  have hz : J0 z = F (t : ℂ) := by
    unfold J0 z
    congr 1
    calc
      -(2 * Complex.I * (Real.sqrt t : ℂ)) ^ 2 / 4 = (Real.sqrt t : ℂ) ^ 2 := by
        rw [mul_pow, mul_pow, Complex.I_sq]
        ring
      _ = (t : ℂ) := hsq
  have hn : ‖z‖ = 2 * Real.sqrt t := by
    simp [z, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg t)]
  calc
    (F (t : ℂ)).re ≤ ‖F (t : ℂ)‖ := Complex.re_le_norm _
    _ = ‖J0 z‖ := congrArg norm hz.symm
    _ ≤ Real.exp ‖z‖ := norm_J0_le_exp_norm z
    _ = _ := by rw [hn]

theorem norm_F_le_exp_sqrt (w : ℂ) :
    ‖F w‖ ≤ Real.exp (2 * Real.sqrt ‖w‖) :=
  (norm_F_le_positive_F w).trans (positive_F_le_exp_sqrt (norm_nonneg w))

theorem norm_qTerm_le_positiveFTerm (w : ℂ) (n : ℕ) :
    ‖w ^ n / ((n + 1).factorial : ℂ) ^ 2‖ ≤ positiveFTerm ‖w‖ n := by
  have hle : (n.factorial : ℝ) ≤ (n + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 1)
  have hp : (0 : ℝ) < n.factorial := by positivity
  simp only [norm_div, norm_pow, Complex.norm_natCast, positiveFTerm]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg w) n)
    (sq_pos_of_pos hp) (by nlinarith)

theorem norm_Q_le_positive_F (w : ℂ) :
    ‖Q w‖ ≤ (F (‖w‖ : ℂ)).re :=
  norm_series_le_F_positive w (norm_qTerm_le_positiveFTerm w)

theorem norm_Q_le_exp_sqrt (w : ℂ) :
    ‖Q w‖ ≤ Real.exp (2 * Real.sqrt ‖w‖) :=
  (norm_Q_le_positive_F w).trans (positive_F_le_exp_sqrt (norm_nonneg w))

def harmonicDividedTerm (w : ℂ) (n : ℕ) : ℂ :=
  (harmonic (n + 1) : ℂ) * w ^ n / ((n + 1).factorial : ℂ) ^ 2

theorem norm_harmonicDividedTerm_le_positiveFTerm (w : ℂ) (n : ℕ) :
    ‖harmonicDividedTerm w n‖ ≤ positiveFTerm ‖w‖ n := by
  have hb := harmonic_real_bounds (n + 1)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcoef : (harmonic (n + 1) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have hlin : (harmonic (n + 1) : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast hb.2
    nlinarith
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnc : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    calc
      ‖(n : ℂ) + 1‖ = ‖((n + 1 : ℕ) : ℂ)‖ := by congr 1; push_cast; rfl
      _ = ((n + 1 : ℕ) : ℝ) := Complex.norm_natCast _
      _ = (n : ℝ) + 1 := by push_cast; rfl
  simp only [harmonicDividedTerm, norm_div, norm_mul, norm_pow,
    Complex.norm_ratCast, Complex.norm_natCast, abs_of_nonneg hb.1,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, positiveFTerm]
  rw [hnc]
  calc
    (harmonic (n + 1) : ℝ) * ‖w‖ ^ n /
        (((n : ℝ) + 1) * (n.factorial : ℝ)) ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 * ‖w‖ ^ n /
        (((n : ℝ) + 1) * (n.factorial : ℝ)) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (pow_nonneg (norm_nonneg w) n)) (sq_nonneg _)
    _ = ‖w‖ ^ n / (n.factorial : ℝ) ^ 2 := by
      field_simp [hf, hn1]

theorem harmonicDividedTerm_summable (w : ℂ) : Summable (harmonicDividedTerm w) :=
  (positiveFTerm_hasSum ‖w‖).summable.of_norm_bounded
    (norm_harmonicDividedTerm_le_positiveFTerm w)

theorem harmonicF_eq_mul_divided_series (w : ℂ) :
    harmonicF w = w * ∑' n : ℕ, harmonicDividedTerm w n := by
  have hshift := (harmonic_fTerm_summable w).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, harmonic_zero, Rat.cast_zero, zero_mul, zero_add] at hshift
  calc
    harmonicF w = ∑' n : ℕ, (harmonic (n + 1) : ℂ) * fTerm w (n + 1) := hshift.symm
    _ = ∑' n : ℕ, w * harmonicDividedTerm w n := by
      apply tsum_congr
      intro n
      simp only [fTerm, harmonicDividedTerm, pow_succ]
      ring
    _ = w * ∑' n : ℕ, harmonicDividedTerm w n := tsum_mul_left

theorem harmonicDividedDifference_eq_series (w : ℂ) :
    harmonicDividedDifference w = ∑' n : ℕ, harmonicDividedTerm w n := by
  by_cases hw : w = 0
  · subst w
    rw [harmonicDividedDifference_zero, tsum_eq_single 0]
    · simp [harmonicDividedTerm, harmonic_succ]
    · intro n hn
      simp [harmonicDividedTerm, zero_pow hn]
  · apply mul_left_cancel₀ hw
    rw [← harmonicF_factor_dividedDifference, harmonicF_eq_mul_divided_series]

theorem norm_harmonicDividedDifference_le_positive_F (w : ℂ) :
    ‖harmonicDividedDifference w‖ ≤ (F (‖w‖ : ℂ)).re := by
  rw [harmonicDividedDifference_eq_series]
  exact norm_series_le_F_positive w (norm_harmonicDividedTerm_le_positiveFTerm w)

theorem norm_harmonicDividedDifference_le_exp_sqrt (w : ℂ) :
    ‖harmonicDividedDifference w‖ ≤ Real.exp (2 * Real.sqrt ‖w‖) :=
  (norm_harmonicDividedDifference_le_positive_F w).trans
    (positive_F_le_exp_sqrt (norm_nonneg w))

theorem norm_harmonicF_le_norm_mul_exp_sqrt (w : ℂ) :
    ‖harmonicF w‖ ≤ ‖w‖ * Real.exp (2 * Real.sqrt ‖w‖) := by
  rw [harmonicF_factor_dividedDifference, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_harmonicDividedDifference_le_exp_sqrt w) (norm_nonneg w)

theorem norm_helmholtzResolventArg {s : ℝ} (hs : 0 ≤ s) (lam : ℂ) :
    ‖helmholtzResolventArg lam s‖ = (s * ‖lam‖ / 2) ^ 2 := by
  unfold helmholtzResolventArg
  simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_ofNat,
    Complex.norm_of_nonneg hs]
  ring

theorem twice_sqrt_norm_helmholtzResolventArg {s : ℝ} (hs : 0 ≤ s) (lam : ℂ) :
    2 * Real.sqrt ‖helmholtzResolventArg lam s‖ = s * ‖lam‖ := by
  rw [norm_helmholtzResolventArg hs lam, Real.sqrt_sq (by positivity)]
  ring

theorem norm_F_helmholtzResolventArg_le {s : ℝ} (hs : 0 ≤ s) (lam : ℂ) :
    ‖F (helmholtzResolventArg lam s)‖ ≤ Real.exp (s * ‖lam‖) := by
  simpa only [twice_sqrt_norm_helmholtzResolventArg hs lam] using
    norm_F_le_exp_sqrt (helmholtzResolventArg lam s)

theorem norm_Q_helmholtzResolventArg_le {s : ℝ} (hs : 0 ≤ s) (lam : ℂ) :
    ‖Q (helmholtzResolventArg lam s)‖ ≤ Real.exp (s * ‖lam‖) := by
  simpa only [twice_sqrt_norm_helmholtzResolventArg hs lam] using
    norm_Q_le_exp_sqrt (helmholtzResolventArg lam s)

theorem norm_D_helmholtzResolventArg_le {s : ℝ} (hs : 0 ≤ s) (lam : ℂ) :
    ‖harmonicDividedDifference (helmholtzResolventArg lam s)‖ ≤ Real.exp (s * ‖lam‖) := by
  simpa only [twice_sqrt_norm_helmholtzResolventArg hs lam] using
    norm_harmonicDividedDifference_le_exp_sqrt (helmholtzResolventArg lam s)

theorem norm_H_helmholtzResolventArg_le {s : ℝ} (hs : 0 ≤ s) (lam : ℂ) :
    ‖harmonicF (helmholtzResolventArg lam s)‖ ≤
      (s * ‖lam‖ / 2) ^ 2 * Real.exp (s * ‖lam‖) := by
  have h := norm_harmonicF_le_norm_mul_exp_sqrt (helmholtzResolventArg lam s)
  rw [twice_sqrt_norm_helmholtzResolventArg hs lam, norm_helmholtzResolventArg hs lam] at h
  exact h

end J0RadialUniqueness
