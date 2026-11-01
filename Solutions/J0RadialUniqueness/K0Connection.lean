import Definitions.J0RadialUniqueness.Analytic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
The principal-logarithm connection formula for the independently defined
`K0Series`.  The harmonic-number series is also proved absolutely convergent.
Nothing in this file identifies `K0Series` with the Laplace integral `laplaceK`.
-/

noncomputable section

namespace J0RadialUniqueness

/-- Across negation in the upper half-plane the principal logarithm loses πi. -/
theorem log_neg_of_im_pos (w : ℂ) (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]

/-- The two logarithms in the K₀ connection formula differ by precisely πi. -/
theorem log_I_rotation_difference (z : ℂ) (hz : 0 < z.re) :
    Complex.log (Complex.I * z / 2) - Complex.log (-Complex.I * z / 2) =
      (Real.pi : ℂ) * Complex.I := by
  have him : 0 < (Complex.I * z / 2).im := by
    simpa using div_pos hz (by norm_num : (0 : ℝ) < 2)
  have hneg : -Complex.I * z / 2 = -(Complex.I * z / 2) := by ring
  rw [hneg, log_neg_of_im_pos _ him]
  ring

/-- DLMF 10.27.9 at order zero, for the independent logarithmic K₀ series. -/
theorem K0_connection : K0ConnectionStatement := by
  intro z hz
  change 0 < z.re at hz
  have hplus : (Complex.I * z) ^ 2 / 4 = -z ^ 2 / 4 := by
    rw [mul_pow, Complex.I_sq]
    ring
  have hminus : (-Complex.I * z) ^ 2 / 4 = -z ^ 2 / 4 := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  calc
    (Real.pi : ℂ) * Complex.I * J0 z =
        (Complex.log (Complex.I * z / 2) -
          Complex.log (-Complex.I * z / 2)) * F (-z ^ 2 / 4) := by
      rw [log_I_rotation_difference z hz]
      rfl
    _ = K0Series (-Complex.I * z) - K0Series (Complex.I * z) := by
      unfold K0Series
      rw [hminus, hplus]
      ring

/-- Elementary real bounds used to dominate the logarithmic-series coefficients. -/
theorem harmonic_real_bounds (n : ℕ) :
    0 ≤ (harmonic n : ℝ) ∧ (harmonic n : ℝ) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs : (harmonic (n + 1) : ℝ) =
          (harmonic n : ℝ) + ((n : ℝ) + 1)⁻¹ := by
        simp [harmonic_succ]
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ hp).2 hn
      have hi0 : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := inv_nonneg.mpr hp.le
      rw [hs]
      constructor
      · exact add_nonneg ih.1 hi0
      · push_cast
        linarith [ih.2]

/-- The harmonic-number series defining K₀ converges at every complex argument. -/
theorem K0_series_convergence : K0SeriesConvergenceStatement := by
  intro w
  apply (Real.summable_pow_div_factorial ‖w ^ 2 / 4‖).of_norm_bounded
  intro n
  have hbounds := harmonic_real_bounds n
  have hnf : (n : ℝ) ≤ n.factorial := by exact_mod_cast Nat.self_le_factorial n
  have hh : ‖(harmonic n : ℂ)‖ ≤ (n.factorial : ℝ) := by
    rw [Complex.norm_ratCast, abs_of_nonneg hbounds.1]
    exact hbounds.2.trans hnf
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    ‖(harmonic n : ℂ) * fTerm (w ^ 2 / 4) n‖ =
        ‖(harmonic n : ℂ)‖ * (‖w ^ 2 / 4‖ ^ n / (n.factorial : ℝ) ^ 2) := by
      simp [fTerm, norm_mul, norm_div, norm_pow]
    _ ≤ (n.factorial : ℝ) *
        (‖w ^ 2 / 4‖ ^ n / (n.factorial : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = ‖w ^ 2 / 4‖ ^ n / (n.factorial : ℝ) := by
      field_simp [hf] <;> ring

end J0RadialUniqueness
