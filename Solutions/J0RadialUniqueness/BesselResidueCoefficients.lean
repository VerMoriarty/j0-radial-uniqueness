import Solutions.J0RadialUniqueness.OnePointDerivativeBounds
import Solutions.J0RadialUniqueness.SpectralInversePowerSummability
import Solutions.J0RadialUniqueness.ScaledOnePointDefectBounds

/-! The actual coefficients of the high-order-pole spectral construction.
All convergence assertions are proved on the genuine Bessel one-point set,
then restricted to its right half plane. No zero enumeration is needed. -/

noncomputable section
open Set

namespace J0RadialUniqueness

abbrev RightOnePoint := {z : onePoints // 0 < (z : ℂ).re}

def besselResidueCoefficient (M : ℕ) (z : ℂ) : ℂ :=
  -2 / (z ^ (2 * M + 1) * deriv J0 z)

theorem besselResidueCoefficient_ne_zero (M : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hJ : J0 z = 1) : besselResidueCoefficient M z ≠ 0 :=
  div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ hz)
    (J0_deriv_ne_zero_at_one_point hz hJ))

theorem besselResidueCoefficient_norm_le (M : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hJ : J0 z = 1) :
    ‖besselResidueCoefficient M z‖ ≤ (50 / 7 : ℝ) / ‖z‖ ^ (2 * M) := by
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd : 0 < ‖deriv J0 z‖ := norm_pos_iff.mpr (J0_deriv_ne_zero_at_one_point hz hJ)
  have hi := (J0_inverse_derivative_norm_upper_bound_at_one_point hz hJ).le
  rw [norm_inv] at hi
  have he : ‖besselResidueCoefficient M z‖ =
      2 * ‖deriv J0 z‖⁻¹ / ‖z‖ ^ (2 * M + 1) := by
    unfold besselResidueCoefficient
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    simp only [norm_div, norm_mul, norm_pow, norm_neg, htwo]
    field_simp
  rw [he]
  calc
    _ ≤ 2 * ((25 / 7 : ℝ) * ‖z‖) / ‖z‖ ^ (2 * M + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp [hρ.ne']; ring

theorem besselResidueCoefficient_norm_rpow_bound (M : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hJ : J0 z = 1) :
    ‖besselResidueCoefficient M z‖ ≤ (50 / 7 : ℝ) * ‖z‖ ^ (-(2 * M : ℝ)) := by
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : ‖z‖ ^ (-(2 * M : ℝ)) = (‖z‖ ^ (2 * M : ℕ))⁻¹ := by
    rw [Real.rpow_neg hρ.le]
    congr 1
    norm_cast
  rw [he, ← div_eq_mul_inv]
  exact besselResidueCoefficient_norm_le M hz hJ

/-- Every fixed polynomial weight below the proved sufficient threshold is
summable, using the actual Jensen count and inverse-power sum. -/
theorem besselResidueCoefficient_weight_summable (M : ℕ) {b : ℝ}
    (hb : b < 2 * M - 1) :
    Summable (fun z : onePoints => ‖besselResidueCoefficient M z‖ * ‖(z : ℂ)‖ ^ b) := by
  let ε : ℝ := 2 * M - 1 - b
  have hε : 0 < ε := sub_pos.mpr hb
  have hs := (onePoints_inverse_power_summable hε).mul_left (50 / 7 : ℝ)
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (norm_nonneg _) _)) _ hs
  intro z
  have hρ : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.property.1
  calc
    _ ≤ ((50 / 7 : ℝ) * ‖(z : ℂ)‖ ^ (-(2 * M : ℝ))) * ‖(z : ℂ)‖ ^ b :=
      mul_le_mul_of_nonneg_right (besselResidueCoefficient_norm_rpow_bound M z.property.1
        z.property.2) (Real.rpow_nonneg hρ.le _)
    _ = (50 / 7 : ℝ) * ‖(z : ℂ)‖ ^ (-1 - ε) := by
      rw [mul_assoc, ← Real.rpow_add hρ]
      congr 2
      dsimp only [ε]
      ring

theorem besselResidueCoefficient_summable (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun z : onePoints => besselResidueCoefficient M z) := by
  apply Summable.of_norm
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  simpa only [Real.rpow_zero, mul_one] using
    besselResidueCoefficient_weight_summable M (b := 0) (by linarith)

theorem rightOnePoint_sq_injective :
    Function.Injective (fun z : RightOnePoint => ((z : onePoints) : ℂ) ^ 2) := by
  intro z w hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with he | he
  · exact Subtype.ext (Subtype.ext he)
  · have hre := congrArg Complex.re he
    simp only [Complex.neg_re] at hre
    have hz := z.property
    have hw := w.property
    linarith

end J0RadialUniqueness
