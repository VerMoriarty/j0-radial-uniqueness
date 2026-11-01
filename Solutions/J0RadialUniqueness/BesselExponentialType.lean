import Solutions.J0RadialUniqueness.CircularBesselIntegral
import Solutions.J0RadialUniqueness.SimpleOnePoints

noncomputable section
open MeasureTheory

namespace J0RadialUniqueness

theorem norm_bessel_circle_integrand_le (z : ℂ) (t : ℝ) :
    ‖Complex.exp ((Complex.I * z) * (Real.cos t : ℂ))‖ ≤ Real.exp |z.im| := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : ((Complex.I * z) * (Real.cos t : ℂ)).re = -z.im * Real.cos t := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub, mul_zero]
  rw [hre]
  calc
    -z.im * Real.cos t ≤ |-z.im * Real.cos t| := le_abs_self _
    _ = |z.im| * |Real.cos t| := by rw [abs_mul, abs_neg]
    _ ≤ |z.im| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg _)
    _ = _ := mul_one _

/-- Actual exponential type estimate from the proved complex circle integral. -/
theorem norm_J0_le_exp_abs_im (z : ℂ) : ‖J0 z‖ ≤ Real.exp |z.im| := by
  have hI := integral_exp_mul_cos_eq_J0 (Complex.I * z)
  have hrot : Complex.I * (Complex.I * z) = -z := by rw [← mul_assoc, Complex.I_mul_I]; ring
  rw [hrot, J0_neg] at hI
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun t _ => norm_bessel_circle_integrand_le z t)
  rw [hI, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos), sub_zero,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at h
  nlinarith [Real.pi_pos]

theorem norm_J0_le_exp_norm (z : ℂ) : ‖J0 z‖ ≤ Real.exp ‖z‖ :=
  (norm_J0_le_exp_abs_im z).trans (Real.exp_le_exp.mpr (Complex.abs_im_le_norm z))

theorem norm_sourceEta_le_exp_abs_im_add_one (z : ℂ) :
    ‖1 - J0 z‖ ≤ Real.exp |z.im| + 1 := by
  calc
    ‖1 - J0 z‖ ≤ ‖(1 : ℂ)‖ + ‖J0 z‖ := norm_sub_le _ _
    _ ≤ 1 + Real.exp |z.im| := by
      simp only [norm_one]
      exact add_le_add le_rfl (norm_J0_le_exp_abs_im z)
    _ = _ := add_comm _ _

end J0RadialUniqueness
