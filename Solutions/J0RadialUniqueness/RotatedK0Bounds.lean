import Solutions.J0RadialUniqueness.BesselResolventConnection

/-! Actual rotated K₀ estimates, valid at every positive modulus in the closed
principal sector. In particular, no large-argument hypothesis is imposed on a
radial integration variable approaching zero. -/

noncomputable section

namespace J0RadialUniqueness

theorem norm_laplace_prefactor (w : ℂ) :
    ‖Complex.cpow ((Real.pi : ℂ) / (2 * w)) (1 / 2 : ℂ)‖ =
      Real.sqrt (Real.pi / (2 * ‖w‖)) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [Complex.cpow_eq_pow, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow]
  simp [norm_div, norm_mul, abs_of_pos Real.pi_pos]

theorem norm_APlus_le_all {z : ℂ} (hz : ClosedPrincipalSector z) :
    ‖APlus z‖ ≤ 1 + kappa / ‖z‖ := by
  have hh := (amplitude_uniform_estimates z hz).1
  have ht := norm_add_le (APlus z - 1) (1 : ℂ)
  simp only [sub_add_cancel, norm_one] at ht
  linarith

theorem norm_AMinus_le_all {z : ℂ} (hz : ClosedPrincipalSector z) :
    ‖AMinus z‖ ≤ 1 + kappa / ‖z‖ := by
  have hh := (amplitude_uniform_estimates z hz).2.1
  have ht := norm_add_le (AMinus z - 1) (1 : ℂ)
  simp only [sub_add_cancel, norm_one] at ht
  linarith

theorem K0Series_negI_eq_amplitude {z : ℂ} (hz : 0 < z.re) :
    K0Series (-Complex.I * z) =
      Complex.cpow ((Real.pi : ℂ) / (2 * (-Complex.I * z))) (1 / 2 : ℂ) *
        Complex.exp (Complex.I * z) * APlus z := by
  rw [← k_laplace_identification _ (negI_mul_mem_slitPlane hz)]
  unfold laplaceK
  rw [← APlus_eq_laplaceI]
  simp only [neg_mul, neg_neg]

theorem K0Series_I_eq_amplitude {z : ℂ} (hz : 0 < z.re) :
    K0Series (Complex.I * z) =
      Complex.cpow ((Real.pi : ℂ) / (2 * (Complex.I * z))) (1 / 2 : ℂ) *
        Complex.exp (-Complex.I * z) * AMinus z := by
  rw [← k_laplace_identification _ (I_mul_mem_slitPlane hz)]
  unfold laplaceK
  rw [← AMinus_eq_laplaceI]
  simp only [neg_mul]

theorem norm_K0Series_negI_le {z : ℂ} (hz : ClosedPrincipalSector z) :
    ‖K0Series (-Complex.I * z)‖ ≤
      Real.sqrt (Real.pi / (2 * ‖z‖)) * Real.exp (-z.im) * (1 + kappa / ‖z‖) := by
  rw [K0Series_negI_eq_amplitude hz.2.2, norm_mul, norm_mul,
    norm_laplace_prefactor, Complex.norm_exp]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.I_mul_re]
  exact mul_le_mul_of_nonneg_left (norm_APlus_le_all hz) (by positivity)

theorem norm_K0Series_I_le {z : ℂ} (hz : ClosedPrincipalSector z) :
    ‖K0Series (Complex.I * z)‖ ≤
      Real.sqrt (Real.pi / (2 * ‖z‖)) * Real.exp z.im * (1 + kappa / ‖z‖) := by
  rw [K0Series_I_eq_amplitude hz.2.2, norm_mul, norm_mul,
    norm_laplace_prefactor, Complex.norm_exp]
  simp only [norm_mul, Complex.norm_I, one_mul, neg_mul, Complex.neg_re,
    Complex.I_mul_re, neg_neg]
  exact mul_le_mul_of_nonneg_left (norm_AMinus_le_all hz) (by positivity)

theorem closedPrincipalSector_pos_scale {lam : ℂ} (hlam : ClosedPrincipalSector lam)
    {s : ℝ} (hs : 0 < s) : ClosedPrincipalSector ((s : ℂ) * lam) := by
  rcases hlam with ⟨hi, hir, hr⟩
  simp only [ClosedPrincipalSector, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, add_zero, sub_zero]
  exact ⟨mul_nonneg hs.le hi, mul_le_mul_of_nonneg_left hir hs.le, mul_pos hs hr⟩

end J0RadialUniqueness
