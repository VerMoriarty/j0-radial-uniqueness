import Solutions.J0RadialUniqueness.FUniformGap
import Solutions.J0RadialUniqueness.SpectralVerticalBounds

/-! Lower bounds for the actual mean defect away from its root strip.
The first includes the closed sector boundary. The second uses the actual
dominant amplitude at sufficiently large height, without a phase condition. -/

noncomputable section

namespace J0RadialUniqueness

theorem J0_uniform_defect_gap_outside_principal :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, |z.re| ≤ |z.im| → 2 ≤ ‖z‖ →
      ε ≤ ‖1 - J0 z‖ := by
  obtain ⟨ε, hε, hgap⟩ := F_uniform_defect_gap
  refine ⟨ε, hε, ?_⟩
  intro z hsector hnorm
  have hsq : z.re ^ 2 ≤ z.im ^ 2 := by
    nlinarith only [sq_abs z.re, sq_abs z.im,
      mul_self_le_mul_self (abs_nonneg z.re) hsector]
  have hre : 0 ≤ (-z ^ 2 / 4).re := by
    simp only [Complex.div_ofNat_re, Complex.neg_re, pow_two, Complex.mul_re]
    linarith
  have hn : 1 ≤ ‖-z ^ 2 / 4‖ := by
    simp only [norm_div, norm_neg, norm_pow, Complex.norm_ofNat]
    nlinarith [norm_nonneg z]
  exact hgap (-z ^ 2 / 4) hre hn

theorem norm_one_sub_ge_quarter_of_large_norm_and_relative_error {G J : ℂ}
    (hG : (4 : ℝ) ≤ ‖G‖) (hE : ‖J - G‖ ≤ ‖G‖ / 4) :
    (1 + ‖G‖) / 4 ≤ ‖1 - J‖ := by
  have htri : ‖G‖ ≤ ‖J‖ + ‖J - G‖ := by
    simpa only [sub_sub_cancel, norm_neg] using norm_sub_le J (J - G)
  have hrev : ‖J‖ - 1 ≤ ‖1 - J‖ := by
    simpa only [norm_one, norm_sub_rev] using norm_sub_norm_le J (1 : ℂ)
  linarith

theorem spectral_high_magnitude_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    (hρ : 4 ≤ ‖z‖) (hy : (2 : ℝ) ≤ z.im)
    (hlarge : 4 ≤ Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) :
    (1 + Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) / 4 ≤ ‖1 - J0 z‖ := by
  have hlarge' : (4 : ℝ) ≤ ‖verticalLeadingTerm z‖ := by
    rwa [norm_verticalLeadingTerm]
  have hh := norm_one_sub_ge_quarter_of_large_norm_and_relative_error hlarge'
    (J0_sub_verticalLeadingTerm_bound hz hρ hy)
  rwa [norm_verticalLeadingTerm] at hh

end J0RadialUniqueness
