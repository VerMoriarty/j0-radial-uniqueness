import Solutions.J0RadialUniqueness.BranchGeometry
import Solutions.J0RadialUniqueness.LaplaceKernel
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

theorem sector_plus_base_norm_sq {z : ℂ} (hz : ClosedPrincipalSector z)
    {t : ℝ} (ht : 0 ≤ t) : 1 ≤ ‖1 + Complex.I * (t : ℂ) / (2 * z)‖ ^ 2 := by
  have hzn : z ≠ 0 := rightHalfPlane_ne_zero hz.2.2
  have hzp : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzn)
  have he : 1 + Complex.I * (t : ℂ) / (2 * z) = (z + Complex.I * (t : ℂ) / 2) / z := by
    field_simp
  have hnum : ‖z‖ ^ 2 ≤ ‖z + Complex.I * (t : ℂ) / 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [mul_nonneg ht hz.1, sq_nonneg (t / 2)]
  rw [he, norm_div, div_pow]
  exact (one_le_div hzp).mpr hnum

theorem sector_minus_base_norm_sq {z : ℂ} (hz : ClosedPrincipalSector z) (t : ℝ) :
    (1 / 2 : ℝ) ≤ ‖1 - Complex.I * (t : ℂ) / (2 * z)‖ ^ 2 := by
  have hzn : z ≠ 0 := rightHalfPlane_ne_zero hz.2.2
  have hzp : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzn)
  have he : 1 - Complex.I * (t : ℂ) / (2 * z) = (z - Complex.I * (t : ℂ) / 2) / z := by
    field_simp
  rw [he, norm_div, div_pow]
  exact (le_div_iff₀ hzp).mpr (sector_shift_norm_sq hz t)

theorem norm_cpow_neg_three_halves_le_of_sq_bound {v : ℂ}
    (hv : (1 / 2 : ℝ) ≤ ‖v‖ ^ 2) :
    ‖Complex.cpow v (-3 / 2 : ℂ)‖ ≤ Real.rpow 2 (3 / 4 : ℝ) := by
  have he : Real.rpow ‖v‖ (-3 / 2 : ℝ) = Real.rpow (‖v‖ ^ 2) (-3 / 4 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hv
    (by norm_num : (-3 / 4 : ℝ) ≤ 0)
  have hc : Real.rpow (1 / 2 : ℝ) (-3 / 4 : ℝ) = Real.rpow 2 (3 / 4 : ℝ) := by
    rw [Real.rpow_eq_pow, one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  have hn : ‖Complex.cpow v (-3 / 2 : ℂ)‖ = Real.rpow ‖v‖ (-3 / 2 : ℝ) := by
    simpa only [Complex.cpow_eq_pow, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Real.rpow_eq_pow] using Complex.norm_cpow_real v (-3 / 2 : ℝ)
  rw [hn, he]
  exact h.trans_eq hc

theorem plus_three_halves_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.cpow (1 + Complex.I * (t : ℂ) / (2 * z)) (-3 / 2 : ℂ)‖ ≤
      Real.rpow 2 (3 / 4 : ℝ) :=
  norm_cpow_neg_three_halves_le_of_sq_bound (by
    have hh := sector_plus_base_norm_sq hz ht
    linarith)

theorem minus_three_halves_bound {z : ℂ} (hz : ClosedPrincipalSector z) (t : ℝ) :
    ‖Complex.cpow (1 - Complex.I * (t : ℂ) / (2 * z)) (-3 / 2 : ℂ)‖ ≤
      Real.rpow 2 (3 / 4 : ℝ) :=
  norm_cpow_neg_three_halves_le_of_sq_bound (sector_minus_base_norm_sq hz t)

end J0RadialUniqueness
