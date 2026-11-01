import Definitions.J0RadialUniqueness.Analytic
import Mathlib.Tactic

namespace J0RadialUniqueness

theorem rightHalfPlane_ne_zero {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro hh
  simpa [hh] using hz

theorem imaginary_kernel_im (z : ℂ) (t : ℝ) :
    (Complex.I * (t : ℂ) / (2 * z)).im = t * z.re / (2 * Complex.normSq z) := by
  simp [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.normSq_mul]
  ring

/-- The two line segments used by the amplitude argument stay on the fixed branch. -/
theorem amplitude_bases_mem_slitPlane {z : ℂ} (hz : 0 < z.re)
    {t : ℝ} (ht : 0 ≤ t) :
    (1 + Complex.I * (t : ℂ) / (2 * z)) ∈ Complex.slitPlane ∧
    (1 - Complex.I * (t : ℂ) / (2 * z)) ∈ Complex.slitPlane := by
  by_cases hzero : t = 0
  · simp [hzero]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
  have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr (rightHalfPlane_ne_zero hz)
  have hi : 0 < (Complex.I * (t : ℂ) / (2 * z)).im := by
    rw [imaginary_kernel_im]
    positivity
  constructor
  · right
    simp only [Complex.add_im, Complex.one_im, zero_add]
    exact hi.ne'
  · right
    simp only [Complex.sub_im, Complex.one_im, zero_sub]
    exact neg_ne_zero.mpr hi.ne'

/-- The numerator after completing the square gives the uniform one-half lower bound. -/
theorem sector_shift_norm_sq {z : ℂ} (hz : ClosedPrincipalSector z) (t : ℝ) :
    (1 / 2 : ℝ) * ‖z‖ ^ 2 ≤ ‖z - Complex.I * (t : ℂ) / 2‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hyx : z.im * z.im ≤ z.re * z.re := by nlinarith [hz.1, hz.2.1, hz.2.2]
  nlinarith [sq_nonneg (z.im - t / 2)]

end J0RadialUniqueness
