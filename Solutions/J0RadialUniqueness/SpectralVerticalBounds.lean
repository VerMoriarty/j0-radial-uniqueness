import Solutions.J0RadialUniqueness.Main
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Uniform lower bounds for the actual Bessel mean-defect denominator on
vertical lines. Principal-branch phase, amplitude errors and both height ranges
are treated using the already proved exact decomposition. -/

noncomputable section

namespace J0RadialUniqueness

def verticalLeadingTerm (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4)) /
    Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)

def verticalSubdominantTerm (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (z - (Real.pi : ℂ) / 4)) /
    Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)

theorem norm_verticalLeadingTerm (z : ℂ) :
    ‖verticalLeadingTerm z‖ = Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖) := by
  unfold verticalLeadingTerm
  rw [norm_div, norm_half_power_denominator, Complex.norm_exp]
  congr 2
  simp

theorem norm_verticalSubdominantTerm (z : ℂ) :
    ‖verticalSubdominantTerm z‖ = Real.exp (-z.im) / Real.sqrt (2 * Real.pi * ‖z‖) := by
  unfold verticalSubdominantTerm
  rw [norm_div, norm_half_power_denominator, Complex.norm_exp]
  congr 2
  simp

/-- The principal half-power preserves the upper half-plane. The proof uses
the actual principal logarithm, including its argument convention. -/
theorem principal_half_power_im_nonneg {w : ℂ} (hw : w ≠ 0) (hi : 0 ≤ w.im) :
    0 ≤ (Complex.cpow w (1 / 2 : ℂ)).im := by
  rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hw]
  have hlo : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hi
  have hhi := Complex.arg_le_pi w
  have hsin : 0 ≤ Real.sin (w.arg / 2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by
    simp [Complex.mul_im, Complex.log_im]
    <;> ring
  rw [Complex.exp_im, him]
  exact mul_nonneg (Real.exp_pos _).le hsin

/-- At the chosen real parts the oscillatory numerator is exactly negative
imaginary, before division by the principal square root. -/
theorem verticalLeadingNumerator_phase {z : ℂ} (n : ℕ)
    (hline : z.re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4) :
    Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4)) =
      -Complex.I * (Real.exp z.im : ℂ) := by
  have he : -Complex.I * (z - (Real.pi : ℂ) / 4) =
      (z.im : ℂ) + -((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
        (-(Real.pi : ℂ) / 2 * Complex.I) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, hline] <;> push_cast <;> ring
  rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_neg,
    Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_neg_pi_div_two_mul_I,
    ← Complex.ofReal_exp]
  simp only [inv_one, mul_one]
  ring

theorem verticalLeadingTerm_re_nonpos {z : ℂ} (hz : ClosedPrincipalSector z)
    (n : ℕ) (hline : z.re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4) :
    (verticalLeadingTerm z).re ≤ 0 := by
  let D : ℂ := Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)
  have hw0 : 2 * (Real.pi : ℂ) * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (rightHalfPlane_ne_zero hz.2.2)
  have hwi : 0 ≤ (2 * (Real.pi : ℂ) * z).im := by
    have hzi := hz.1
    simp only [Complex.mul_im, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
    have hpi : 0 ≤ (2 : ℝ) * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
    exact mul_nonneg hpi hzi
  have hDi : 0 ≤ D.im := principal_half_power_im_nonneg hw0 hwi
  have hNr : (-Complex.I * (Real.exp z.im : ℂ)).re = 0 := by simp
  have hNi : (-Complex.I * (Real.exp z.im : ℂ)).im = -Real.exp z.im := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add,
      neg_zero, neg_one_mul]
  unfold verticalLeadingTerm
  rw [verticalLeadingNumerator_phase n hline]
  change ((-Complex.I * (Real.exp z.im : ℂ)) / D).re ≤ 0
  rw [Complex.div_re, hNr, hNi]
  simp only [zero_mul, zero_div, zero_add]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hDi)
    (Complex.normSq_nonneg D)

/-- A half-plane geometric bound, with no assumption on the size of `G`. -/
theorem norm_one_sub_ge_half_one_add_norm {G : ℂ} (hG : G.re ≤ 0) :
    (1 + ‖G‖) / 2 ≤ ‖1 - G‖ := by
  have h1 : 1 ≤ ‖1 - G‖ := by
    have hr := Complex.re_le_norm (1 - G)
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith
  have hsqG := Complex.sq_norm_sub_sq_re G
  have hsq1 := Complex.sq_norm_sub_sq_re (1 - G)
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    zero_sub, neg_sq] at hsq1
  have h2 : ‖G‖ ≤ ‖1 - G‖ := by
    nlinarith [norm_nonneg G, norm_nonneg (1 - G)]
  linarith

/-- The geometric lower bound is stable under a quarter-relative error. -/
theorem norm_one_sub_ge_quarter_of_relative_error {G J : ℂ}
    (hG : G.re ≤ 0) (herr : ‖J - G‖ ≤ ‖G‖ / 4) :
    (1 + ‖G‖) / 4 ≤ ‖1 - J‖ := by
  have hbase := norm_one_sub_ge_half_one_add_norm hG
  have ht := norm_add_le (1 - J) (J - G)
  have heq : (1 - J) + (J - G) = 1 - G := by ring
  rw [heq] at ht
  linarith

theorem J0_eq_vertical_components {z : ℂ} (hz : 0 < z.re) :
    J0 z = verticalLeadingTerm z * AMinus z + verticalSubdominantTerm z * APlus z := by
  rw [exact_decomposition z hz]
  unfold verticalLeadingTerm verticalSubdominantTerm
  ring

theorem norm_verticalSubdominant_eq_exp_mul (z : ℂ) :
    ‖verticalSubdominantTerm z‖ = Real.exp (-2 * z.im) * ‖verticalLeadingTerm z‖ := by
  rw [norm_verticalSubdominantTerm, norm_verticalLeadingTerm]
  have he : Real.exp (-2 * z.im) * Real.exp z.im = Real.exp (-z.im) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_div_assoc, he]

theorem exp_neg_two_im_le_sixteenth {z : ℂ} (hy : (2 : ℝ) ≤ z.im) :
    Real.exp (-2 * z.im) ≤ (1 / 16 : ℝ) := by
  have h16 : (16 : ℝ) < Real.exp (2 * z.im) :=
    exp_fourteen_fifths_gt_sixteen.trans_le (Real.exp_le_exp.mpr (by linarith))
  rw [show -2 * z.im = -(2 * z.im) by ring, Real.exp_neg]
  have hi : (Real.exp (2 * z.im))⁻¹ < (16 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos (2 * z.im)) (by norm_num)).mpr h16
  simpa only [one_div] using hi.le

/-- The exact amplitude integrals give a small relative error for the actual
dominant term at height at least two. -/
theorem J0_sub_verticalLeadingTerm_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    (hρ : 4 ≤ ‖z‖) (hy : (2 : ℝ) ≤ z.im) :
    ‖J0 z - verticalLeadingTerm z‖ ≤ ‖verticalLeadingTerm z‖ / 4 := by
  have hm := (amplitude_uniform_estimates z hz).2.1
  have hmerr : ‖AMinus z - 1‖ ≤ (1 / 16 : ℝ) :=
    (hm.trans_lt (kappa_div_lt_one_sixteenth hρ)).le
  have hp : ‖APlus z‖ ≤ (17 / 16 : ℝ) :=
    (amplitude_modulus_bounds z hz hρ).2.1.le
  have he := exp_neg_two_im_le_sixteenth hy
  have hdecomp : J0 z - verticalLeadingTerm z =
      verticalLeadingTerm z * (AMinus z - 1) + verticalSubdominantTerm z * APlus z := by
    rw [J0_eq_vertical_components hz.2.2]
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖verticalLeadingTerm z‖ * ‖AMinus z - 1‖ +
        ‖verticalSubdominantTerm z‖ * ‖APlus z‖ := by
      simpa only [norm_mul] using norm_add_le
        (verticalLeadingTerm z * (AMinus z - 1)) (verticalSubdominantTerm z * APlus z)
    _ ≤ ‖verticalLeadingTerm z‖ * (1 / 16) +
        (Real.exp (-2 * z.im) * ‖verticalLeadingTerm z‖) * (17 / 16) := by
      rw [norm_verticalSubdominant_eq_exp_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmerr (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hp (by positivity))
    _ ≤ ‖verticalLeadingTerm z‖ / 4 := by
      have hh := mul_le_mul_of_nonneg_right he (norm_nonneg (verticalLeadingTerm z))
      nlinarith [norm_nonneg (verticalLeadingTerm z)]

theorem spectral_vertical_high_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    (n : ℕ) (hline : z.re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4)
    (hρ : 4 ≤ ‖z‖) (hy : (2 : ℝ) ≤ z.im) :
    (1 + Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) / 4 ≤ ‖1 - J0 z‖ := by
  have h := norm_one_sub_ge_quarter_of_relative_error
    (verticalLeadingTerm_re_nonpos hz n hline) (J0_sub_verticalLeadingTerm_bound hz hρ hy)
  rwa [norm_verticalLeadingTerm] at h

theorem J0_norm_le_amplitude_majorant {z : ℂ} (hz : ClosedPrincipalSector z)
    (hρ : 4 ≤ ‖z‖) :
    ‖J0 z‖ ≤ (17 / 16 : ℝ) * (Real.exp z.im + Real.exp (-z.im)) /
      Real.sqrt (2 * Real.pi * ‖z‖) := by
  obtain ⟨_, hp, _, hm, _, _⟩ := amplitude_modulus_bounds z hz hρ
  rw [J0_eq_vertical_components hz.2.2]
  calc
    _ ≤ ‖verticalLeadingTerm z‖ * ‖AMinus z‖ +
        ‖verticalSubdominantTerm z‖ * ‖APlus z‖ := by
      simpa only [norm_mul] using norm_add_le
        (verticalLeadingTerm z * AMinus z) (verticalSubdominantTerm z * APlus z)
    _ ≤ ‖verticalLeadingTerm z‖ * (17 / 16) +
        ‖verticalSubdominantTerm z‖ * (17 / 16) :=
      add_le_add (mul_le_mul_of_nonneg_left hm.le (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hp.le (norm_nonneg _))
    _ = _ := by rw [norm_verticalLeadingTerm, norm_verticalSubdominantTerm]; ring

theorem exp_two_lt_nine : Real.exp (2 : ℝ) < 9 := by
  have he : Real.exp (2 : ℝ) = Real.exp (1 : ℝ) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]
  rw [he]
  nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 : ℝ)]

/-- A deliberately generous fixed radial cutoff for the bounded-height range. -/
theorem sqrt_denominator_ge_thirty_two {z : ℂ} (hρ : (256 : ℝ) ≤ ‖z‖) :
    (32 : ℝ) ≤ Real.sqrt (2 * Real.pi * ‖z‖) := by
  apply Real.le_sqrt_of_sq_le
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (norm_nonneg z)
  nlinarith

theorem spectral_low_height_small_norms {z : ℂ} (hz : ClosedPrincipalSector z)
    (hρ : (256 : ℝ) ≤ ‖z‖) (hy : z.im ≤ 2) :
    ‖J0 z‖ ≤ (1 / 2 : ℝ) ∧ ‖verticalLeadingTerm z‖ ≤ (1 / 2 : ℝ) := by
  have hD := sqrt_denominator_ge_thirty_two hρ
  have hDpos : 0 < Real.sqrt (2 * Real.pi * ‖z‖) := by linarith
  have he : Real.exp z.im ≤ 9 :=
    (Real.exp_le_exp.mpr hy).trans exp_two_lt_nine.le
  have hm : Real.exp (-z.im) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hz.1])
  have hJ := (le_div_iff₀ hDpos).mp
    (J0_norm_le_amplitude_majorant hz (by linarith : (4 : ℝ) ≤ ‖z‖))
  have hscaled := mul_le_mul_of_nonneg_left hD (norm_nonneg (J0 z))
  constructor
  · nlinarith
  · rw [norm_verticalLeadingTerm]
    apply (div_le_iff₀ hDpos).mpr
    linarith

/-- In bounded height the full Bessel function itself is small. This estimate
does not need the vertical phase condition. -/
theorem spectral_low_height_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    (hρ : (256 : ℝ) ≤ ‖z‖) (hy : z.im ≤ 2) :
    (1 + Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) / 4 ≤ ‖1 - J0 z‖ := by
  obtain ⟨hJ, hG⟩ := spectral_low_height_small_norms hz hρ hy
  have hr := norm_sub_norm_le (1 : ℂ) (J0 z)
  simp only [norm_one] at hr
  rw [norm_verticalLeadingTerm] at hG
  linarith

/-- A uniform denominator lower bound on every specified vertical line, once
the actual radius is at least the explicit fixed cutoff. -/
theorem spectral_vertical_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    (n : ℕ) (hline : z.re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4)
    (hρ : (256 : ℝ) ≤ ‖z‖) :
    (1 + Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) / 4 ≤ ‖1 - J0 z‖ := by
  rcases le_total z.im 2 with hy | hy
  · exact spectral_low_height_bound hz hρ hy
  · exact spectral_vertical_high_bound hz n hline (by linarith) hy

theorem spectral_vertical_bound_of_index_ge_hundred {z : ℂ}
    (hz : ClosedPrincipalSector z) {n : ℕ} (hn : 100 ≤ n)
    (hline : z.re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4) :
    (1 + Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) / 4 ≤ ‖1 - J0 z‖ := by
  have hnR : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hre := Complex.re_le_norm z
  have hρ : (256 : ℝ) ≤ ‖z‖ := by rw [hline] at hre; nlinarith [Real.pi_pos]
  exact spectral_vertical_bound hz n hline hρ

end J0RadialUniqueness
