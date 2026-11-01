import Solutions.J0RadialUniqueness.BesselResidueCoefficients
import Solutions.J0RadialUniqueness.SpectralZeroStrip
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual compact-interval convergence of the cosine spectral construction.
The growth in the imaginary direction is bounded using the proved one-point
localization, and the majorant is summed on the actual right-half-plane root
subtype. No zero enumeration or uniform convergence premise is supplied. -/

noncomputable section
open Set

namespace J0RadialUniqueness

theorem norm_complex_cos_le_exp_abs_im (w : ℂ) :
    ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h := norm_add_le (Complex.exp (w * Complex.I))
    (Complex.exp (-w * Complex.I))
  rw [← Complex.two_cos] at h
  have ht : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  simp only [norm_mul, ht, Complex.norm_exp, Complex.mul_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, Complex.neg_im, neg_neg] at h
  have h₁ := Real.exp_le_exp.mpr (neg_le_abs w.im)
  have h₂ := Real.exp_le_exp.mpr (le_abs_self w.im)
  linarith

theorem one_point_exp_abs_im_bound {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    Real.exp |z.im| < 4 * ‖z‖ := by
  have hl := globalLocalization z hz hJ
  have hp := principal_one_point_exp_im_bound (J0_quadrantRep z hJ)
    (quadrantRep_in_principalSector z hl.1 hl.2.1)
  rw [norm_quadrantRep] at hp
  exact hp

theorem norm_cos_one_point_real_mul_le {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1)
    {T x : ℝ} (hT : 0 ≤ T) (hx : |x| ≤ T) :
    ‖Complex.cos (z * (x : ℂ))‖ ≤ (4 : ℝ) ^ T * ‖z‖ ^ T := by
  have he : Real.exp (T * |z.im|) ≤ (4 * ‖z‖) ^ T := by
    rw [mul_comm T, Real.exp_mul]
    exact Real.rpow_le_rpow (Real.exp_pos _).le (one_point_exp_abs_im_bound hz hJ).le hT
  calc
    _ ≤ Real.exp |(z * (x : ℂ)).im| := norm_complex_cos_le_exp_abs_im _
    _ ≤ Real.exp (T * |z.im|) := by
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, abs_mul]
      nlinarith [abs_nonneg z.im]
    _ ≤ _ := he.trans_eq (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg z))

def besselCosineSeries (M : ℕ) (x : ℝ) : ℂ :=
  ∑' z : RightOnePoint, besselResidueCoefficient M z * Complex.cos ((z : ℂ) * (x : ℂ))

theorem besselCosineSeries_compact_majorant (M : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hMT : T < 2 * M - 1) :
    Summable (fun z : RightOnePoint =>
      (4 : ℝ) ^ T * (‖besselResidueCoefficient M z‖ * ‖(z : ℂ)‖ ^ T)) ∧
      ∀ z : RightOnePoint, ∀ x ∈ Icc (-T) T,
        ‖besselResidueCoefficient M z * Complex.cos ((z : ℂ) * (x : ℂ))‖ ≤
          (4 : ℝ) ^ T * (‖besselResidueCoefficient M z‖ * ‖(z : ℂ)‖ ^ T) := by
  have hs := (besselResidueCoefficient_weight_summable M hMT).subtype
    (fun z : onePoints => 0 < (z : ℂ).re)
  refine ⟨hs.mul_left _, ?_⟩
  intro z x hx
  have hh := norm_cos_one_point_real_mul_le z.val.property.1 z.val.property.2 hT
    (abs_le.mpr hx)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)

theorem besselCosineSeries_summable (M : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hMT : T < 2 * M - 1) {x : ℝ} (hx : x ∈ Icc (-T) T) :
    Summable (fun z : RightOnePoint =>
      besselResidueCoefficient M z * Complex.cos ((z : ℂ) * (x : ℂ))) :=
  Summable.of_norm_bounded (besselCosineSeries_compact_majorant M hT hMT).1
    (fun z => (besselCosineSeries_compact_majorant M hT hMT).2 z x hx)

theorem besselCosineSeries_continuousOn (M : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hMT : T < 2 * M - 1) :
    ContinuousOn (besselCosineSeries M) (Icc (-T) T) := by
  obtain ⟨hs, hb⟩ := besselCosineSeries_compact_majorant M hT hMT
  apply continuousOn_tsum _ hs hb
  intro z
  exact (by fun_prop : Continuous (fun x : ℝ =>
    besselResidueCoefficient M z * Complex.cos ((z : ℂ) * (x : ℂ)))).continuousOn

end J0RadialUniqueness
