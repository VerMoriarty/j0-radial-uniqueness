import Definitions.J0RadialUniqueness.Analytic
import Solutions.J0RadialUniqueness.Constants
import Solutions.J0RadialUniqueness.ZeroFree
import Solutions.J0RadialUniqueness.Conditional.RadialCalculus
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

/-- The norm estimate in Section 5, with the actual complex error terms. -/
theorem complex_radial_error_bound (z a b d d' : ℂ)
    (ha : ‖a‖ < (1 / 15 : ℝ)) (hb : ‖b‖ < (1 / 15 : ℝ))
    (hd : ‖d‖ < (17 / 240 : ℝ)) (hzd : ‖z‖ * ‖d‖ < (187 / 750 : ℝ))
    (heq : z * d' = d * (2 * Complex.I * z + a - b)) :
    ‖b + z * d' / (1 + d)‖ < (31 / 50 : ℝ) := by
  have hden : 1 - ‖d‖ ≤ ‖(1 : ℂ) + d‖ := by
    have hh := norm_sub_le ((1 : ℂ) + d) d
    rw [add_sub_cancel_right, norm_one] at hh
    linarith
  have hdenpos : 0 < 1 - ‖d‖ := by linarith
  have hT : ‖2 * Complex.I * z + a - b‖ ≤ 2 * ‖z‖ + ‖a‖ + ‖b‖ := by
    calc
      _ ≤ ‖2 * Complex.I * z + a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ (‖2 * Complex.I * z‖ + ‖a‖) + ‖b‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by simp [norm_mul]
  have hn : ‖d‖ * ‖2 * Complex.I * z + a - b‖ ≤
      2 * (‖z‖ * ‖d‖) + (‖b‖ + ‖a‖) * ‖d‖ := by
    calc
      _ ≤ ‖d‖ * (2 * ‖z‖ + ‖a‖ + ‖b‖) :=
        mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ = _ := by ring
  have hdiv : ‖z * d' / (1 + d)‖ ≤
      (2 * (‖z‖ * ‖d‖) + (‖b‖ + ‖a‖) * ‖d‖) / (1 - ‖d‖) := by
    rw [heq, norm_div, norm_mul]
    exact div_le_div₀ (by positivity) hn hdenpos hden
  calc
    _ ≤ ‖b‖ + ‖z * d' / (1 + d)‖ := norm_add_le _ _
    _ ≤ ‖b‖ + (2 * (‖z‖ * ‖d‖) + (‖b‖ + ‖a‖) * ‖d‖) / (1 - ‖d‖) :=
      add_le_add le_rfl hdiv
    _ < _ := radial_error_bound hb.le ha.le (norm_nonneg _) hd.le hzd.le

/-- The analytic premises used for Proposition 5.1 are explicit and remain open. -/
theorem principalRadialEscape_of_analytic_inputs
    (hsep : QuantitativeSeparationStatement) (hray : RaySeparationStatement)
    (hamp : AmplitudeModulusBoundsStatement) (hdelta : DeltaDerivativeStatement)
    (hdecomp : RadialDerivativeDecompositionStatement) : PrincipalRadialEscapeStatement := by
  intro z hJ hp
  have hy := (hsep z hJ hp).2.1
  have hderivative (τ : ℝ) (hτ : 1 ≤ τ) :
      DifferentiableAt ℝ (rayLogNorm z) τ ∧ (7 / 25 : ℝ) < rayLogDerivative z τ := by
    let w : ℂ := (τ : ℂ) * z
    have hτpos : 0 < τ := by linarith
    have hwim : w.im = τ * z.im := by simp [w]
    have hwre : w.re = τ * z.re := by simp [w]
    have hclosed : ClosedPrincipalSector w := by
      have hzre : 0 < z.re := lt_trans hp.1 hp.2
      refine ⟨?_, ?_, ?_⟩
      · rw [hwim]; positivity
      · rw [hwim, hwre]; exact mul_le_mul_of_nonneg_left hp.2.le hτpos.le
      · rw [hwre]; exact mul_pos hτpos hzre
    have hs := hray z hJ hp τ hτ
    have hwfour : 4 ≤ ‖w‖ := by
      have hs₀ : 4 ≤ ‖z‖ := by
        have : z ≠ 0 := by intro hz; simpa [hz] using hp.1
        exact one_point_norm_ge_four z this hJ
      have hw : ‖w‖ = τ * ‖z‖ := by simp [w, norm_mul, abs_of_pos hτpos]
      rw [hw]
      nlinarith [norm_nonneg z]
    have ham := hamp w hclosed hwfour
    have he := complex_radial_error_bound w
      (w * deriv APlus w / APlus w) (w * deriv AMinus w / AMinus w)
      (delta w) (deriv delta w) ham.2.2.2.2.1 ham.2.2.2.2.2
      hs.2.1 hs.2.2.1 (hdelta w hs.1)
    have hd := hdecomp z hJ hp τ hτ
    have hyw : (7 / 5 : ℝ) < w.im := by
      rw [hwim]
      nlinarith [hp.1]
    refine ⟨hd.1, ?_⟩
    apply radial_derivative_lower_bound hyw _ hd.2
    have hreal := Complex.abs_re_le_norm
      (w * deriv AMinus w / AMinus w + w * deriv delta w / (1 + delta w))
    exact (abs_lt.mp (lt_of_le_of_lt hreal he)).1
  refine ⟨hderivative, ?_⟩
  intro c hc
  have hstart : rayLogNorm z 1 = 0 := by simp [rayLogNorm, hJ]
  have hg := logarithmic_growth_seven_twentyfifths (rayLogNorm z)
    (deriv (rayLogNorm z)) hstart
    (fun t ht => (hderivative t ht).1.hasDerivAt)
    (fun t ht => (hderivative t ht).2) hc
  have hexp := Real.exp_lt_exp.mpr hg
  have hnz : J0 ((c : ℂ) * z) ≠ 0 := (hray z hJ hp c hc.le).2.2.2
  rw [rayLogNorm, Real.exp_log (norm_pos_iff.mpr hnz)] at hexp
  simpa [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < c), mul_comm,
    Real.rpow_eq_pow] using hexp

end J0RadialUniqueness
