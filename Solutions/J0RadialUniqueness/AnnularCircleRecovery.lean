import Solutions.J0RadialUniqueness.AngularChebyshevProjection
import Solutions.J0RadialUniqueness.AnnularAbelKernelReduction
import Solutions.J0RadialUniqueness.AnnularModeRecovery

/-! Actual circular means give the annular Abel equations. The endpoint
where a chord may vanish is removed only by the null-singleton integral
congruence; the geometric phase pairing is used on the open half circle. -/

noncomputable section

open MeasureTheory Set
open scoped Topology Interval ContDiff

namespace J0RadialUniqueness

theorem integral_full_circle_eq_half_reflect {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ α : ℝ in (0 : ℝ)..2 * Real.pi, F α) =
      ∫ α : ℝ in (0 : ℝ)..Real.pi, F α + F (2 * Real.pi - α) := by
  have h₁ := hF.intervalIntegrable (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := Real.pi)
  have h₂ := hF.intervalIntegrable (μ := (volume : Measure ℝ)) (a := Real.pi) (b := 2 * Real.pi)
  have h₃ : IntervalIntegrable (fun α : ℝ => F (2 * Real.pi - α)) volume 0 Real.pi :=
    (hF.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 Real.pi
  have hr : (∫ α : ℝ in (0 : ℝ)..Real.pi, F (2 * Real.pi - α)) =
      ∫ α : ℝ in Real.pi..2 * Real.pi, F α := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  rw [intervalIntegral.integral_add h₁ h₃]
  rw [hr, intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

theorem angularProjection_circularMean_eq_chebyshev_angle {f : Plane → ℂ}
    (hf : Continuous f) (m : ℤ) (ρ : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * circularMean f r (ρ • circleDirection θ)) =
      (Real.pi : ℂ)⁻¹ * ∫ α : ℝ in (0 : ℝ)..Real.pi,
        (chebyshevTValue m.natAbs
          ((circleChord ρ r α).re / ‖circleChord ρ r α‖) : ℂ) *
            helmholtzFourierMode f m ‖circleChord ρ r α‖ := by
  rw [angularProjection_circularMean_eq_chord_integral hf]
  change (2 * (Real.pi : ℂ))⁻¹ *
      (∫ α : ℝ in (0 : ℝ)..2 * Real.pi, angularFourierAt f m (circleChord ρ r α)) = _
  have hc : Continuous (fun α => angularFourierAt f m (circleChord ρ r α)) := by
    apply (continuous_angularFourierAt hf m).comp
    unfold circleChord
    fun_prop
  rw [integral_full_circle_eq_half_reflect hc]
  have hi : (∫ α : ℝ in (0 : ℝ)..Real.pi,
      angularFourierAt f m (circleChord ρ r α) +
        angularFourierAt f m (circleChord ρ r (2 * Real.pi - α))) =
      ∫ α : ℝ in (0 : ℝ)..Real.pi,
        2 * ((chebyshevTValue m.natAbs
          ((circleChord ρ r α).re / ‖circleChord ρ r α‖) : ℂ) *
            helmholtzFourierMode f m ‖circleChord ρ r α‖) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le Real.pi_pos.le]
    intro α hα
    dsimp only
    rw [circleChord_reflect,
      angularFourierAt_conjugate_pair f m (circleChord_im_pos hr hα)]
    ring
  rw [hi, intervalIntegral.integral_const_mul]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem circleChord_re (ρ r α : ℝ) :
    (circleChord ρ r α).re = ρ + r * Real.cos α := by
  simp only [circleChord, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

theorem circleChord_norm (ρ r α : ℝ) :
    ‖circleChord ρ r α‖ = annularChordRadius ρ r α := by
  have hi : (circleChord ρ r α).im = r * Real.sin α := by
    simp only [circleChord, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, zero_add, Complex.exp_ofReal_mul_I_im]
  have hs : ‖circleChord ρ r α‖ ^ 2 = ρ ^ 2 + r ^ 2 + 2 * ρ * r * Real.cos α := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, circleChord_re, hi]
    nlinarith [Real.sin_sq_add_cos_sq α]
  unfold annularChordRadius
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem annularAbel_equation_of_circularMean_zero {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r a : ℝ} (hr : 0 < r) (hra : r < a)
    (hinner : ∀ x ∈ planeBall a, u x = 0)
    (hmean : ∀ x ∈ planeBall a, circularMean u r x = 0)
    (m : ℤ) {p : ℝ} (hp : p ∈ Ioo a (a + r)) :
    (∫ s : ℝ in a..p, (Real.sqrt (p - s))⁻¹ •
      ((annularVolterraKernel m.natAbs r (p, s) : ℂ) * helmholtzFourierMode u m s)) = 0 := by
  have hρ : 0 < p - r := by linarith [hp.1]
  have hρa : p - r < a := by linarith [hp.2]
  have hproj : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * circularMean u r ((p - r) • circleDirection θ)) = 0 := by
    calc
      _ = ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [hmean _ (by
          simpa only [planeBall, Metric.mem_ball, dist_zero_right, norm_smul,
            Real.norm_eq_abs, norm_circleDirection, mul_one, abs_of_pos hρ] using hρa), mul_zero]
      _ = 0 := by simp
  rw [angularProjection_circularMean_eq_chebyshev_angle hu.continuous m (p - r) hr] at hproj
  have hv : Continuous (helmholtzFourierMode u m) :=
    continuous_iff_continuousAt.mpr fun s => (helmholtzFourierMode_hasDerivAt hu m s).continuousAt
  have hz : ∀ s ∈ Ioo |p - 2 * r| a, helmholtzFourierMode u m s = 0 := by
    intro s hs
    exact helmholtzFourierMode_eq_zero_on_smaller_ball hinner m
      (abs_nonneg _ |>.trans hs.1.le) hs.2
  have hab := annularChord_integral_eq_abel m.natAbs hr hra hp.1 hp.2 hv hz
  have he : (1 / Real.pi) • (∫ α : ℝ in (0 : ℝ)..Real.pi,
      chebyshevTValue m.natAbs (annularChordAngleArgument (p - r) r α) •
        helmholtzFourierMode u m (annularChordRadius (p - r) r α)) = 0 := by
    simpa only [circleChord_re, circleChord_norm, annularChordAngleArgument,
      Complex.real_smul, one_div, Complex.ofReal_inv] using hproj
  rw [hab] at he
  exact he

theorem eq_zero_on_larger_ball_of_circularMean_zero {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r a : ℝ} (hr : 0 < r) (hra : r < a)
    (hinner : ∀ x ∈ planeBall a, u x = 0)
    (hmean : ∀ x ∈ planeBall a, circularMean u r x = 0) :
    ∀ y ∈ planeBall (a + r), u y = 0 := by
  apply eq_zero_on_larger_ball_of_annular_abel hu hr hra hinner
  intro m p hp
  exact annularAbel_equation_of_circularMean_zero hu hr hra hinner hmean m hp

end J0RadialUniqueness
