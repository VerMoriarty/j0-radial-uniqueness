import Solutions.J0RadialUniqueness.PlanarGreenKernel
import Mathlib.Tactic

/-!
Actual compact complex radial kernels and polar integration. The radial
Jacobian is assumed integrable, rather than the possibly singular density.
The original planar product and the complete polar product are both proved
integrable before Fubini is used.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology Interval ENNReal

namespace J0RadialUniqueness

def compactRadialComplexKernel (r : ℝ) (b : ℝ → ℂ) (y : Plane) : ℂ :=
  if ‖y‖ < r then b ‖y‖ else 0

def complexPolarJacobian (r : ℝ) (b : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Ioo (0 : ℝ) r).indicator (fun t : ℝ => (t : ℂ) * b t) t

theorem measurable_compactRadialComplexKernel (r : ℝ) {b : ℝ → ℂ} (hb : Measurable b) :
    Measurable (compactRadialComplexKernel r b) := by
  unfold compactRadialComplexKernel
  exact Measurable.ite (measurableSet_lt measurable_norm measurable_const)
    (hb.comp measurable_norm) measurable_const

theorem compactRadialComplexKernel_radial (r : ℝ) (b : ℝ → ℂ) (y z : Plane)
    (h : ‖y‖ = ‖z‖) : compactRadialComplexKernel r b y = compactRadialComplexKernel r b z := by
  simp only [compactRadialComplexKernel, h]

@[simp] theorem compactRadialComplexKernel_neg (r : ℝ) (b : ℝ → ℂ) (y : Plane) :
    compactRadialComplexKernel r b (-y) = compactRadialComplexKernel r b y := by
  simp only [compactRadialComplexKernel, norm_neg]

theorem compactRadialComplexKernel_support_radius (r : ℝ) (b : ℝ → ℂ) {y : Plane}
    (hy : compactRadialComplexKernel r b y ≠ 0) : ‖y‖ ≤ r := by
  by_contra h
  exact hy (by simp only [compactRadialComplexKernel, if_neg (not_lt.mpr (le_of_not_ge h))])

theorem compactRadialComplexKernel_hasCompactSupport (r : ℝ) (b : ℝ → ℂ) :
    HasCompactSupport (compactRadialComplexKernel r b) := by
  have hs : tsupport (compactRadialComplexKernel r b) ⊆ Metric.closedBall (0 : Plane) r := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      compactRadialComplexKernel_support_radius r b hy
  exact (isCompact_closedBall (0 : Plane) r).of_isClosed_subset
    (isClosed_tsupport (compactRadialComplexKernel r b)) hs

theorem complexPolarJacobian_integrable {r : ℝ} (hr : 0 < r) {b : ℝ → ℂ}
    (hb : IntervalIntegrable (fun t : ℝ => (t : ℂ) * b t) volume 0 r) :
    Integrable (complexPolarJacobian r b) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp hb
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (hi.mono_set Ioo_subset_Ioc_self)

theorem compactRadialComplexKernel_polar_jacobian {r t : ℝ} (b : ℝ → ℂ)
    (ht : 0 < t) (θ : ℝ) :
    (t : ℂ) * compactRadialComplexKernel r b (t • circleDirection θ) =
      complexPolarJacobian r b t := by
  by_cases htr : t < r
  · change (t : ℂ) * compactRadialComplexKernel r b (t • circleDirection θ) =
      (Ioo (0 : ℝ) r).indicator (fun u : ℝ => (u : ℂ) * b u) t
    rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) r from ⟨ht, htr⟩)]
    simp only [compactRadialComplexKernel, norm_smul, Real.norm_eq_abs,
      norm_circleDirection, mul_one, abs_of_pos ht, if_pos htr]
  · simp [compactRadialComplexKernel, norm_smul, abs_of_pos ht, htr,
      complexPolarJacobian, show t ∉ Ioo (0 : ℝ) r from fun h => htr h.2]

/-- The full polar product is dominated by the integrable norm of the radial
Jacobian times a genuine bound for f on its compact translated ball. -/
theorem compactRadialComplexKernel_polar_integrable {r : ℝ} (hr : 0 < r)
    {b : ℝ → ℂ} (hbm : Measurable b)
    (hbi : IntervalIntegrable (fun t : ℝ => (t : ℂ) * b t) volume 0 r)
    {f : Plane → ℂ} (hf : Continuous f) (x : Plane) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 •
      (compactRadialComplexKernel r b (planePolar p) * f (x - planePolar p)))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
  have hfc : Continuous (fun y : Plane => f (x - y)) :=
    hf.comp (continuous_const.sub continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Plane) r).exists_bound_of_continuousOn hfc.continuousOn
  have hbase : IntegrableOn (fun p : ℝ × ℝ => ‖complexPolarJacobian r b p.1‖ * C)
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    have hh := ((((complexPolarJacobian_integrable hr hbi).norm).integrableOn
      (s := Ioi (0 : ℝ))).comp_fst (volume.restrict (Ioo (-Real.pi) Real.pi))).mul_const C
    simp only [Measure.prod_restrict] at hh
    exact hh
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 •
      (compactRadialComplexKernel r b (planePolar p) * f (x - planePolar p)))
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)) := by
    exact (measurable_fst.stronglyMeasurable.smul
      ((((measurable_compactRadialComplexKernel r hbm).comp continuous_planePolar.measurable).stronglyMeasurable).mul
        (hf.comp (continuous_const.sub continuous_planePolar)).stronglyMeasurable)).aestronglyMeasurable
  apply hbase.mono' hm
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  have ht : 0 < p.1 := hp.1
  rw [Complex.real_smul, ← mul_assoc, planePolar_eq,
    compactRadialComplexKernel_polar_jacobian b ht, norm_mul]
  by_cases htr : p.1 < r
  · have hy : planePolar p ∈ Metric.closedBall (0 : Plane) r := by
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_planePolar, abs_of_pos ht] using htr.le
    have hc := hC (planePolar p) hy
    rw [planePolar_eq] at hc
    exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  · simp [complexPolarJacobian, show p.1 ∉ Ioo (0 : ℝ) r from fun h => htr h.2]

/-- Integrability of the actual plane integral follows from polar domination,
including densities which are unbounded at zero. -/
theorem compactRadialComplexKernel_integrable_mul {r : ℝ} (hr : 0 < r)
    {b : ℝ → ℂ} (hbm : Measurable b)
    (hbi : IntervalIntegrable (fun t : ℝ => (t : ℂ) * b t) volume 0 r)
    {f : Plane → ℂ} (hf : Continuous f) (x : Plane) :
    Integrable (fun y : Plane => compactRadialComplexKernel r b y * f (x - y)) := by
  have hpol := compactRadialComplexKernel_polar_integrable hr hbm hbi hf x
  refine ⟨((measurable_compactRadialComplexKernel r hbm).stronglyMeasurable.mul
    (hf.comp (continuous_const.sub continuous_id)).stronglyMeasurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, plane_lintegral_eq_polar]
  have hfinite := hpol.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfinite
  convert hfinite using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  simp only [enorm_smul, Real.enorm_of_nonneg (show 0 ≤ p.1 from hp.1.le)]

/-- Actual polar/Fubini formula for a measurable complex radial density with
integrable radial Jacobian. -/
theorem compactRadialComplexKernel_integral_eq_radial {r : ℝ} (hr : 0 < r)
    {b : ℝ → ℂ} (hbm : Measurable b)
    (hbi : IntervalIntegrable (fun t : ℝ => (t : ℂ) * b t) volume 0 r)
    {f : Plane → ℂ} (hf : Continuous f) (x : Plane) :
    (∫ y : Plane, compactRadialComplexKernel r b y * f (x - y)) =
      ∫ t : ℝ in (0 : ℝ)..r, (2 * (Real.pi : ℂ) * (t : ℂ)) * b t * circularMean f t x := by
  have hp := compactRadialComplexKernel_polar_integrable hr hbm hbi hf x
  calc
    _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (compactRadialComplexKernel r b (planePolar p) * f (x - planePolar p))
          ∂(volume.prod volume) := plane_integral_eq_polar _
    _ = ∫ t : ℝ in Ioi (0 : ℝ), ∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
        complexPolarJacobian r b t * f (x + (-t) • circleDirection θ) := by
      rw [setIntegral_prod _ hp]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      change t • (compactRadialComplexKernel r b (planePolar (t, θ)) * f (x - planePolar (t, θ))) = _
      rw [Complex.real_smul, ← mul_assoc, planePolar_eq,
        compactRadialComplexKernel_polar_jacobian b ht]
      simp only [neg_smul, sub_eq_add_neg]
    _ = ∫ t : ℝ in Ioi (0 : ℝ),
        (complexPolarJacobian r b t * (2 * (Real.pi : ℂ))) * circularMean f t x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
        complexPolarJacobian r b t * f (x + (-t) • circleDirection θ)) = _
      rw [integral_const_mul, centeredAngleIntegral_eq_circularMean,
        circularMean_neg_radius, Complex.real_smul]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    _ = ∫ t : ℝ in Ioi (0 : ℝ), (Ioo (0 : ℝ) r).indicator
        (fun t : ℝ => (2 * (Real.pi : ℂ) * (t : ℂ)) * b t * circularMean f t x) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      unfold complexPolarJacobian
      by_cases ht : t ∈ Ioo (0 : ℝ) r
      · simp only [indicator_of_mem ht]
        ring
      · simp [ht]
    _ = ∫ t : ℝ in Ioo (0 : ℝ) r,
        (2 * (Real.pi : ℂ) * (t : ℂ)) * b t * circularMean f t x := by
      rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
        inter_eq_left.mpr Ioo_subset_Ioi_self]
    _ = _ := by rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]

theorem compactRadialComplexKernel_integrable {r : ℝ} (hr : 0 < r)
    {b : ℝ → ℂ} (hbm : Measurable b)
    (hbi : IntervalIntegrable (fun t : ℝ => (t : ℂ) * b t) volume 0 r) :
    Integrable (compactRadialComplexKernel r b) := by
  simpa only [mul_one] using compactRadialComplexKernel_integrable_mul hr hbm hbi
    (f := fun _ : Plane => (1 : ℂ)) continuous_const (0 : Plane)

theorem compactRadialComplexKernel_integral {r : ℝ} (hr : 0 < r)
    {b : ℝ → ℂ} (hbm : Measurable b)
    (hbi : IntervalIntegrable (fun t : ℝ => (t : ℂ) * b t) volume 0 r) :
    (∫ y : Plane, compactRadialComplexKernel r b y) =
      ∫ t : ℝ in (0 : ℝ)..r, (2 * (Real.pi : ℂ) * (t : ℂ)) * b t := by
  simpa only [mul_one, circularMean_constant] using compactRadialComplexKernel_integral_eq_radial
    hr hbm hbi (f := fun _ : Plane => (1 : ℂ)) continuous_const (0 : Plane)

end J0RadialUniqueness
