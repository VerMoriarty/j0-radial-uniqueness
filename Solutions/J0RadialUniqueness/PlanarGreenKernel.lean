import Solutions.J0RadialUniqueness.HarmonicRadialConvolution
import Solutions.J0RadialUniqueness.CircleGreenIdentity
import Solutions.J0RadialUniqueness.LocalConvolution
import Solutions.J0RadialUniqueness.CircularBesselIntegral
import Solutions.J0RadialUniqueness.SpectralExponential
import Mathlib.Tactic

/-! The actual compact planar logarithmic Green kernel.

The kernel is measurable and integrable, not continuous at the origin. Its polar
integrability is proved by a genuine `C * t log(r/t)` majorant. The only polar
change of variables used here is Mathlib's existing one, transported by the
already established measure-preserving coordinate bridge. Fubini is invoked
only after proving integrability of the complete polar integrand.
-/

noncomputable section

open MeasureTheory Set Laplacian
open scoped Topology ContDiff Interval ENNReal

namespace J0RadialUniqueness

def planarGreenKernel (r : ℝ) (y : Plane) : ℝ :=
  if ‖y‖ < r then Real.log (r / ‖y‖) / (2 * Real.pi) else 0

def greenPolarWeight (r t : ℝ) : ℝ :=
  (Ioo (0 : ℝ) r).indicator (fun t : ℝ => greenRadialWeight r t / (2 * Real.pi)) t

theorem measurable_planarGreenKernel (r : ℝ) : Measurable (planarGreenKernel r) := by
  unfold planarGreenKernel
  apply Measurable.ite (measurableSet_lt measurable_norm measurable_const)
  · fun_prop
  · exact measurable_const

theorem planarGreenKernel_radial (r : ℝ) (y z : Plane) (h : ‖y‖ = ‖z‖) :
    planarGreenKernel r y = planarGreenKernel r z := by simp only [planarGreenKernel, h]

@[simp] theorem planarGreenKernel_neg (r : ℝ) (y : Plane) :
    planarGreenKernel r (-y) = planarGreenKernel r y := by simp [planarGreenKernel]

theorem planarGreenKernel_support_radius (r : ℝ) {y : Plane}
    (hy : planarGreenKernel r y ≠ 0) : ‖y‖ ≤ r := by
  by_contra h
  exact hy (by simp [planarGreenKernel, not_lt.mpr (le_of_not_ge h)])

theorem planarGreenKernel_hasCompactSupport (r : ℝ) : HasCompactSupport (planarGreenKernel r) := by
  have hs : tsupport (planarGreenKernel r) ⊆ Metric.closedBall (0 : Plane) r := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      planarGreenKernel_support_radius r hy
  exact (isCompact_closedBall (0 : Plane) r).of_isClosed_subset
    (isClosed_tsupport (planarGreenKernel r)) hs

theorem greenPolarWeight_integrable {r : ℝ} (hr : 0 < r) : Integrable (greenPolarWeight r) := by
  have h := (continuous_greenRadialWeight hr).intervalIntegrable (μ := volume) (0 : ℝ) r
  have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp h
  have hIoo : IntegrableOn (fun t : ℝ => greenRadialWeight r t / (2 * Real.pi)) (Ioo 0 r) :=
    (hIoc.mono_set Ioo_subset_Ioc_self).div_const _
  exact (integrable_indicator_iff measurableSet_Ioo).mpr hIoo

theorem greenPolarWeight_nonneg {r t : ℝ} (hr : 0 < r) : 0 ≤ greenPolarWeight r t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) r
  · rw [greenPolarWeight, indicator_of_mem ht]
    exact div_nonneg (greenRadialWeight_nonneg ht.1 ht.2.le) Real.two_pi_pos.le
  · simp [greenPolarWeight, ht]

theorem green_polar_jacobian {r t : ℝ} (ht : 0 < t) (θ : ℝ) :
    t * planarGreenKernel r (t • circleDirection θ) = greenPolarWeight r t := by
  by_cases htr : t < r
  · have hmem : t ∈ Ioo (0 : ℝ) r := ⟨ht, htr⟩
    change t * planarGreenKernel r (t • circleDirection θ) =
      (Ioo (0 : ℝ) r).indicator (fun u : ℝ => greenRadialWeight r u / (2 * Real.pi)) t
    rw [indicator_of_mem hmem (fun u : ℝ => greenRadialWeight r u / (2 * Real.pi))]
    simp only [planarGreenKernel, norm_smul, Real.norm_eq_abs, norm_circleDirection,
      mul_one, abs_of_pos ht, if_pos htr, greenRadialWeight]
    ring
  · simp [planarGreenKernel, norm_smul, abs_of_pos ht, htr, greenPolarWeight,
      show t ∉ Ioo (0 : ℝ) r from fun h => htr h.2]

/-- Nonnegative polar integration, using the existing complex polar theorem and
the already proved plane coordinate measure-preserving bridge. -/
theorem plane_lintegral_eq_polar (F : Plane → ℝ≥0∞) :
    (∫⁻ y : Plane, F y) =
      ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F (planePolar p) ∂(volume.prod volume) := by
  have he := Complex.orthonormalBasisOneI.measurePreserving_repr
  have hi := he.lintegral_comp_emb
    Complex.orthonormalBasisOneI.repr.toMeasurableEquiv.measurableEmbedding F
  rw [← hi]
  simpa only [planePolar, polarCoord_target, Measure.volume_eq_prod, smul_eq_mul] using
    (Complex.lintegral_comp_polarCoord_symm
      (fun z : ℂ => F (Complex.orthonormalBasisOneI.repr z))).symm

section PolarGreen

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem planarGreen_polar_integrable {g : Plane → V} (hg : Continuous g)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 • (planarGreenKernel r (planePolar p) • g (x - planePolar p)))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
  have hgc : Continuous (fun y : Plane => g (x - y)) :=
    hg.comp (continuous_const.sub continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Plane) r).exists_bound_of_continuousOn
    hgc.continuousOn
  have hbase : IntegrableOn (fun p : ℝ × ℝ => greenPolarWeight r p.1 * C)
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    have h := (((greenPolarWeight_integrable hr).integrableOn
      (s := Ioi (0 : ℝ))).comp_fst (volume.restrict (Ioo (-Real.pi) Real.pi))).mul_const C
    simp only [Measure.prod_restrict] at h
    exact h
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      p.1 • (planarGreenKernel r (planePolar p) • g (x - planePolar p)))
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)) := by
    exact (measurable_fst.stronglyMeasurable.smul
      (((measurable_planarGreenKernel r).comp continuous_planePolar.measurable).stronglyMeasurable.smul
        (hg.comp (continuous_const.sub continuous_planePolar)).stronglyMeasurable)).aestronglyMeasurable
  apply hbase.mono' hm
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  have ht : 0 < p.1 := hp.1
  rw [smul_smul, planePolar_eq, green_polar_jacobian ht, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (greenPolarWeight_nonneg hr)]
  by_cases htr : p.1 < r
  · have hy : planePolar p ∈ Metric.closedBall (0 : Plane) r := by
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_planePolar, abs_of_pos ht] using htr.le
    have hc := hC (planePolar p) hy
    rw [planePolar_eq] at hc
    exact mul_le_mul_of_nonneg_left hc (greenPolarWeight_nonneg hr)
  · simp [greenPolarWeight, show p.1 ∉ Ioo (0 : ℝ) r from fun h => htr h.2]

/-- Polar domination also establishes integrability for the original planar
Bochner integral, including the logarithmic singularity. -/
theorem planarGreen_integrable_mul {g : Plane → V} (hg : Continuous g)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : Plane => planarGreenKernel r y • g (x - y)) := by
  have hpol := planarGreen_polar_integrable hg x hr
  refine ⟨((measurable_planarGreenKernel r).stronglyMeasurable.smul
    (hg.comp (continuous_const.sub continuous_id)).stronglyMeasurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, plane_lintegral_eq_polar]
  have hfinite := hpol.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfinite
  convert hfinite using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  simp only [enorm_smul, Real.enorm_of_nonneg (show 0 ≤ p.1 from hp.1.le)]

theorem circularMean_neg_radius (g : Plane → V) (r : ℝ) (x : Plane) :
    circularMean g (-r) x = circularMean g r x := by
  rw [circularMean_eq_circleAverage, circularMean_eq_circleAverage, Real.circleAverage_neg_radius]

/-- The actual planar Green integral equals its radial circular-mean integral.
Fubini is applied only with the preceding singular-integrand integrability proof. -/
theorem planarGreen_integral_eq_radial {g : Plane → V} (hg : Continuous g)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ y : Plane, planarGreenKernel r y • g (x - y)) =
      ∫ t : ℝ in (0 : ℝ)..r, greenRadialWeight r t • circularMean g t x := by
  have hp := planarGreen_polar_integrable hg x hr
  calc
    _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (planarGreenKernel r (planePolar p) • g (x - planePolar p)) ∂(volume.prod volume) :=
      plane_integral_eq_polar _
    _ = ∫ t : ℝ in Ioi (0 : ℝ), ∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
        greenPolarWeight r t • g (x + (-t) • circleDirection θ) := by
      rw [setIntegral_prod _ hp]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      change t • (planarGreenKernel r (planePolar (t, θ)) • g (x - planePolar (t, θ))) = _
      rw [planePolar_eq, smul_smul, green_polar_jacobian ht]
      simp only [neg_smul, sub_eq_add_neg]
    _ = ∫ t : ℝ in Ioi (0 : ℝ), (greenPolarWeight r t * (2 * Real.pi)) • circularMean g t x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
        greenPolarWeight r t • g (x + (-t) • circleDirection θ)) =
        (greenPolarWeight r t * (2 * Real.pi)) • circularMean g t x
      rw [integral_smul, centeredAngleIntegral_eq_circularMean, circularMean_neg_radius, smul_smul]
    _ = ∫ t : ℝ in Ioi (0 : ℝ), (Ioo (0 : ℝ) r).indicator
        (fun t : ℝ => greenRadialWeight r t • circularMean g t x) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change (greenPolarWeight r t * (2 * Real.pi)) • circularMean g t x =
        (Ioo (0 : ℝ) r).indicator
          (fun u : ℝ => greenRadialWeight r u • circularMean g u x) t
      unfold greenPolarWeight
      by_cases ht : t ∈ Ioo (0 : ℝ) r
      · simp only [indicator_of_mem ht]
        congr 1
        field_simp [Real.two_pi_pos.ne']
      · simp [ht]
    _ = ∫ t : ℝ in Ioo (0 : ℝ) r, greenRadialWeight r t • circularMean g t x := by
      rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
        inter_eq_left.mpr Ioo_subset_Ioi_self]
    _ = _ := by rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]

end PolarGreen

theorem planarGreenKernel_integrable {r : ℝ} (hr : 0 < r) : Integrable (planarGreenKernel r) := by
  simpa only [smul_eq_mul, mul_one] using
    planarGreen_integrable_mul (g := fun _ : Plane => (1 : ℝ)) continuous_const (0 : Plane) hr

/-- The compact logarithmic Green kernel has exactly mass r²/4. -/
theorem planarGreenKernel_integral {r : ℝ} (hr : 0 < r) :
    (∫ y : Plane, planarGreenKernel r y) = r ^ 2 / 4 := by
  have h := planarGreen_integral_eq_radial (g := fun _ : Plane => (1 : ℝ))
    continuous_const (0 : Plane) hr
  simp only [smul_eq_mul, mul_one, circularMean_constant] at h
  have hm := integral_greenRadialMonomial hr 0
  norm_num [greenRadialMonomial] at hm
  exact h.trans hm

/-- The Green kernel applied to the actual Laplacian is the circle mean defect. -/
theorem localConvolution_planarGreen_laplacian {φ : Plane → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    localConvolution (planarGreenKernel r) (laplacian φ) x = circularMean φ r x - φ x := by
  rw [localConvolution, planarGreen_integral_eq_radial (laplacian_contDiff_infty hφ).continuous x hr]
  exact integral_circleGreen_laplacian hφ x hr

/-- Actual planar spectral evaluation on a complex exponential, proved through
the exact circular multiplier and the already verified factorial-series integral. -/
theorem localConvolution_planarGreen_spectral {r : ℝ} (hr : 0 < r) (ζ : ℂ) :
    localConvolution (planarGreenKernel r) (spectralExponential (Complex.I * ζ)) 0 =
      ((r : ℂ) ^ 2 / 4) * Q (-((r : ℂ) * ζ) ^ 2 / 4) := by
  rw [localConvolution, planarGreen_integral_eq_radial
    (spectralExponential_contDiff (Complex.I * ζ)).continuous 0 hr]
  have heq : (fun t : ℝ => greenRadialWeight r t •
      circularMean (spectralExponential (Complex.I * ζ)) t 0) =
      (fun t : ℝ => (t * Real.log (r / t)) • J0 ((t : ℂ) * ζ)) := by
    funext t
    rw [circularMean_spectralExponential, spectralExponential_zero, one_mul]
    have harg : Complex.I * (Complex.I * ζ) * (t : ℂ) = -((t : ℂ) * ζ) := by
      calc
        _ = (Complex.I * Complex.I) * ((t : ℂ) * ζ) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [harg, J0_neg]
    rfl
  rw [heq]
  exact integral_greenBessel_eq_Q hr ζ

end J0RadialUniqueness
