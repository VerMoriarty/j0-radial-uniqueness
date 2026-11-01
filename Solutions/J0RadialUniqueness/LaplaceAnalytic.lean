import Solutions.J0RadialUniqueness.LaplaceGeometry
import Solutions.J0RadialUniqueness.LaplaceKernel
import Solutions.J0RadialUniqueness.LaplaceMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace J0RadialUniqueness

theorem muDensity_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ muDensity t := by
  unfold muDensity
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht _))
    (Real.sqrt_nonneg _)

theorem muDensity_continuousOn : ContinuousOn muDensity (Ioi (0 : ℝ)) := by
  have hp : ContinuousOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioi 0) :=
    continuous_id.continuousOn.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  change ContinuousOn (fun t : ℝ =>
    Real.exp (-t) * Real.rpow t (-1 / 2 : ℝ) / Real.sqrt Real.pi) (Ioi 0)
  simpa only [Real.rpow_eq_pow, Function.comp_def, Pi.mul_apply] using
    ((Real.continuous_exp.comp continuous_neg).continuousOn.mul hp).div_const (Real.sqrt Real.pi)

theorem laplace_weighted_kernel_measurable {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    AEStronglyMeasurable (fun t => (muDensity t : ℂ) * laplaceKernel w t)
      (volume.restrict (Ioi (0 : ℝ))) :=
  ((Complex.continuous_ofReal.comp_continuousOn muDensity_continuousOn).mul
    (laplaceKernel_continuousOn_t hw)).aestronglyMeasurable measurableSet_Ioi

theorem laplace_weighted_moment_measurable {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    AEStronglyMeasurable (fun t => (muDensity t : ℂ) * laplaceMomentKernel w t)
      (volume.restrict (Ioi (0 : ℝ))) :=
  ((Complex.continuous_ofReal.comp_continuousOn muDensity_continuousOn).mul
    (laplaceMomentKernel_continuousOn_t hw)).aestronglyMeasurable measurableSet_Ioi

theorem laplace_weighted_kernel_integrable {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    IntegrableOn (fun t => (muDensity t : ℂ) * laplaceKernel w t) (Ioi (0 : ℝ)) := by
  obtain ⟨r, m, c, hr, hm, hc, hsub, hmb, hcb⟩ := laplace_local_uniform_lower hw
  apply (muDensity_integrableOn.mul_const (Real.rpow c (-1 / 2 : ℝ))).mono'
    (laplace_weighted_kernel_measurable hw)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (muDensity_nonneg t ht.le)]
  exact mul_le_mul_of_nonneg_left
    (laplaceKernel_norm_le_of_base_lower_bound hc
      (hcb w (Metric.mem_closedBall_self hr.le) t ht.le)) (muDensity_nonneg t ht.le)

theorem laplace_weighted_moment_integrable {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    IntegrableOn (fun t => (muDensity t : ℂ) * laplaceMomentKernel w t) (Ioi (0 : ℝ)) := by
  obtain ⟨r, m, c, hr, hm, hc, hsub, hmb, hcb⟩ := laplace_local_uniform_lower hw
  apply (firstMoment_integrableOn.mul_const (Real.rpow c (-3 / 2 : ℝ))).mono'
    (laplace_weighted_moment_measurable hw)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (muDensity_nonneg t ht.le)]
  calc
    _ ≤ muDensity t * (t * Real.rpow c (-3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (laplaceMomentKernel_norm_le_of_base_lower_bound ht.le hc
          (hcb w (Metric.mem_closedBall_self hr.le) t ht.le)) (muDensity_nonneg t ht.le)
    _ = _ := by ring

theorem laplace_integrability : LaplaceIntegrabilityStatement :=
  fun _ hw => ⟨laplace_weighted_kernel_integrable hw, laplace_weighted_moment_integrable hw⟩

/-- Complex differentiation under the actual improper integral on the full slit plane. -/
theorem laplaceI_hasDerivAt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt laplaceI ((1 / (4 * w ^ 2)) * weightedIntegral (laplaceMomentKernel w)) w := by
  obtain ⟨r, m, c, hr, hm, hc, hsub, hmb, hcb⟩ := laplace_local_uniform_lower hw
  let P : ℂ → ℝ → ℂ := fun z t => (muDensity t : ℂ) * laplaceKernel z t
  let D : ℂ → ℝ → ℂ := fun z t =>
    (muDensity t : ℂ) * ((1 / (4 * z ^ 2)) * laplaceMomentKernel z t)
  let B : ℝ → ℝ := fun t =>
    (1 / (4 * m ^ 2)) * Real.rpow c (-3 / 2 : ℝ) * (t * muDensity t)
  have hmeas : ∀ᶠ z in 𝓝 w, AEStronglyMeasurable (P z)
      (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [Metric.closedBall_mem_nhds w hr] with z hz
    exact laplace_weighted_kernel_measurable (hsub hz)
  have hdmeas : AEStronglyMeasurable (D w) (volume.restrict (Ioi (0 : ℝ))) := by
    have hh := (laplace_weighted_moment_measurable hw).const_mul (1 / (4 * w ^ 2))
    convert hh using 1
    funext t
    dsimp [D]
    ring
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ z ∈ Metric.closedBall w r, ‖D z t‖ ≤ B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hμ := muDensity_nonneg t ht.le
    have hmz := hmb z hz
    have hzpos : 0 < ‖z‖ := hm.trans_le hmz
    have hinv : 1 / (4 * ‖z‖ ^ 2) ≤ 1 / (4 * m ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hmoment := laplaceMomentKernel_norm_le_of_base_lower_bound ht.le hc (hcb z hz t ht.le)
    dsimp only [D, B]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ]
    have hnorm : ‖1 / (4 * z ^ 2)‖ = 1 / (4 * ‖z‖ ^ 2) := by simp
    rw [hnorm]
    calc
      _ ≤ muDensity t * ((1 / (4 * m ^ 2)) *
          (t * Real.rpow c (-3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  have hBint : Integrable B (volume.restrict (Ioi (0 : ℝ))) :=
    firstMoment_integrableOn.const_mul _
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ z ∈ Metric.closedBall w r, HasDerivAt (P · t) (D z t) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    exact (laplaceKernel_hasDerivAt_moment (hsub hz) ht.le).const_mul (muDensity t : ℂ)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (Metric.closedBall_mem_nhds w hr)
    hmeas (laplace_weighted_kernel_integrable hw) hdmeas hbound hBint hdiff
  have hvalue : (∫ t, D w t ∂volume.restrict (Ioi (0 : ℝ))) =
      (1 / (4 * w ^ 2)) * weightedIntegral (laplaceMomentKernel w) := by
    rw [weightedIntegral, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by dsimp [D]; ring)
  rw [hvalue] at hd
  exact hd.2

theorem laplaceI_differentiableOn : DifferentiableOn ℂ laplaceI Complex.slitPlane :=
  fun _ hw => (laplaceI_hasDerivAt hw).differentiableAt.differentiableWithinAt

theorem positive_div_mem_slitPlane {w : ℂ} (hw : w ∈ Complex.slitPlane)
    {a : ℝ} (ha : 0 < a) : (a : ℂ) / w ∈ Complex.slitPlane := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero hw)
  rcases hw with hr | hi
  · left
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos ha hr) hn
  · right
    simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero ha.ne' hi) hn.ne')

theorem laplaceK_differentiableAt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    DifferentiableAt ℂ laplaceK w := by
  have hwn : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have hd : (2 : ℂ) * w ≠ 0 := mul_ne_zero (by norm_num) hwn
  have hbase : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) / (2 * z)) w :=
    ((hasDerivAt_const w (Real.pi : ℂ)).div ((hasDerivAt_id w).const_mul 2) hd).differentiableAt
  have hslit : (Real.pi : ℂ) / (2 * w) ∈ Complex.slitPlane := by
    convert positive_div_mem_slitPlane hw (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2)) using 1
    push_cast
    ring
  have hp := hbase.cpow_const (c := (1 / 2 : ℂ)) hslit
  have he : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-z)) w := by fun_prop
  have hh := (hp.mul he).mul (laplaceI_hasDerivAt hw).differentiableAt
  exact hh

theorem laplaceK_differentiableOn : DifferentiableOn ℂ laplaceK Complex.slitPlane :=
  fun _ hw => (laplaceK_differentiableAt hw).differentiableWithinAt

/-- The complete analytic and derivative portion of Proposition 3.1. -/
theorem k_laplace_analytic : KLaplaceStatement :=
  ⟨laplaceI_differentiableOn, laplaceK_differentiableOn, fun _ hw => laplaceI_hasDerivAt hw⟩

end J0RadialUniqueness
