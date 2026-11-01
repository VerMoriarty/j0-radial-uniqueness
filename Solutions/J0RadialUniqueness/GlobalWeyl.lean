import Solutions.J0RadialUniqueness.HarmonicRadialConvolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-! A global Weyl lemma on the actual plane.  One explicit radial kernel gives
the smooth representative. General Mathlib bump functions, which need not be
radial, are used only for the final almost-everywhere approximate-identity limit.
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped ContDiff Convolution Topology

namespace J0RadialUniqueness

/-- An explicit radial smooth kernel, rather than the arbitrary bump base chosen
by the `HasContDiffBump` typeclass. -/
def weylRawKernel : Plane → ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace Plane).toFun 2

theorem weylRawKernel_contDiff : ContDiff ℝ ∞ weylRawKernel := by
  rw [← contDiffOn_univ]
  have hpair : ContDiffOn ℝ ∞ (fun y : Plane => ((2 : ℝ), y)) Set.univ :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmaps : Set.MapsTo (fun y : Plane => ((2 : ℝ), y)) Set.univ
      (Ioi (1 : ℝ) ×ˢ (Set.univ : Set Plane)) := by
    intro y hy
    exact ⟨by norm_num, Set.mem_univ _⟩
  exact (ContDiffBumpBase.ofInnerProductSpace Plane).smooth.comp hpair hmaps

theorem weylRawKernel_support : Function.support weylRawKernel = Metric.ball (0 : Plane) 2 :=
  (ContDiffBumpBase.ofInnerProductSpace Plane).support 2 (by norm_num)

theorem weylRawKernel_hasCompactSupport : HasCompactSupport weylRawKernel := by
  change IsCompact (closure (Function.support weylRawKernel))
  rw [weylRawKernel_support, closure_ball (0 : Plane) (by norm_num : (2 : ℝ) ≠ 0)]
  exact isCompact_closedBall (0 : Plane) (2 : ℝ)

theorem weylRawKernel_nonneg (y : Plane) : 0 ≤ weylRawKernel y :=
  ((ContDiffBumpBase.ofInnerProductSpace Plane).mem_Icc 2 y).1

theorem weylRawKernel_integrable : Integrable weylRawKernel :=
  weylRawKernel_contDiff.continuous.integrable_of_hasCompactSupport
    weylRawKernel_hasCompactSupport

theorem weylRawKernel_integral_pos : 0 < ∫ y : Plane, weylRawKernel y := by
  apply (integral_pos_iff_support_of_nonneg weylRawKernel_nonneg
    weylRawKernel_integrable).mpr
  rw [weylRawKernel_support]
  exact Metric.measure_ball_pos volume (0 : Plane) (by norm_num)

/-- A single concrete compactly supported smooth radial kernel of integral one. -/
def weylRadialKernel (y : Plane) : ℝ :=
  weylRawKernel y / ∫ z : Plane, weylRawKernel z

theorem weylRadialKernel_contDiff : ContDiff ℝ ∞ weylRadialKernel :=
  weylRawKernel_contDiff.div_const _

theorem weylRadialKernel_hasCompactSupport : HasCompactSupport weylRadialKernel := by
  apply weylRawKernel_hasCompactSupport.mono
  intro y hy
  change weylRawKernel y ≠ 0
  intro hzero
  exact hy (by simp only [weylRadialKernel, hzero, zero_div])

theorem weylRadialKernel_radial (y z : Plane) (h : ‖y‖ = ‖z‖) :
    weylRadialKernel y = weylRadialKernel z := by
  change smoothTransition (((2 : ℝ) - ‖y‖) / (2 - 1)) /
      (∫ u : Plane, weylRawKernel u) =
    smoothTransition (((2 : ℝ) - ‖z‖) / (2 - 1)) /
      (∫ u : Plane, weylRawKernel u)
  rw [h]

theorem weylRadialKernel_integral_one : (∫ y : Plane, weylRadialKernel y) = 1 := by
  simp_rw [weylRadialKernel, div_eq_mul_inv, mul_comm (weylRawKernel _),
    ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ weylRawKernel_integral_pos.ne'

/-- A family of arbitrary Mathlib bump functions with uniformly comparable
inner and outer radii. Radiality of these functions is neither asserted nor needed. -/
def weylApproximationBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := ((n : ℝ) + 1)⁻¹
  rOut := 2 * ((n : ℝ) + 1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith

theorem weylApproximationBump_rOut_tendsto :
    Tendsto (fun n : ℕ => (weylApproximationBump n).rOut) atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [weylApproximationBump, mul_zero] using hi.const_mul 2

theorem mollified_eq_kernelConvolution (f : Plane → ℂ) (ψ : Plane → ℝ) (x : Plane) :
    mollified f ψ x = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  rw [mollified_eq_integral_swap, convolution_def]
  rfl

/-- The explicit smoothing by `weylRadialKernel` is the smooth harmonic
representative of every globally locally integrable weakly harmonic function. -/
theorem global_weyl_explicit {f : Plane → ℂ} (hf : LocallyIntegrable f)
    (hweak : DistributionHarmonicOn f Set.univ) :
    ContDiff ℝ ∞ (mollified f weylRadialKernel) ∧
      InnerProductSpace.HarmonicOnNhd (mollified f weylRadialKernel) Set.univ ∧
      ∀ᵐ x : Plane, f x = mollified f weylRadialKernel x := by
  let g : Plane → ℂ := mollified f weylRadialKernel
  have hgs := mollified_smooth_harmonic hf hweak
    weylRadialKernel_hasCompactSupport weylRadialKernel_contDiff
  refine ⟨hgs.1, hgs.2, ?_⟩
  have hfconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure Plane)) (φ := weylApproximationBump) (K := (2 : ℝ))
    weylApproximationBump_rOut_tendsto
    (Filter.Eventually.of_forall fun n => le_rfl) hf
  filter_upwards [hfconv] with x hfx
  have hgconv := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Plane)) (φ := weylApproximationBump)
    weylApproximationBump_rOut_tendsto hgs.1.continuous x
  have hseq : ∀ n : ℕ,
      (((weylApproximationBump n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x =
      (((weylApproximationBump n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
    intro n
    rw [← mollified_eq_kernelConvolution, ← mollified_eq_kernelConvolution]
    exact mollified_eq_mollified_radial_smoothing hf hweak
      weylRadialKernel_hasCompactSupport weylRadialKernel_contDiff
      weylRadialKernel_radial weylRadialKernel_integral_one
      (weylApproximationBump n).hasCompactSupport_normed
      (weylApproximationBump n).contDiff_normed x
  exact tendsto_nhds_unique hfx ((tendsto_congr hseq).mpr hgconv)

/-- Global Weyl regularity, with no regularity theorem included among the hypotheses. -/
theorem global_weyl {f : Plane → ℂ} (hf : LocallyIntegrable f)
    (hweak : DistributionHarmonicOn f Set.univ) :
    ∃ g : Plane → ℂ, ContDiff ℝ ∞ g ∧
      InnerProductSpace.HarmonicOnNhd g Set.univ ∧ ∀ᵐ x : Plane, f x = g x :=
  ⟨mollified f weylRadialKernel, global_weyl_explicit hf hweak⟩

/-- For a continuous weakly harmonic function the representative equality is
pointwise, so every positive-radius circular mean is the original function. -/
theorem continuous_harmonic_of_distribution {f : Plane → ℂ} (hf : Continuous f)
    (hweak : DistributionHarmonicOn f Set.univ) :
    InnerProductSpace.HarmonicOnNhd f Set.univ ∧
      ∀ r : ℝ, 0 < r → ∀ x : Plane, circularMean f r x = f x := by
  have hs := global_weyl_explicit hf.locallyIntegrable hweak
  have heq : f = mollified f weylRadialKernel :=
    Measure.eq_of_ae_eq (μ := (volume : Measure Plane)) hs.2.2 hf hs.1.continuous
  have hh : InnerProductSpace.HarmonicOnNhd f Set.univ := by
    rw [heq]
    exact hs.2.1
  exact ⟨hh, fun r _ x => circularMean_eq_of_harmonicOnNhd f hh r x⟩

end J0RadialUniqueness
