import Solutions.J0RadialUniqueness.SpectralSmoothingOperators
import Solutions.J0RadialUniqueness.RootCosineMeanIdentities
import Solutions.J0RadialUniqueness.SmoothedResidueSummability
import Solutions.J0RadialUniqueness.LocalMeanMollification

/-! Local smoothing of the actual residue series. The exchange of its sum
and the plane integral is justified by the compact kernel times the proved
root majorant. Only equality on the larger open ball is used. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace J0RadialUniqueness

theorem localConvolution_rootCosineSeries_hasSum
    {a : RightOnePoint → ℂ} {F : Plane → ℂ} {ψ : Plane → ℝ}
    {R η : ℝ} (hR : 0 ≤ R)
    (hw : Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖ ^ R))
    (hEq : EqOn F (rootCosinePlane a 1) (planeBall R))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η)
    {x : Plane} (hx : x ∈ planeBall (R - η)) :
    HasSum (fun ν : RightOnePoint => ∫ y : Plane,
      ψ y • (a ν * spectralCosine (ν : ℂ) (x - y)))
      (localConvolution ψ F x) := by
  let B : RightOnePoint → ℝ := fun ν =>
    (4 : ℝ) ^ R * (‖a ν‖ * ‖(ν : ℂ)‖ ^ R)
  have hB : Summable B := hw.mul_left _
  have hinside {y : Plane} (hy : ψ y ≠ 0) : x - y ∈ planeBall R := by
    have hn : ‖y‖ ≤ η := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hs (subset_tsupport ψ hy)
    exact norm_sub_lt_of_inner_ball hx hn
  have hcoord {y : Plane} (hy : ψ y ≠ 0) : |(x - y) 0| ≤ R := by
    have hh := coordinate_div_abs_lt_of_mem_ball (s := 1) (T := R)
      (by norm_num) (by simpa only [one_mul] using hinside hy)
    simpa only [div_one] using hh.le
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (F := fun ν : RightOnePoint => fun y : Plane =>
      ψ y • (a ν * spectralCosine (ν : ℂ) (x - y)))
    (f := fun y : Plane => ψ y • F (x - y))
    (fun ν y => ‖ψ y‖ * B ν)
  · intro ν
    exact (hψ.smul (continuous_const.mul
      ((spectralCosine_contDiff (ν : ℂ)).continuous.comp
        (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · intro ν
    exact Eventually.of_forall fun y => by
      by_cases hy : ψ y = 0
      · simp [hy]
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (rootCosineSeries_norm_majorant a hR (hcoord hy) ν) (norm_nonneg _)
  · exact Eventually.of_forall fun y => hB.mul_left ‖ψ y‖
  · have hψI : Integrable ψ (volume : Measure Plane) := hψ.integrable_of_hasCompactSupport hc
    have hI := hψI.norm.mul_const (∑' ν, B ν)
    simpa only [tsum_mul_left] using hI
  · exact Eventually.of_forall fun y => by
      by_cases hy : ψ y = 0
      · simpa only [hy, zero_smul] using (hasSum_zero : HasSum (fun _ : RightOnePoint => (0 : ℂ)) 0)
      · have he := hEq (hinside hy)
        have hsum := (rootCosineSeries_summable a hR hw (hcoord hy)).hasSum
        have hval : F (x - y) = rootCosineSeries a ((x - y) 0) := by
          simpa only [rootCosinePlane, div_one] using he
        rw [hval]
        simpa only [spectralCosine, rootCosineSeries] using hsum.const_smul (ψ y)

theorem localConvolution_eq_smoothed_rootCosinePlane
    {a : RightOnePoint → ℂ} {F : Plane → ℂ} {ψ : Plane → ℝ}
    {R η : ℝ} (hR : 0 ≤ R)
    (hw : Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖ ^ R))
    (hEq : EqOn F (rootCosinePlane a 1) (planeBall R))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η)
    {x : Plane} (hx : x ∈ planeBall (R - η)) :
    localConvolution ψ F x =
      rootCosinePlane (fun ν => a ν * spectralSmoothingMultiplier ψ (ν : ℂ)) 1 x := by
  have hsum := localConvolution_rootCosineSeries_hasSum hR hw hEq hψ hc hs hx
  have heach (ν : RightOnePoint) : (∫ y : Plane,
      ψ y • (a ν * spectralCosine (ν : ℂ) (x - y))) =
      (a ν * spectralSmoothingMultiplier ψ (ν : ℂ)) * spectralCosine (ν : ℂ) x := by
    calc
      _ = a ν * localConvolution ψ (spectralCosine (ν : ℂ)) x := by
        unfold localConvolution
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp only [Complex.real_smul]
          ring
      _ = _ := by rw [localConvolution_spectralCosine hψ hc hrad]; ring
  simp_rw [heach] at hsum
  simpa only [rootCosinePlane, rootCosineSeries, div_one, spectralCosine]
    using hsum.tsum_eq.symm

/-- The global extension is used only on the original ball. Actual radial
smoothing and angular projection give equality on the smaller open ball. -/
theorem mollified_angularProjection_eq_smoothed_residue_projection
    (M : ℕ) {τ : ℝ} (hτ : 1 < τ) (hMT : 1 + τ < 2 * M - 1)
    {F : Plane → ℂ} (hF : Continuous F)
    (hEq : EqOn F (scaledBesselCosinePlane M τ 1) (planeBall (1 + τ)))
    {ψ : Plane → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z)
    {η : ℝ} (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η)
    (m : ℤ) :
    EqOn (mollified (angularProjection F m) ψ)
      (angularProjection
        (rootCosinePlane (fun ν : RightOnePoint => smoothedBesselResidueCoefficient M τ ψ ν) 1) m)
      (planeBall ((1 + τ) - η)) := by
  have he : EqOn (localConvolution ψ F)
      (rootCosinePlane (fun ν : RightOnePoint => smoothedBesselResidueCoefficient M τ ψ ν) 1)
      (planeBall ((1 + τ) - η)) := by
    intro x hx
    exact localConvolution_eq_smoothed_rootCosinePlane (by linarith)
      ((scaledBesselResidueCoefficient_weight_summable M hτ hMT).subtype
        (fun ν : onePoints => 0 < (ν : ℂ).re)) hEq hψ hc hrad hs hx
  intro x hx
  rw [mollified_eq_localConvolution,
    ← angularProjection_localConvolution_comm hψ hc hF hrad]
  exact angularProjection_congr_on_ball he m hx

end J0RadialUniqueness
