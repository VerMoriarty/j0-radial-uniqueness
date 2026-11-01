import Solutions.J0RadialUniqueness.MollifiedWeakHarmonic
import Solutions.J0RadialUniqueness.LocalConvolution
import Solutions.J0RadialUniqueness.SmoothMeanReduction
import Mathlib.MeasureTheory.Integral.Prod

/-! Local smoothing of the actual circular mean identities. The cutoff is
globally integrable because its closed support lies strictly inside the original
ball. Circle averaging and smoothing are exchanged only after proving joint
integrability. The final inheritance statement uses the original mean equation
only on its natural center domain. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology

namespace J0RadialUniqueness

def ballCutoff (Q : ℝ) (f : Plane → ℂ) : Plane → ℂ :=
  (planeBall Q).indicator f

theorem ballCutoff_eq_on_ball (Q : ℝ) (f : Plane → ℂ) :
    EqOn (ballCutoff Q f) f (planeBall Q) := by
  intro x hx
  exact indicator_of_mem hx f

theorem ballCutoff_integrable {f : Plane → ℂ} {Q R : ℝ}
    (hf : LocallyIntegrableOn f (planeBall R)) (_hQ : 0 < Q) (hQR : Q < R) :
    Integrable (ballCutoff Q f) := by
  have hclosed : IntegrableOn f (Metric.closedBall (0 : Plane) Q) := by
    apply hf.integrableOn_compact_subset _ (isCompact_closedBall (0 : Plane) Q)
    intro x hx
    have hn : ‖x‖ ≤ Q := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change dist x 0 < R
    rw [dist_zero_right]
    exact hn.trans_lt hQR
  exact (integrable_indicator_iff (show MeasurableSet (planeBall Q) from
    measurableSet_ball)).mpr (hclosed.mono_set Metric.ball_subset_closedBall)

theorem mollified_eq_localConvolution (f : Plane → ℂ) (ψ : Plane → ℝ) (x : Plane) :
    mollified f ψ x = localConvolution ψ f x := by
  unfold mollified
  rw [convolution_eq_swap]
  rfl

/-- Pointwise smoothings depend only on the local a.e. representative, with the
precise support-radius loss. No global equality of extensions is required. -/
theorem mollified_congr_on_inner_ball {ψ : Plane → ℝ} {f g : Plane → ℂ}
    {R η : ℝ} (hs : ∀ y : Plane, ψ y ≠ 0 → ‖y‖ ≤ η)
    (hfg : f =ᵐ[volume.restrict (planeBall R)] g)
    {x : Plane} (hx : x ∈ planeBall (R - η)) :
    mollified f ψ x = mollified g ψ x := by
  rw [mollified_eq_localConvolution, mollified_eq_localConvolution]
  exact localConvolution_congr_on_inner_ball hs hfg hx

theorem mollified_ballCutoff_eq_on_inner_ball {ψ : Plane → ℝ} (f : Plane → ℂ)
    {Q η : ℝ} (hs : ∀ y : Plane, ψ y ≠ 0 → ‖y‖ ≤ η)
    {x : Plane} (hx : x ∈ planeBall (Q - η)) :
    mollified (ballCutoff Q f) ψ x = mollified f ψ x :=
  mollified_congr_on_inner_ball hs
    ((ballCutoff_eq_on_ball Q f).aeEq_restrict measurableSet_ball) hx

theorem compactKernel_uniform_bound {ψ : Plane → ℝ}
    (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Plane, ‖ψ y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn hψ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : ψ y = 0
  · simpa only [hy, norm_zero] using (le_max_right C 0)
  · exact (hC y (subset_closure hy)).trans (le_max_left _ _)

/-- The angle/translation integrand is genuinely jointly L1. Its majorant is a
bounded kernel times a measure-preserving translate of an ambient L1 function.
This result precedes the Fubini exchange below. -/
theorem circularMean_mollified_integrand_integrable {f : Plane → ℂ} {ψ : Plane → ℝ}
    (hf : Integrable f) (hc : HasCompactSupport ψ) (hψ : Continuous ψ)
    (r : ℝ) (x : Plane) :
    Integrable (fun p : ℝ × Plane =>
      ψ p.2 • f ((x + r • circleDirection p.1) - p.2))
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod volume) := by
  have href : Integrable (fun y : Plane => f (x - y)) :=
    ((volume : Measure Plane).measurePreserving_sub_left x).integrable_comp_of_integrable hf
  have hh := integrable_circleEvaluation_product href (-r)
  have hbase : Integrable (fun p : ℝ × Plane =>
      f ((x + r • circleDirection p.1) - p.2))
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod volume) := by
    apply hh.congr
    filter_upwards [] with p
    congr 1
    simp only [neg_smul]
    abel
  obtain ⟨C, _, hC⟩ := compactKernel_uniform_bound hc hψ
  exact hbase.bdd_smul C (hψ.comp continuous_snd).aestronglyMeasurable
    (Eventually.of_forall fun p => hC p.2)

/-- Actual circle averaging commutes with smoothing an ambient L1 function.
The joint L1 theorem, rather than a formal exchange of undefined integrals,
justifies the use of Fubini. -/
theorem circularMean_mollified_eq_localConvolution {f : Plane → ℂ} {ψ : Plane → ℝ}
    (hf : Integrable f) (hc : HasCompactSupport ψ) (hψ : Continuous ψ)
    (r : ℝ) (x : Plane) :
    circularMean (mollified f ψ) r x = localConvolution ψ (circularMean f r) x := by
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hF := circularMean_mollified_integrand_integrable hf hc hψ r x
  have hswap := integral_integral_swap
    (f := fun θ : ℝ => fun y : Plane =>
      ψ y • f ((x + r • circleDirection θ) - y)) hF
  have hangle (y : Plane) :
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        ψ y • f ((x + r • circleDirection θ) - y)) =
      ψ y • ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        f ((x - y) + r • circleDirection θ) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with θ
    congr 2
    abel
  unfold circularMean
  simp_rw [mollified_eq_localConvolution]
  unfold localConvolution
  rw [intervalIntegral.integral_of_le hle, hswap]
  simp_rw [hangle]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [intervalIntegral.integral_of_le hle, smul_comm]

theorem circularMean_mollified_comm {f : Plane → ℂ} {ψ : Plane → ℝ}
    (hf : Integrable f) (hc : HasCompactSupport ψ) (hψ : Continuous ψ)
    (r : ℝ) (x : Plane) :
    circularMean (mollified f ψ) r x = mollified (circularMean f r) ψ x := by
  rw [circularMean_mollified_eq_localConvolution hf hc hψ,
    mollified_eq_localConvolution]

/-- The cutoff retains the original mean equation only inside its smaller
natural center ball. In particular no mean equation is asserted outside B_Q. -/
theorem meanIdentityOn_ballCutoff {f : Plane → ℂ} {R Q r : ℝ}
    (hr : 0 ≤ r) (hQR : Q < R)
    (hmean : MeanIdentityOn f r (planeBall (R - r))) :
    MeanIdentityOn (ballCutoff Q f) r (planeBall (Q - r)) := by
  have hsub : planeBall (Q - r) ⊆ planeBall (R - r) := by
    apply Metric.ball_subset_ball
    linarith
  have hm := ae_restrict_of_ae_restrict_of_subset hsub hmean
  filter_upwards [hm, ae_restrict_mem (show MeasurableSet (planeBall (Q - r)) from
    measurableSet_ball)] with x hmx hx
  have hxQ : x ∈ planeBall Q := by
    apply (Metric.ball_subset_ball (show Q - r ≤ Q by linarith)) hx
  change circularMean ((planeBall Q).indicator f) r x = (planeBall Q).indicator f x
  rw [circularMean_indicator_eq f r x (planeBall Q) (circleEvaluation_mem_ball hr hx),
    indicator_of_mem hxQ]
  exact hmx

/-- A local a.e. mean equation becomes a pointwise equation after smoothing,
on precisely the ball allowed by the compact kernel support. -/
theorem circularMean_mollified_ballCutoff_eq {f : Plane → ℂ} {ψ : Plane → ℝ}
    {R Q R' η r : ℝ} (hf : LocallyIntegrableOn f (planeBall R))
    (hQ : 0 < Q) (hQR : Q < R) (hmargin : R' + η < Q)
    (hr : 0 ≤ r) (hc : HasCompactSupport ψ) (hψ : Continuous ψ)
    (hs : ∀ y : Plane, ψ y ≠ 0 → ‖y‖ ≤ η)
    (hmean : MeanIdentityOn f r (planeBall (R - r)))
    {x : Plane} (hx : x ∈ planeBall (R' - r)) :
    circularMean (mollified (ballCutoff Q f) ψ) r x = mollified (ballCutoff Q f) ψ x := by
  have hcut := ballCutoff_integrable hf hQ hQR
  have hm := meanIdentityOn_ballCutoff hr hQR hmean
  have hxinner : x ∈ planeBall ((Q - r) - η) := by
    apply (Metric.ball_subset_ball (show R' - r ≤ (Q - r) - η by linarith)) hx
  rw [circularMean_mollified_eq_localConvolution hcut hc hψ]
  rw [localConvolution_congr_on_inner_ball hs hm hxinner]
  exact (mollified_eq_localConvolution (ballCutoff Q f) ψ x).symm

/-- The global C∞ smoothing and its actual local mean identities are obtained
from the original locally integrable input and its two a.e. equations. -/
theorem local_two_mean_mollification {f : Plane → ℂ} {ψ : Plane → ℝ}
    {R Q R' η r₁ r₂ : ℝ} (hf : LocallyIntegrableOn f (planeBall R))
    (hQ : 0 < Q) (hQR : Q < R) (hmargin : R' + η < Q)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hc : HasCompactSupport ψ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ y : Plane, ψ y ≠ 0 → ‖y‖ ≤ η)
    (hm₁ : MeanIdentityOn f r₁ (planeBall (R - r₁)))
    (hm₂ : MeanIdentityOn f r₂ (planeBall (R - r₂))) :
    ContDiff ℝ ∞ (mollified (ballCutoff Q f) ψ) ∧
      (∀ x ∈ planeBall (R' - r₁),
        circularMean (mollified (ballCutoff Q f) ψ) r₁ x = mollified (ballCutoff Q f) ψ x) ∧
      (∀ x ∈ planeBall (R' - r₂),
        circularMean (mollified (ballCutoff Q f) ψ) r₂ x = mollified (ballCutoff Q f) ψ x) := by
  refine ⟨mollified_contDiff (ballCutoff_integrable hf hQ hQR).locallyIntegrable hc hψ,
    ?_, ?_⟩
  · intro x hx
    exact circularMean_mollified_ballCutoff_eq hf hQ hQR hmargin hr₁ hc hψ.continuous hs hm₁ hx
  · intro x hx
    exact circularMean_mollified_ballCutoff_eq hf hQ hQR hmargin hr₂ hc hψ.continuous hs hm₂ hx

end J0RadialUniqueness
