import Solutions.J0RadialUniqueness.MollifiedWeakHarmonic
import Solutions.J0RadialUniqueness.LocalConvolution

/-! Local weak harmonicity survives actual smoothing on the exact smaller
ball. The reflected kernel test is supported inside the original open ball;
no zero extension of the weak equation is used. -/

noncomputable section
open MeasureTheory Set Laplacian
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem reflectedKernel_tsupport_subset_ball {ψ : Plane → ℝ} {R η : ℝ}
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η) {x : Plane}
    (hx : x ∈ planeBall (R - η)) :
    tsupport (fun y : Plane => ψ (x - y)) ⊆ planeBall R := by
  intro y hy
  have hxy : x - y ∈ tsupport ψ :=
    tsupport_comp_subset_preimage ψ (by fun_prop : Continuous (fun y : Plane => x - y)) hy
  have hn : ‖x - y‖ ≤ η := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hs hxy
  have hh := norm_sub_lt_of_inner_ball hx hn
  convert! hh using 1 <;> abel

theorem mollified_laplacian_eq_zero_on_inner_ball {f : Plane → ℂ} {ψ : Plane → ℝ}
    {R η : ℝ} (hf : LocallyIntegrable f)
    (hweak : DistributionHarmonicOn f (planeBall R))
    (hc : HasCompactSupport ψ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η) {x : Plane}
    (hx : x ∈ planeBall (R - η)) :
    laplacian (mollified f ψ) x = 0 := by
  obtain ⟨ht, hct⟩ := reflectedKernel_test hc hψ x
  have hw := hweak (fun y => ψ (x - y)) ht hct (reflectedKernel_tsupport_subset_ball hs hx)
  rw [laplacian_mollified hf hc hψ, mollified_eq_integral]
  simpa only [laplacian_reflect hψ, Complex.real_smul] using hw

theorem mollified_harmonicOnNhd_inner_ball {f : Plane → ℂ} {ψ : Plane → ℝ}
    {R η : ℝ} (hf : LocallyIntegrable f)
    (hweak : DistributionHarmonicOn f (planeBall R))
    (hc : HasCompactSupport ψ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η) :
    InnerProductSpace.HarmonicOnNhd (mollified f ψ) (planeBall (R - η)) := by
  intro x hx
  refine ⟨((contDiff_infty.mp (mollified_contDiff hf hc hψ)) 2).contDiffAt, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact mollified_laplacian_eq_zero_on_inner_ball hf hweak hc hψ hs hy

end J0RadialUniqueness
