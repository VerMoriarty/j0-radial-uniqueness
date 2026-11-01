import Solutions.J0RadialUniqueness.CircularMeanRegularity

noncomputable section
open MeasureTheory Set

namespace J0RadialUniqueness

theorem circleEvaluation_mem_ball {r R : ℝ} {x : Plane}
    (hr : 0 ≤ r) (hx : x ∈ planeBall (R - r)) (t : ℝ) :
    x + r • circleDirection t ∈ planeBall R := by
  have hxn : ‖x‖ < R - r := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
  change dist (x + r • circleDirection t) 0 < R
  rw [dist_zero_right]
  calc
    ‖x + r • circleDirection t‖ ≤ ‖x‖ + ‖r • circleDirection t‖ := norm_add_le _ _
    _ = ‖x‖ + r := by simp only [norm_smul, Real.norm_eq_abs, norm_circleDirection,
      abs_of_nonneg hr, mul_one]
    _ < R := by linarith

theorem circularMean_congr_ae_on_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : Plane → V} {R r : ℝ}
    (hr : 0 ≤ r) (hfg : f =ᵐ[volume.restrict (planeBall R)] g) :
    circularMean f r =ᵐ[volume.restrict (planeBall (R - r))] circularMean g r := by
  have hball : MeasurableSet (planeBall R) := measurableSet_ball
  have hind : (planeBall R).indicator f =ᵐ[volume] (planeBall R).indicator g :=
    (ae_eq_restrict_iff_indicator_ae_eq hball).mp hfg
  have hmean := ae_restrict_of_ae (s := planeBall (R - r)) (circularMean_congr_ae hind r)
  filter_upwards [hmean, ae_restrict_mem (show MeasurableSet (planeBall (R - r)) from
    measurableSet_ball)] with x hm hx
  rw [circularMean_indicator_eq f r x _ (circleEvaluation_mem_ball hr hx),
    circularMean_indicator_eq g r x _ (circleEvaluation_mem_ball hr hx)] at hm
  exact hm

theorem paper_circle_mean_well_defined : CircularMeanWellDefinedStatement := by
  constructor
  · intro f g R r hr hfg
    exact circularMean_congr_ae_on_ball hr hfg
  · intro f R r hr hf
    exact ⟨ae_intervalIntegrable_circleEvaluation_of_locallyIntegrableOn_ball hf hr,
      locallyIntegrableOn_circularMean_ball hf hr⟩

end J0RadialUniqueness
