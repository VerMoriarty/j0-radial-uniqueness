import Solutions.J0RadialUniqueness.LocalWeakMollificationLimit
import Definitions.J0RadialUniqueness.Sharpness

/-! Smoothing a genuine local counterexample on a strictly smaller ball.
The nonharmonicity premise is explicitly on the target ball; nonharmonicity
somewhere in the larger ball would not suffice. The actual weak-pairing limit
ensures that at least one of the small normalized smoothings remains a
counterexample, while the support margins preserve both circular means. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem smooth_two_mean_counterexample_on_smaller_ball
    {f : Plane → ℂ} {T R r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : max r₁ r₂ < R) (hRT : R < T)
    (hf : LocallyIntegrableOn f (planeBall T))
    (hm₁ : MeanIdentityOn f r₁ (planeBall (T - r₁)))
    (hm₂ : MeanIdentityOn f r₂ (planeBall (T - r₂)))
    (hnot : ¬ DistributionHarmonicOn f (planeBall R)) :
    ∃ g : Plane → ℂ,
      ContDiff ℝ ∞ g ∧ LocallyIntegrableOn g (planeBall R) ∧
      MeanIdentityOn g r₁ (planeBall (R - r₁)) ∧
      MeanIdentityOn g r₂ (planeBall (R - r₂)) ∧
      ¬ DistributionHarmonicOn g (planeBall R) := by
  obtain ⟨Q, hRQ, hQT⟩ := exists_between hRT
  have hQ : 0 < Q := hr₁.trans ((le_max_left _ _).trans_lt (hR.trans hRQ))
  by_contra hnone
  apply hnot
  apply distributionHarmonicOn_of_eventually_mollified_ballCutoff hf hQ hQT hRQ.le
  have hevent : ∀ᶠ n : ℕ in atTop, (weylApproximationBump n).rOut < Q - R :=
    weylApproximationBump_rOut_tendsto.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < Q - R))
  filter_upwards [hevent] with n hn
  have hsupp : ∀ y : Plane, (weylApproximationBump n).normed volume y ≠ 0 →
      ‖y‖ ≤ (weylApproximationBump n).rOut := by
    intro y hy
    have hy' : y ∈ Function.support ((weylApproximationBump n).normed volume) := hy
    rw [(weylApproximationBump n).support_normed_eq] at hy'
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hy' :
      ‖y‖ < (weylApproximationBump n).rOut).le
  obtain ⟨hsm, hmean₁, hmean₂⟩ := local_two_mean_mollification hf hQ hQT
    (show R + (weylApproximationBump n).rOut < Q by linarith) hr₁.le hr₂.le
    (weylApproximationBump n).hasCompactSupport_normed
    (weylApproximationBump n).contDiff_normed hsupp hm₁ hm₂
  by_contra hnnot
  apply hnone
  exact ⟨_, hsm, hsm.continuous.locallyIntegrable.locallyIntegrableOn _,
    (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall hmean₁),
    (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall hmean₂), hnnot⟩

/-- A critical counterexample which is nonharmonic on the chosen interior
ball yields the exact subcritical C∞ witness. The localized nonharmonicity
obligation remains visible until the spectral construction discharges it. -/
theorem subcriticalSmoothCounterexample_of_critical_local_nonharmonicity
    {r₁ r₂ R : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hR : max r₁ r₂ < R) (hsub : R < r₁ + r₂)
    (hcritical : ∃ f : Plane → ℂ,
      LocallyIntegrableOn f (planeBall (r₁ + r₂)) ∧
      MeanIdentityOn f r₁ (planeBall ((r₁ + r₂) - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall ((r₁ + r₂) - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall R)) :
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ ∞ f (planeBall R) ∧ LocallyIntegrableOn f (planeBall R) ∧
      MeanIdentityOn f r₁ (planeBall (R - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall (R - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall R) := by
  obtain ⟨f, hf, hm₁, hm₂, hnot⟩ := hcritical
  obtain ⟨g, hg, hL, hM₁, hM₂, hn⟩ :=
    smooth_two_mean_counterexample_on_smaller_ball hr₁ hr₂ hR hsub hf hm₁ hm₂ hnot
  exact ⟨g, hg.contDiffOn, hL, hM₁, hM₂, hn⟩

end J0RadialUniqueness
