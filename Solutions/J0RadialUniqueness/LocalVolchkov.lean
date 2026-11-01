import Solutions.J0RadialUniqueness.SmoothLocalTwoRadius
import Solutions.J0RadialUniqueness.LocalWeakMollificationLimit
import Solutions.J0RadialUniqueness.GlobalTwoRadius

/-! The finite-ball locally integrable two-radius theorem. Every smoothing is
taken from a strictly interior cutoff, and only eventually small supports are
used. Compact test supports then exhaust the original open ball. -/

noncomputable section
open MeasureTheory Set Filter Laplacian
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem localTwoRadius_noCommon_on_innerBall {f : Plane → ℂ} {R S r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hS : r₁ + r₂ < S) (hSR : S < R)
    (hf : LocallyIntegrableOn f (planeBall R))
    (hm₁ : MeanIdentityOn f r₁ (planeBall (R - r₁)))
    (hm₂ : MeanIdentityOn f r₂ (planeBall (R - r₂)))
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0) :
    DistributionHarmonicOn f (planeBall S) := by
  obtain ⟨Q, hSQ, hQR⟩ := exists_between hSR
  have hQ : 0 < Q := by linarith
  apply distributionHarmonicOn_of_eventually_mollified_ballCutoff hf hQ hQR hSQ.le
  have hevent : ∀ᶠ n : ℕ in atTop, (weylApproximationBump n).rOut < Q - S :=
    weylApproximationBump_rOut_tendsto.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < Q - S))
  filter_upwards [hevent] with n hn
  have hsupp : ∀ y : Plane, (weylApproximationBump n).normed volume y ≠ 0 →
      ‖y‖ ≤ (weylApproximationBump n).rOut := by
    intro y hy
    have hy' : y ∈ Function.support ((weylApproximationBump n).normed volume) := hy
    rw [(weylApproximationBump n).support_normed_eq] at hy'
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hy' :
      ‖y‖ < (weylApproximationBump n).rOut).le
  obtain ⟨hsm, hm₁', hm₂'⟩ := local_two_mean_mollification hf hQ hQR
    (show S + (weylApproximationBump n).rOut < Q by linarith) hr₁.le hr₂.le
    (weylApproximationBump n).hasCompactSupport_normed
    (weylApproximationBump n).contDiff_normed hsupp hm₁ hm₂
  exact smoothLocalTwoRadius_noCommon hsm hr₁ hr₂ hS hNoCommon
    ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall hm₁'))
    ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall hm₂'))

/-- The local weak equation is recovered on B_R using compact supports of the
actual C∞ tests. No assertion about a test touching the boundary is needed. -/
theorem localTwoRadius_noCommon {f : Plane → ℂ} {R r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hf : LocallyIntegrableOn f (planeBall R))
    (hm₁ : MeanIdentityOn f r₁ (planeBall (R - r₁)))
    (hm₂ : MeanIdentityOn f r₂ (planeBall (R - r₂)))
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0) :
    DistributionHarmonicOn f (planeBall R) := by
  intro φ hφ hcφ hsφ
  let K : Set Plane := tsupport φ ∪ {(0 : Plane)}
  have hK : IsCompact K := hcφ.isCompact.union isCompact_singleton
  have hKne : K.Nonempty := ⟨0, Or.inr (mem_singleton _)⟩
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn hKne (continuous_norm.continuousOn)
  have hnorm : ‖x‖ < R := by
    rcases hxK with hx | hx
    · simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hsφ hx
    · have hx0 : x = 0 := mem_singleton_iff.mp hx
      rw [hx0, norm_zero]
      linarith
  obtain ⟨S, hmaxS, hSR⟩ := exists_between (max_lt hnorm hR)
  have hS : r₁ + r₂ < S := (le_max_right ‖x‖ (r₁ + r₂)).trans_lt hmaxS
  have hsS : tsupport φ ⊆ planeBall S := by
    intro y hy
    change dist y 0 < S
    rw [dist_zero_right]
    exact (hxmax (Or.inl hy)).trans_lt ((le_max_left ‖x‖ (r₁ + r₂)).trans_lt hmaxS)
  exact localTwoRadius_noCommon_on_innerBall hr₁ hr₂ hS hSR hf hm₁ hm₂ hNoCommon
    φ hφ hcφ hsS

theorem paper_6_3 : VolchkovLocalStatement := by
  intro r₁ r₂ R f hr₁ hr₂ hR hf hm₁ hm₂ hratio
  exact localTwoRadius_noCommon hr₁ hr₂ hR hf hm₁ hm₂
    (helmholtzResolventMasses_no_common_zero_of_ratio_exclusion hr₁ hr₂ hratio)

theorem paper_6_4 : LocalTwoRadiusStatement :=
  localTwoRadius_of_rayUniqueness_and_volchkov paper_5_3 paper_6_3

theorem paper_6_5 : GlobalTwoRadiusStatement := globalTwoRadius_of_local paper_6_4

end J0RadialUniqueness
