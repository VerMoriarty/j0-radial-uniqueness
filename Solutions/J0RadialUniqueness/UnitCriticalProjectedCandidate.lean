import Solutions.J0RadialUniqueness.RootCosineMeanIdentities
import Solutions.J0RadialUniqueness.BallCutoffExtension
import Solutions.J0RadialUniqueness.AngularProjectionOperators

/-! Actual finite-order smooth candidates at the critical unit-small-radius
geometry.  A genuine compact extension is constructed before angular
projection.  Its low-degree second mean defect is annihilated by the actual
projection operator.  No nonharmonicity assertion is included here. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace J0RadialUniqueness

/-- Pointwise agreement on the whole ball gives agreement of the actual
circle integrals at every center in the natural inner ball. -/
theorem circularMean_congr_on_inner_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : Plane → V} {R r : ℝ}
    (hr : 0 ≤ r) (hfg : EqOn f g (planeBall R))
    {x : Plane} (hx : x ∈ planeBall (R - r)) :
    circularMean f r x = circularMean g r x := by
  unfold circularMean
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact hfg (circleEvaluation_mem_ball hr hx θ)

theorem meanIdentityOn_of_pointwise {f : Plane → ℂ} {r S : ℝ}
    (hm : ∀ x ∈ planeBall S, circularMean f r x = f x) :
    MeanIdentityOn f r (planeBall S) := by
  change ∀ᵐ x ∂volume.restrict (planeBall S), circularMean f r x = f x
  filter_upwards [ae_restrict_mem
    (show MeasurableSet (planeBall S) from measurableSet_ball)] with x hx
  exact hm x hx

/-- A compact extension preserves the actual defects on the two critical
natural center domains.  All mean identities are supplied by the proved
root-series calculation, rather than by an extension hypothesis. -/
theorem unitCritical_extension_mean_defects (M : ℕ) (hM : 2 ≤ M)
    {τ : ℝ} (hτ : 1 < τ) (hMT : τ + 2 < 2 * M - 1)
    {F : Plane → ℂ}
    (hEq : EqOn F (scaledBesselCosinePlane M τ 1) (planeBall (1 + τ))) :
    EqOn (circularMean F 1) F (planeBall ((1 + τ) - 1)) ∧
      EqOn (fun x => circularMean F τ x - F x)
        (fun x : Plane => (besselCentralPolynomial M).eval (x 0 : ℂ))
        (planeBall ((1 + τ) - τ)) := by
  have hcore :
      (∀ x ∈ planeBall ((1 + τ) - 1),
        circularMean (scaledBesselCosinePlane M τ 1) 1 x =
          scaledBesselCosinePlane M τ 1 x) ∧
      (∀ x ∈ planeBall ((1 + τ) - τ),
        circularMean (scaledBesselCosinePlane M τ 1) τ x -
          scaledBesselCosinePlane M τ 1 x =
            (besselCentralPolynomial M).eval (x 0 : ℂ)) := by
    simpa only [one_mul, mul_one, div_one] using
      (scaledBesselCosinePlane_critical_mean_defects M hM hτ
        (by norm_num : 0 < (1 : ℝ)) (T := τ + 2) (by linarith) hMT)
  have hτ0 : 0 ≤ τ := by linarith
  constructor
  · intro x hx
    have hxR : x ∈ planeBall (1 + τ) :=
      Metric.ball_subset_ball (by linarith : (1 + τ) - 1 ≤ 1 + τ) hx
    calc
      circularMean F 1 x = circularMean (scaledBesselCosinePlane M τ 1) 1 x :=
        circularMean_congr_on_inner_ball (by norm_num) hEq hx
      _ = scaledBesselCosinePlane M τ 1 x := hcore.1 x hx
      _ = F x := (hEq hxR).symm
  · intro x hx
    have hxR : x ∈ planeBall (1 + τ) :=
      Metric.ball_subset_ball (by linarith : (1 + τ) - τ ≤ 1 + τ) hx
    calc
      circularMean F τ x - F x = circularMean (scaledBesselCosinePlane M τ 1) τ x -
          scaledBesselCosinePlane M τ 1 x := by
        rw [circularMean_congr_on_inner_ball hτ0 hEq hx, hEq hxR]
      _ = (besselCentralPolynomial M).eval (x 0 : ℂ) := hcore.2 x hx

theorem unitCritical_projected_mean_identities (M : ℕ) (hM : 2 ≤ M)
    {τ : ℝ} (hτ : 1 < τ) (hMT : τ + 2 < 2 * M - 1)
    {F : Plane → ℂ} (hF : Continuous F)
    (hEq : EqOn F (scaledBesselCosinePlane M τ 1) (planeBall (1 + τ)))
    (m : ℤ) (hm : (besselCentralPolynomial M).natDegree < m.natAbs) :
    (∀ x ∈ planeBall ((1 + τ) - 1),
      circularMean (angularProjection F m) 1 x = angularProjection F m x) ∧
    (∀ x ∈ planeBall ((1 + τ) - τ),
      circularMean (angularProjection F m) τ x = angularProjection F m x) := by
  obtain ⟨hfirst, hsecond⟩ := unitCritical_extension_mean_defects M hM hτ hMT hEq
  constructor
  · intro x hx
    calc
      circularMean (angularProjection F m) 1 x = angularProjection (circularMean F 1) m x :=
        (angularProjection_circularMean_comm hF m 1 x).symm
      _ = angularProjection F m x := angularProjection_congr_on_ball hfirst m hx
  · exact angularProjection_meanIdentity_of_polynomial_defect hF τ
      (besselCentralPolynomial M) m hm hsecond

/-- A concrete critical candidate with its finite smoothness, actual compact
extension, and both pointwise and a.e. natural-domain mean equations.  The
polynomial cutoff frequency remains explicit for the subsequent independent
nonharmonicity argument. -/
theorem exists_unitCriticalProjectedCandidate {τ : ℝ} (hτ : 1 < τ)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : ℕ, 2 ≤ M ∧ τ + 2 + n < 2 * M - 1 ∧
      ∃ F : Plane → ℂ,
        ContDiff ℝ (n : ℕ∞ω) F ∧ HasCompactSupport F ∧
        EqOn F (scaledBesselCosinePlane M τ 1) (planeBall (1 + τ)) ∧
        ∀ m : ℤ, (besselCentralPolynomial M).natDegree < m.natAbs →
          ContDiff ℝ (n : ℕ∞ω) (angularProjection F m) ∧
          (∀ x ∈ planeBall ((1 + τ) - 1),
            circularMean (angularProjection F m) 1 x = angularProjection F m x) ∧
          (∀ x ∈ planeBall ((1 + τ) - τ),
            circularMean (angularProjection F m) τ x = angularProjection F m x) ∧
          MeanIdentityOn (angularProjection F m) 1 (planeBall ((1 + τ) - 1)) ∧
          MeanIdentityOn (angularProjection F m) τ (planeBall ((1 + τ) - τ)) := by
  obtain ⟨M, hMlarge⟩ := exists_nat_gt (τ + 2 + (n : ℝ) + 2)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hMr : (2 : ℝ) ≤ M := by linarith
  have hM : 2 ≤ M := by exact_mod_cast hMr
  have hMreg : τ + 2 + n < 2 * M - 1 := by linarith
  have hMT : τ + 2 < 2 * M - 1 := by linarith
  have hreal : ContDiffOn ℝ (n : ℕ∞ω) (scaledBesselCosineSeries M τ)
      (Ioo (-(τ + 2)) (τ + 2)) :=
    scaledBesselCosineSeries_contDiffOn M n hτ (by linarith) hMreg
  have hplane : ContDiffOn ℝ (n : ℕ∞ω)
      (scaledBesselCosinePlane M τ 1) (planeBall (τ + 2)) := by
    have hfun : scaledBesselCosinePlane M τ 1 =
        fun x : Plane => scaledBesselCosineSeries M τ (x 0) := by
      funext x
      rw [scaledBesselCosinePlane_apply, div_one]
    rw [hfun]
    exact coordinate_lift_contDiffOn_ball n hreal
  obtain ⟨F, hFn, hFc, hEq⟩ := exists_contDiff_compact_ball_extension n
    (by linarith : 0 < 1 + τ) (by linarith : 1 + τ < τ + 2) hplane
  refine ⟨M, hM, hMreg, F, hFn, hFc, hEq, ?_⟩
  intro m hm
  obtain ⟨hmfirst, hmsecond⟩ :=
    unitCritical_projected_mean_identities M hM hτ hMT hFn.continuous hEq m hm
  refine ⟨angularProjection_contDiff (n := (n : ℕ∞)) hFn m,
    hmfirst, hmsecond, meanIdentityOn_of_pointwise hmfirst,
    meanIdentityOn_of_pointwise hmsecond⟩

end J0RadialUniqueness
