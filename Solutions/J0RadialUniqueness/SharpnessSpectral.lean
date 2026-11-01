import Definitions.J0RadialUniqueness.Sharpness
import Solutions.J0RadialUniqueness.ExplicitCounterexample
import Solutions.J0RadialUniqueness.ClassicalWeakHarmonic

/-! The common-spectrum branch of the geometric sharpness problem.

The witness is the actual global complex exponential. This module does not
assert existence of a common nonzero spectral frequency for arbitrary radii,
and therefore does not assert either full geometric sharpness specification.
Its conclusions are exactly the corresponding branches with that frequency
given as a mathematical premise. -/

noncomputable section

open MeasureTheory Laplacian
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem spectralExponential_meanIdentityOn (lam : ℂ) (r : ℝ)
    (hJ : J0 (Complex.I * lam * (r : ℂ)) = 1) (U : Set Plane) :
    MeanIdentityOn (spectralExponential lam) r U := by
  exact Filter.Eventually.of_forall (fun x => by
    rw [circularMean_spectralExponential, hJ, mul_one])

theorem spectralExponential_locallyIntegrableOn (lam : ℂ) (U : Set Plane) :
    LocallyIntegrableOn (spectralExponential lam) U :=
  (spectralExponential_contDiff lam).continuous.locallyIntegrable.locallyIntegrableOn U

/-- The nonzero Laplacian at the origin rules out the actual distributional
harmonicity on every ball of positive radius. -/
theorem spectralExponential_not_distributionHarmonicOn_ball {lam : ℂ} (hlam : lam ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    ¬ DistributionHarmonicOn (spectralExponential lam) (planeBall R) := by
  have hf : ContDiffOn ℝ 2 (spectralExponential lam) (planeBall R) :=
    ((contDiff_infty.mp (spectralExponential_contDiff lam)) 2).contDiffOn
  apply not_distributionHarmonicOn_of_laplacian_ne_zero
    (show IsOpen (planeBall R) from Metric.isOpen_ball) hf (x := (0 : Plane))
  · simpa only [planeBall, Metric.mem_ball, dist_self] using hR
  · rw [laplacian_spectralExponential, spectralExponential_zero, mul_one]
    exact pow_ne_zero 2 hlam

/-- The explicitly identified global smooth witness works on every positive
ball and on both full natural center domains. -/
theorem exists_common_spectral_counterexample_on_ball {r₁ r₂ : ℝ}
    (_hr₁ : 0 < r₁) (_hr₂ : 0 < r₂) {lam : ℂ} (hlam : lam ≠ 0)
    (hJ₁ : J0 (Complex.I * lam * (r₁ : ℂ)) = 1)
    (hJ₂ : J0 (Complex.I * lam * (r₂ : ℂ)) = 1) {R : ℝ} (hR : 0 < R) :
    ∃ f : Plane → ℂ,
      f = spectralExponential lam ∧ ContDiff ℝ ∞ f ∧
      LocallyIntegrableOn f (planeBall R) ∧
      MeanIdentityOn f r₁ (planeBall (R - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall (R - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall R) := by
  refine ⟨spectralExponential lam, rfl, spectralExponential_contDiff lam,
    spectralExponential_locallyIntegrableOn lam _, spectralExponential_meanIdentityOn lam r₁ hJ₁ _,
    spectralExponential_meanIdentityOn lam r₂ hJ₂ _, ?_⟩
  exact spectralExponential_not_distributionHarmonicOn_ball hlam hR

/-- The finite-regularity boundary-radius specification for this actual
common-spectrum pair of radii. Its frequency premise is explicit. -/
theorem boundaryFiniteSmoothCounterexample_of_common_spectral_root {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) {lam : ℂ} (hlam : lam ≠ 0)
    (hJ₁ : J0 (Complex.I * lam * (r₁ : ℂ)) = 1)
    (hJ₂ : J0 (Complex.I * lam * (r₂ : ℂ)) = 1) (s : ℕ) :
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ (s : WithTop ℕ∞) f (planeBall (r₁ + r₂)) ∧
      LocallyIntegrableOn f (planeBall (r₁ + r₂)) ∧
      MeanIdentityOn f r₁ (planeBall ((r₁ + r₂) - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall ((r₁ + r₂) - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall (r₁ + r₂)) := by
  obtain ⟨f, rfl, hf, hL, hM₁, hM₂, hnot⟩ :=
    exists_common_spectral_counterexample_on_ball hr₁ hr₂ hlam hJ₁ hJ₂ (add_pos hr₁ hr₂)
  exact ⟨spectralExponential lam, ((contDiff_infty.mp hf) s).contDiffOn, hL, hM₁, hM₂, hnot⟩

/-- The subcritical smooth specification for a pair possessing the stated
common nonzero spectral frequency. The source's radius hypotheses are retained. -/
theorem subcriticalSmoothCounterexample_of_common_spectral_root {r₁ r₂ R : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : max r₁ r₂ < R) (_hsub : R < r₁ + r₂)
    {lam : ℂ} (hlam : lam ≠ 0)
    (hJ₁ : J0 (Complex.I * lam * (r₁ : ℂ)) = 1)
    (hJ₂ : J0 (Complex.I * lam * (r₂ : ℂ)) = 1) :
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ ∞ f (planeBall R) ∧ LocallyIntegrableOn f (planeBall R) ∧
      MeanIdentityOn f r₁ (planeBall (R - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall (R - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall R) := by
  have hRpos : 0 < R := hr₁.trans ((le_max_left r₁ r₂).trans_lt hR)
  obtain ⟨f, _hident, hf, hL, hM₁, hM₂, hnot⟩ :=
    exists_common_spectral_counterexample_on_ball hr₁ hr₂ hlam hJ₁ hJ₂ hRpos
  exact ⟨f, hf.contDiffOn, hL, hM₁, hM₂, hnot⟩

end J0RadialUniqueness
