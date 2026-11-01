import Definitions.J0RadialUniqueness.TwoRadius
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith

/-!
The distributional local-to-global part of Corollary 6.5. The only substantive
input is the explicitly supplied local two-radius theorem. No Weyl regularity
or Fourier statement is assumed by this reduction.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace J0RadialUniqueness

theorem meanIdentityOn_of_global {f : Plane → ℂ} {r : ℝ}
    (h : MeanIdentityOn f r Set.univ) (U : Set Plane) : MeanIdentityOn f r U := by
  have hglobal : ∀ᵐ x : Plane, circularMean f r x = f x := by
    simpa only [MeanIdentityOn, Measure.restrict_univ] using h
  exact ae_restrict_of_ae hglobal

/-- Compactly supported tests fit in a ball satisfying the strict geometric condition. -/
theorem globalDistributionHarmonic_of_local
    (hloc : LocalTwoRadiusStatement)
    (r₁ r₂ : ℝ) (f : Plane → ℂ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hne : r₁ ≠ r₂)
    (hf : LocallyIntegrable f)
    (hm₁ : MeanIdentityOn f r₁ Set.univ)
    (hm₂ : MeanIdentityOn f r₂ Set.univ) :
    DistributionHarmonicOn f Set.univ := by
  intro φ hφ hcompact _
  obtain ⟨s, hs⟩ := hcompact.isCompact.isBounded.subset_ball (0 : Plane)
  let R : ℝ := max s (r₁ + r₂) + 1
  have hR : r₁ + r₂ < R := by
    have hmax := le_max_right s (r₁ + r₂)
    dsimp only [R]
    linarith
  have hsR : s ≤ R := by
    have hmax := le_max_left s (r₁ + r₂)
    dsimp only [R]
    linarith
  have hsupport : tsupport φ ⊆ planeBall R :=
    hs.trans (Metric.ball_subset_ball hsR)
  have hlocal : DistributionHarmonicOn f (planeBall R) :=
    hloc r₁ r₂ R f hr₁ hr₂ hne hR (hf.locallyIntegrableOn (planeBall R))
      (meanIdentityOn_of_global hm₁ (planeBall (R - r₁)))
      (meanIdentityOn_of_global hm₂ (planeBall (R - r₂)))
  exact hlocal φ hφ hcompact hsupport

end J0RadialUniqueness
