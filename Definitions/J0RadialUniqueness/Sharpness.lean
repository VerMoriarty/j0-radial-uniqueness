import Definitions.J0RadialUniqueness.TwoRadius

/-! Geometric sharpness obligations from Volchkov Theorem 1(iii)--(iv),
specialized to dimension two. These are specifications, not assumed theorems.
The subcritical radius retains the source's standing condition R > max(r1,r2).
Nonharmonicity is stated distributionally, including at finite regularity zero. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace J0RadialUniqueness

def BoundaryFiniteSmoothCounterexampleStatement : Prop :=
  ∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ → ∀ s : ℕ,
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ (s : WithTop ℕ∞) f (planeBall (r₁ + r₂)) ∧
      LocallyIntegrableOn f (planeBall (r₁ + r₂)) ∧
      MeanIdentityOn f r₁ (planeBall ((r₁ + r₂) - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall ((r₁ + r₂) - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall (r₁ + r₂))

def SubcriticalSmoothCounterexampleStatement : Prop :=
  ∀ r₁ r₂ R : ℝ, 0 < r₁ → 0 < r₂ → max r₁ r₂ < R → R < r₁ + r₂ →
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ ∞ f (planeBall R) ∧ LocallyIntegrableOn f (planeBall R) ∧
      MeanIdentityOn f r₁ (planeBall (R - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall (R - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall R)

end J0RadialUniqueness
