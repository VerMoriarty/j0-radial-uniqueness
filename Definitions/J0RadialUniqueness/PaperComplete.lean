import Definitions.J0RadialUniqueness.Analytic
import Definitions.J0RadialUniqueness.TwoRadius
import Definitions.J0RadialUniqueness.Sharpness

/-! The exact sixteen numbered obligations. This proposition is a completion
specification, with no proof asserted while any numbered result remains open. -/

namespace J0RadialUniqueness

def PaperCompleteStatement : Prop :=
  FRightHalfPlaneStatement ∧
  NoRealOnePointsStatement ∧
  QZeroFreeStatement ∧
  GlobalLocalizationStatement ∧
  (KLaplaceStatement ∧ KLaplaceIdentificationStatement) ∧
  (AmplitudeDerivativeStatement ∧ ExactDecompositionStatement) ∧
  (AmplitudeUniformEstimatesStatement ∧ AmplitudeModulusBoundsStatement) ∧
  QuantitativeSeparationStatement ∧
  PrincipalRadialEscapeStatement ∧
  RadialEscape ∧
  RayUniqueness ∧
  (∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ →
    (((r₁ / r₂ : ℝ) : ℂ) ∈ ratioSet ↔
      ∃ lam : ℂ, lam ≠ 0 ∧ J0 (Complex.I * lam * (r₁ : ℂ)) = 1 ∧
        J0 (Complex.I * lam * (r₂ : ℂ)) = 1)) ∧
  ExplicitCounterexampleStatement ∧
  VolchkovLocalStatement ∧
  LocalTwoRadiusStatement ∧
  GlobalTwoRadiusStatement

end J0RadialUniqueness
