import Solutions.J0RadialUniqueness.Conditional.Localization
import Solutions.J0RadialUniqueness.Conditional.Amplitude
import Solutions.J0RadialUniqueness.Conditional.RaySeparation
import Solutions.J0RadialUniqueness.Conditional.RadialEscape
import Solutions.J0RadialUniqueness.Conditional.Spectral
import Solutions.J0RadialUniqueness.Localization
import Solutions.J0RadialUniqueness.AmplitudeUniform
import Solutions.J0RadialUniqueness.ExactDecomposition
import Solutions.J0RadialUniqueness.Conditional.QuantitativeSeparation
import Solutions.J0RadialUniqueness.Conditional.RadialDifferentiation

namespace J0RadialUniqueness

/-- A checked assembly of the radial theorem, with every remaining analytic input explicit.
This is a conditional reduction, not a proof of Theorem A. -/
theorem radialEscape_of_remaining_analytic_inputs
    (hhalf : FRightHalfPlaneStatement) (hreal : NoRealOnePointsStatement)
    (huniform : AmplitudeUniformEstimatesStatement)
    (hampderiv : AmplitudeDerivativeStatement)
    (hexact : ExactDecompositionStatement)
    (hseparation : QuantitativeSeparationStatement)
    (hlogderiv : RadialDerivativeDecompositionStatement) : RadialEscape := by
  have hmod := amplitudeModulusBounds_of_uniform huniform
  have hfac := factorization_of_exactDecomposition hexact
  have hray := raySeparation_of_initial_amplitudes_factorization hseparation hmod hfac
  have hdelt := deltaDerivative_of_amplitudeDerivative hampderiv
  have hprincipal := principalRadialEscape_of_analytic_inputs hseparation hray hmod hdelt hlogderiv
  exact radialEscape_of_principal
    (globalLocalization_of_halfPlane_and_real hhalf hreal) hprincipal

/-- Localization is now closed; five analytic inputs still remain for Theorem A. -/
theorem radialEscape_of_five_analytic_inputs
    (huniform : AmplitudeUniformEstimatesStatement)
    (hampderiv : AmplitudeDerivativeStatement)
    (hexact : ExactDecompositionStatement)
    (hseparation : QuantitativeSeparationStatement)
    (hlogderiv : RadialDerivativeDecompositionStatement) : RadialEscape := by
  have hmod := amplitudeModulusBounds_of_uniform huniform
  have hfac := factorization_of_exactDecomposition hexact
  have hray := raySeparation_of_initial_amplitudes_factorization hseparation hmod hfac
  exact radialEscape_of_principal globalLocalization
    (principalRadialEscape_of_analytic_inputs hseparation hray hmod
      (deltaDerivative_of_amplitudeDerivative hampderiv) hlogderiv)

/-- All amplitude, separation and ordinary radial differentiation inputs are
discharged. Only identification of the independent Laplace integral remains. -/
theorem radialEscape_of_laplaceIdentification
    (hident : KLaplaceIdentificationStatement) : RadialEscape := by
  have hexact := exactDecomposition_of_laplaceIdentification hident
  have hfact := factorization_of_exactDecomposition hexact
  have hsep := quantitativeSeparation_of_exact hexact
  have hray := raySeparation_of_initial_amplitudes_factorization
    hsep amplitude_modulus_bounds hfact
  exact radialEscape_of_five_analytic_inputs amplitude_uniform_estimates
    amplitude_derivatives hexact hsep
    (radialDerivativeDecomposition_of_factorization_and_ray hfact hray)

end J0RadialUniqueness
