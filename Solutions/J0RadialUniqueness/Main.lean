import Solutions.J0RadialUniqueness.K0Identification
import Solutions.J0RadialUniqueness.Conditional.Main

namespace J0RadialUniqueness

theorem exact_decomposition : ExactDecompositionStatement :=
  exactDecomposition_of_laplaceIdentification k_laplace_identification

theorem paper_3_2 : AmplitudeDerivativeStatement ∧ ExactDecompositionStatement :=
  ⟨amplitude_derivatives, exact_decomposition⟩

theorem paper_factorization : FactorizationStatement :=
  factorization_of_exactDecomposition exact_decomposition

theorem quantitative_separation : QuantitativeSeparationStatement :=
  quantitativeSeparation_of_exact exact_decomposition

theorem paper_4_2 : QuantitativeSeparationStatement := quantitative_separation

theorem ray_separation : RaySeparationStatement :=
  raySeparation_of_initial_amplitudes_factorization
    quantitative_separation amplitude_modulus_bounds paper_factorization

theorem radial_derivative_decomposition : RadialDerivativeDecompositionStatement :=
  radialDerivativeDecomposition_of_factorization_and_ray paper_factorization ray_separation

theorem paper_5_1 : PrincipalRadialEscapeStatement :=
  principalRadialEscape_of_analytic_inputs quantitative_separation ray_separation
    amplitude_modulus_bounds delta_derivative radial_derivative_decomposition

theorem paper_5_2 : RadialEscape := radialEscape_of_principal globalLocalization paper_5_1

theorem paper_5_3 : RayUniqueness := rayUniqueness_of_radialEscape paper_5_2

theorem positive_nonunit_ratio_exclusion {c : ℝ} (hc : 0 < c) (hc1 : c ≠ 1) :
    (c : ℂ) ∉ ratioSet := not_mem_ratioSet_of_pos_ne_one paper_5_3 hc hc1

end J0RadialUniqueness
