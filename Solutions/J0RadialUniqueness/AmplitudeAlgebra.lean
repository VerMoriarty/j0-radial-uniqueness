import Definitions.J0RadialUniqueness.Analytic
import Solutions.J0RadialUniqueness.AmplitudeConstants
import Solutions.J0RadialUniqueness.AmplitudeDomain
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

/-!
Reusable algebraic consequences of amplitude estimates and exact decomposition.
Every input is explicit; the actual amplitude estimates are proved separately.
-/

noncomputable section

namespace J0RadialUniqueness

/-- The large-radius part of Proposition 4.1 follows from its integral estimates. -/
theorem amplitudeModulusBounds_of_uniform
    (h : AmplitudeUniformEstimatesStatement) : AmplitudeModulusBoundsStatement := by
  intro z hz hr
  obtain ⟨hp, hm, hp', hm'⟩ := h z hz
  have hkp := kappa_div_lt_one_sixteenth hr
  have hsp : ‖APlus z - 1‖ < (1 / 16 : ℝ) := hp.trans_lt hkp
  have hsm : ‖AMinus z - 1‖ < (1 / 16 : ℝ) := hm.trans_lt hkp
  have hnp := norm_bounds_of_norm_sub_one_lt hsp
  have hnm := norm_bounds_of_norm_sub_one_lt hsm
  exact ⟨hnp.1, hnp.2, hnm.1, hnm.2,
    logarithmic_amplitude_bound hnp.1 (weighted_derivative_lt_one_sixteenth hr hp'),
    logarithmic_amplitude_bound hnm.1 (weighted_derivative_lt_one_sixteenth hr hm')⟩

/-- The factorization uses only the exact decomposition and nonzero amplitudes. -/
theorem factorization_of_exactDecomposition
    (h : ExactDecompositionStatement) : FactorizationStatement := by
  intro z hz
  have hm : AMinus z ≠ 0 := (mul_ne_zero_iff.mp hz.2).2
  let χ : ℂ := z - (Real.pi : ℂ) / 4
  let D : ℂ := Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)
  have he : Complex.exp (-Complex.I * χ) * Complex.exp (2 * Complex.I * χ) =
      Complex.exp (Complex.I * χ) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hc : (Complex.exp (-Complex.I * χ) * AMinus z / D) *
      (Complex.exp (2 * Complex.I * χ) * APlus z / AMinus z) =
      Complex.exp (Complex.I * χ) * APlus z / D := by
    calc
      _ = ((Complex.exp (-Complex.I * χ) * Complex.exp (2 * Complex.I * χ)) *
          APlus z / D) * (AMinus z / AMinus z) := by ring
      _ = Complex.exp (Complex.I * χ) * APlus z / D := by
        rw [div_self hm, mul_one, he]
  change J0 z = (Complex.exp (-Complex.I * χ) * AMinus z / D) *
    (1 + Complex.exp (2 * Complex.I * χ) * APlus z / AMinus z)
  calc
    J0 z = (Complex.exp (Complex.I * χ) * APlus z +
        Complex.exp (-Complex.I * χ) * AMinus z) / D := h z hz.1
    _ = Complex.exp (-Complex.I * χ) * AMinus z / D +
        Complex.exp (Complex.I * χ) * APlus z / D := by ring
    _ = Complex.exp (-Complex.I * χ) * AMinus z / D +
        (Complex.exp (-Complex.I * χ) * AMinus z / D) *
          (Complex.exp (2 * Complex.I * χ) * APlus z / AMinus z) := by rw [hc]
    _ = _ := by ring


end J0RadialUniqueness
