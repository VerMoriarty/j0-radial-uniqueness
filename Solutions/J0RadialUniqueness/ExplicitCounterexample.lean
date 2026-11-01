import Solutions.J0RadialUniqueness.CircularBesselIntegral
import Solutions.J0RadialUniqueness.SpectralExponential
import Mathlib.Tactic

/-! Proposition 6.2 with its actual real-valued spectral witness.

The complex mean identity is proved from the exponential series in
`CircularBesselIntegral`.  Passing to the real and imaginary parts below uses
interval integrability of the actual circle integrand.  Nonharmonicity is
witnessed by a nonzero Laplacian at the origin.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace J0RadialUniqueness

/-- The actual complex circle integrand is continuous, hence interval integrable. -/
theorem spectralExponential_circle_intervalIntegrable (lam : ℂ) (r : ℝ) (x : Plane) :
    IntervalIntegrable
      (fun t : ℝ => spectralExponential lam (x + r • circleDirection t))
      volume (0 : ℝ) (2 * Real.pi) := by
  have hfun :
      (fun t : ℝ => spectralExponential lam (x + r • circleDirection t)) =
        fun t : ℝ => spectralExponential lam x *
          Complex.exp ((lam * (r : ℂ)) * (Real.cos t : ℂ)) := by
    funext t
    exact spectralExponential_circle_factor lam r x t
  rw [hfun]
  apply Continuous.intervalIntegrable
  fun_prop

/-- Taking real parts commutes with the normalized circular mean of the exponential. -/
theorem circularMean_spectralRealPart (lam : ℂ) (r : ℝ) (x : Plane) :
    circularMean (spectralRealPart lam) r x =
      (circularMean (spectralExponential lam) r x).re := by
  have h := Complex.reCLM.intervalIntegral_comp_comm
    (spectralExponential_circle_intervalIntegrable lam r x)
  unfold circularMean spectralRealPart
  rw [Complex.smul_re]
  apply congrArg (fun y : ℝ => ((2 * Real.pi)⁻¹ : ℝ) • y)
  simpa only [Complex.reCLM_apply] using h

/-- Taking imaginary parts commutes with the normalized circular mean of the exponential. -/
theorem circularMean_spectralImagPart (lam : ℂ) (r : ℝ) (x : Plane) :
    circularMean (spectralImagPart lam) r x =
      (circularMean (spectralExponential lam) r x).im := by
  have h := Complex.imCLM.intervalIntegral_comp_comm
    (spectralExponential_circle_intervalIntegrable lam r x)
  unfold circularMean spectralImagPart
  rw [Complex.smul_im]
  apply congrArg (fun y : ℝ => ((2 * Real.pi)⁻¹ : ℝ) • y)
  simpa only [Complex.imCLM_apply] using h

/-- The real part has the required mean property whenever the actual multiplier is one. -/
theorem circularMean_spectralRealPart_of_J0_eq_one (lam : ℂ) (r : ℝ)
    (hJ : J0 (Complex.I * lam * (r : ℂ)) = 1) (x : Plane) :
    circularMean (spectralRealPart lam) r x = spectralRealPart lam x := by
  rw [circularMean_spectralRealPart, circularMean_spectralExponential, hJ, mul_one]
  rfl

/-- The imaginary part has the same mean property. -/
theorem circularMean_spectralImagPart_of_J0_eq_one (lam : ℂ) (r : ℝ)
    (hJ : J0 (Complex.I * lam * (r : ℂ)) = 1) (x : Plane) :
    circularMean (spectralImagPart lam) r x = spectralImagPart lam x := by
  rw [circularMean_spectralImagPart, circularMean_spectralExponential, hJ, mul_one]
  rfl

/-- Proposition 6.2: a shared nonzero spectral frequency gives an explicit smooth
real-valued nonharmonic function with both circular mean identities everywhere. -/
theorem paper_6_2 : ExplicitCounterexampleStatement := by
  intro r₁ r₂ _hr₁ _hr₂ lam hlam hJ₁ hJ₂
  rcases exists_spectral_nonharmonic_witness lam hlam with
    ⟨g, hg, hcont, hnot, _hDelta⟩
  have hm (r : ℝ) (hJ : J0 (Complex.I * lam * (r : ℂ)) = 1) :
      ∀ x : Plane, circularMean g r x = g x := by
    rcases hg with rfl | rfl
    · exact circularMean_spectralRealPart_of_J0_eq_one lam r hJ
    · exact circularMean_spectralImagPart_of_J0_eq_one lam r hJ
  exact ⟨g, hg, hcont, hnot, hm r₁ hJ₁, hm r₂ hJ₂⟩

end J0RadialUniqueness
