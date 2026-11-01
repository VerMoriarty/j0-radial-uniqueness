import Solutions.J0RadialUniqueness.BesselFiniteContourIdentity
import Solutions.J0RadialUniqueness.BesselSpectralContourDecay

/-! The actual infinite Bessel expansion of the nonconstant pole polynomial.
The finite contour formula, its proved vanishing limit, and the actual root
box exhaustion are combined here. No completeness or spectral expansion
statement is assumed. -/

noncomputable section

open Set Filter
open scoped Topology

namespace J0RadialUniqueness

theorem besselRadialRootSeries_eq_polynomial (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    besselRadialRootSeries M t = (besselPolePolynomial M).eval (t : ℂ) := by
  let q : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let K : ℂ := (besselPolePolynomial M).eval (t : ℂ)
  have hsum := besselSpectralRightBoxSum_tendsto M hM ht
  have hlim : Tendsto (fun n : ℕ => q * (K - besselSpectralRightBoxSum M (t : ℂ) n)) atTop
      (𝓝 (q * (K - besselRadialRootSeries M t))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hsum)
  have hzero := besselSpectralContourIntegral_tendsto_zero M (by omega : 1 ≤ M) ht
  have heq : (fun n : ℕ => squareBoundaryIntegral (besselSpectralBoxRadius n)
      (besselSpectralIntegrand M (t : ℂ))) =ᶠ[atTop]
      (fun n : ℕ => q * (K - besselSpectralRightBoxSum M (t : ℂ) n)) := by
    filter_upwards [eventually_ge_atTop (100 : ℕ)] with n hn
    exact besselSpectral_finite_contour_identity M (t : ℂ) hn
  have hzero' : Tendsto (fun n : ℕ => q * (K - besselSpectralRightBoxSum M (t : ℂ) n)) atTop
      (𝓝 0) := (tendsto_congr' heq).mp hzero
  have hvalue : q * (K - besselRadialRootSeries M t) = 0 := tendsto_nhds_unique hlim hzero'
  have hq : q ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hvalue).resolve_left hq)).symm

/-- The polynomial is the sum of the genuine absolutely convergent series
over the actual right-half-plane roots. -/
theorem hasSum_besselRadialRootSeries_polynomial (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun z : RightOnePoint => besselResidueCoefficient M z * J0 ((t : ℂ) * (z : ℂ)))
      ((besselPolePolynomial M).eval (t : ℂ)) := by
  rw [← besselRadialRootSeries_eq_polynomial M hM ht]
  exact (besselRadialRootSeries_summable M hM ht).hasSum

end J0RadialUniqueness
