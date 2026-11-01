import Solutions.J0RadialUniqueness.BesselPolePolynomial
import Solutions.J0RadialUniqueness.BesselSpectralBoxBounds
import Solutions.J0RadialUniqueness.SpectralRootCounting
import Solutions.J0RadialUniqueness.SquareContourIntegral
import Mathlib.Tactic

/-! Local principal parts of the actual Bessel spectral integrand, and the
actual finite pole set in each spectral box. The origin has its proved higher
principal part, and every nonzero one-point its proved simple principal part.
This module prepares the finite contour assembly; it does not assume a
residue theorem or assert an infinite spectral expansion as a hypothesis. -/

noncomputable section

open Set Filter Polynomial
open scoped Topology Classical

namespace J0RadialUniqueness

def besselSpectralIntegrand (M : ℕ) (t z : ℂ) : ℂ :=
  J0 (t * z) / (z ^ (2 * M + 1) * (J0 z - 1))

def besselSpectralNumerator (M : ℕ) (t z : ℂ) : ℂ := J0 (t * z) / z ^ (2 * M + 1)

def besselSpectralDefect (z : ℂ) : ℂ := J0 z - 1

theorem besselSpectralIntegrand_eq_simple_quotient (M : ℕ) (t z : ℂ) :
    besselSpectralNumerator M t z / besselSpectralDefect z = besselSpectralIntegrand M t z := by
  simp only [besselSpectralNumerator, besselSpectralDefect, besselSpectralIntegrand, div_div]

theorem besselSpectralNumerator_analyticAt (M : ℕ) (t : ℂ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (besselSpectralNumerator M t) z :=
  ((J0_analyticAt (t * z)).comp (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_id.pow _) (pow_ne_zero _ hz)

theorem besselSpectralDefect_analyticAt (z : ℂ) : AnalyticAt ℂ besselSpectralDefect z :=
  (J0_analyticAt z).sub analyticAt_const

theorem besselSpectralDefect_deriv (z : ℂ) : deriv besselSpectralDefect z = deriv J0 z :=
  ((J0_differentiable z).hasDerivAt.sub_const 1).deriv

theorem besselSpectralIntegrand_analyticAt (M : ℕ) (t : ℂ) {z : ℂ}
    (hz : z ≠ 0) (hJ : J0 z ≠ 1) : AnalyticAt ℂ (besselSpectralIntegrand M t) z := by
  have hh := (besselSpectralNumerator_analyticAt M t hz).div
    (besselSpectralDefect_analyticAt z) (sub_ne_zero.mpr hJ)
  have hfun : (fun w : ℂ => besselSpectralNumerator M t w / besselSpectralDefect w) =
      besselSpectralIntegrand M t := funext (besselSpectralIntegrand_eq_simple_quotient M t)
  change AnalyticAt ℂ (fun w : ℂ => besselSpectralNumerator M t w / besselSpectralDefect w) z at hh
  rw [hfun] at hh
  exact hh

def besselSpectralSimpleResidue (M : ℕ) (t nu : ℂ) : ℂ :=
  J0 (t * nu) / (nu ^ (2 * M + 1) * deriv J0 nu)

def besselSpectralRootCoefficient (M : ℕ) (nu : ℂ) : ℂ :=
  -2 / (nu ^ (2 * M + 1) * deriv J0 nu)

def besselSpectralSimpleRegularPart (M : ℕ) (t nu z : ℂ) : ℂ :=
  simplePoleRegularPart (besselSpectralNumerator M t) besselSpectralDefect nu z

theorem besselSpectralSimpleResidue_eq_generic (M : ℕ) (t nu : ℂ) :
    simplePoleResidue (besselSpectralNumerator M t) besselSpectralDefect nu =
      besselSpectralSimpleResidue M t nu := by
  simp only [simplePoleResidue, besselSpectralNumerator, besselSpectralSimpleResidue,
    besselSpectralDefect_deriv, div_div]

theorem besselSpectralSimpleRegularPart_analyticAt (M : ℕ) (t : ℂ) {nu : ℂ}
    (hnu : nu ≠ 0) (hroot : J0 nu = 1) :
    AnalyticAt ℂ (besselSpectralSimpleRegularPart M t nu) nu := by
  apply simplePoleRegularPart_analyticAt
    (besselSpectralNumerator_analyticAt M t hnu) (besselSpectralDefect_analyticAt nu)
  rw [besselSpectralDefect_deriv]
  exact J0_deriv_ne_zero_at_one_point hnu hroot

/-- The local simple residue and analytic remainder refer to the actual
integrand, with its actual spectral numerator and denominator. -/
theorem besselSpectralSimpleRegularPart_eventuallyEq (M : ℕ) (t : ℂ) {nu : ℂ}
    (hnu : nu ≠ 0) (hroot : J0 nu = 1) :
    ∀ᶠ z : ℂ in 𝓝 nu, z ≠ nu →
      besselSpectralIntegrand M t z =
        besselSpectralSimpleResidue M t nu / (z - nu) +
          besselSpectralSimpleRegularPart M t nu z := by
  have hsimple : deriv besselSpectralDefect nu ≠ 0 := by
    rw [besselSpectralDefect_deriv]
    exact J0_deriv_ne_zero_at_one_point hnu hroot
  have hh := simplePoleRegularPart_eventuallyEq (f := besselSpectralNumerator M t)
    (besselSpectralDefect_analyticAt nu) (sub_eq_zero.mpr hroot) hsimple
  filter_upwards [hh] with z hz hzne
  have heq := hz hzne
  rw [besselSpectralIntegrand_eq_simple_quotient, besselSpectralSimpleResidue_eq_generic] at heq
  change besselSpectralSimpleRegularPart M t nu z = _ at heq
  linear_combination -heq

theorem J0_deriv_neg_value (z : ℂ) : deriv J0 (-z) = -deriv J0 z := by
  have hd : HasDerivAt (fun w : ℂ => J0 (-w)) (-deriv J0 (-z)) z := by
    convert! (J0_differentiable (-z)).hasDerivAt.comp z (hasDerivAt_id z).neg using 1 <;>
      simp only [id_eq, mul_neg, mul_one]
  have hfun : (fun w : ℂ => J0 (-w)) = J0 := funext J0_neg
  rw [hfun] at hd
  have hh := hd.unique (J0_differentiable z).hasDerivAt
  linear_combination -hh

theorem besselSpectralSimpleResidue_neg (M : ℕ) (t nu : ℂ) :
    besselSpectralSimpleResidue M t (-nu) = besselSpectralSimpleResidue M t nu := by
  have hp : (-nu) ^ (2 * M + 1) = -(nu ^ (2 * M + 1)) := by
    simp only [pow_add, pow_mul, neg_sq, pow_one]
    ring
  simp only [besselSpectralSimpleResidue, mul_neg, J0_neg, hp, J0_deriv_neg_value,
    neg_mul_neg, neg_mul, neg_neg]

/-- The minus sign in the cosine-series coefficient comes from moving the
paired nonzero residues to the opposite side of the contour identity. -/
theorem besselSpectralSimpleResidue_pair (M : ℕ) (t nu : ℂ) :
    besselSpectralSimpleResidue M t nu + besselSpectralSimpleResidue M t (-nu) =
      -besselSpectralRootCoefficient M nu * J0 (t * nu) := by
  rw [besselSpectralSimpleResidue_neg]
  simp only [besselSpectralSimpleResidue, besselSpectralRootCoefficient, div_eq_mul_inv]
  ring

theorem J0_sub_one_quadratic_factor (z : ℂ) :
    J0 z - 1 = (-z ^ 2 / 4) * Q (-z ^ 2 / 4) := F_sub_one _

def besselSpectralOriginOrder (M : ℕ) : ℕ := 2 * M + 3

def besselSpectralOriginPrincipalPart (M : ℕ) (t z : ℂ) : ℂ :=
  -4 * finiteLaurentPrincipalPart (besselPoleNumerator t) 0 (besselSpectralOriginOrder M) z

def besselSpectralOriginRegularPart (M : ℕ) (t z : ℂ) : ℂ :=
  -4 * iteratedDSlope (besselPoleNumerator t) 0 (besselSpectralOriginOrder M) z

def besselSpectralOriginResidue (M : ℕ) (t : ℂ) : ℂ :=
  -4 * iteratedDSlope (besselPoleNumerator t) 0 (besselSpectralOriginOrder M - 1) 0

theorem besselSpectralIntegrand_eq_origin_quotient (M : ℕ) (t : ℂ) {z : ℂ} (hz : z ≠ 0) :
    besselSpectralIntegrand M t z =
      -4 * (besselPoleNumerator t z / z ^ besselSpectralOriginOrder M) := by
  have hp : z ^ (2 * M + 3) = z ^ (2 * M + 1) * z ^ 2 := by
    rw [show 2 * M + 3 = (2 * M + 1) + 2 by omega, pow_add]
  unfold besselSpectralIntegrand besselPoleNumerator besselSpectralOriginOrder
  rw [J0_sub_one_quadratic_factor, hp]
  by_cases hQ : Q (-z ^ 2 / 4) = 0
  · simp only [hQ, mul_zero, div_zero, zero_div, mul_zero]
  · field_simp [hz, hQ] <;> ring

theorem besselSpectralOriginRegularPart_analyticAt (M : ℕ) (t : ℂ) :
    AnalyticAt ℂ (besselSpectralOriginRegularPart M t) 0 :=
  analyticAt_const.mul (iteratedDSlope_analyticAt (besselPoleNumerator_hasFPowerSeriesAt t).analyticAt
    (besselSpectralOriginOrder M))

/-- The explicit higher-principal-part identity is valid at every nonzero
parameter, so in particular on every punctured neighborhood of zero. -/
theorem besselSpectralIntegrand_eq_origin_principal_add (M : ℕ) (t : ℂ) {z : ℂ} (hz : z ≠ 0) :
    besselSpectralIntegrand M t z =
      besselSpectralOriginPrincipalPart M t z + besselSpectralOriginRegularPart M t z := by
  rw [besselSpectralIntegrand_eq_origin_quotient M t hz]
  have hh := div_pow_eq_finiteLaurentPrincipalPart_add
    (besselPoleNumerator t) 0 (besselSpectralOriginOrder M) hz
  simp only [sub_zero] at hh
  rw [hh]
  unfold besselSpectralOriginPrincipalPart besselSpectralOriginRegularPart
  ring

theorem besselSpectralOriginResidue_eq_polynomial (M : ℕ) (t : ℂ) :
    besselSpectralOriginResidue M t = (besselPolePolynomial M).eval t := by
  have hn : besselSpectralOriginOrder M - 1 = 2 * (M + 1) := by
    unfold besselSpectralOriginOrder
    omega
  rw [besselSpectralOriginResidue, hn, besselPolePolynomial_eval]

def besselSpectralClosedBox (n : ℕ) : Set ℂ :=
  {z | |z.re| ≤ besselSpectralBoxRadius n ∧ |z.im| ≤ besselSpectralBoxRadius n}

def besselSpectralOpenBox (n : ℕ) : Set ℂ :=
  {z | |z.re| < besselSpectralBoxRadius n ∧ |z.im| < besselSpectralBoxRadius n}

/-- The finite pole set includes the genuine higher pole at zero. -/
def besselSpectralBoxPoles (n : ℕ) : Set ℂ :=
  {z | z ∈ besselSpectralClosedBox n ∧ (z = 0 ∨ J0 z = 1)}

theorem besselSpectralBoxPoles_finite (n : ℕ) : (besselSpectralBoxPoles n).Finite := by
  apply ((finite_singleton (0 : ℂ)).union
    (onePoints_inter_closedBall_finite (2 * besselSpectralBoxRadius n))).subset
  intro z hz
  by_cases hz0 : z = 0
  · exact Or.inl (mem_singleton_iff.mpr hz0)
  · right
    refine ⟨⟨hz0, hz.2.resolve_left hz0⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith [hz.1.1, hz.1.2])

theorem besselSpectralBoxPoles_zero (n : ℕ) : (0 : ℂ) ∈ besselSpectralBoxPoles n := by
  refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩ <;>
    simpa only [Complex.zero_re, Complex.zero_im, abs_zero] using (besselSpectralBoxRadius_pos n).le

theorem besselSpectralBoxPoles_subset_open {n : ℕ} (hn : 100 ≤ n) :
    besselSpectralBoxPoles n ⊆ besselSpectralOpenBox n := by
  obtain ⟨C, hC, hbound⟩ := exists_bessel_spectral_box_ratio_bound
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    exact ⟨by simpa only [Complex.zero_re, abs_zero] using besselSpectralBoxRadius_pos n,
      by simpa only [Complex.zero_im, abs_zero] using besselSpectralBoxRadius_pos n⟩
  · have hroot : J0 z = 1 := hz.2.resolve_left hz0
    rcases lt_or_eq_of_le hz.1.1 with hre | hre
    · rcases lt_or_eq_of_le hz.1.2 with him | him
      · exact ⟨hre, him⟩
      · exact False.elim ((hbound n hn z (Or.inr ⟨him, hz.1.1⟩)).1 hroot)
    · exact False.elim ((hbound n hn z (Or.inl ⟨hre, hz.1.2⟩)).1 hroot)

theorem besselSpectralDenominator_eq_zero_iff (M : ℕ) (z : ℂ) :
    z ^ (2 * M + 1) * (J0 z - 1) = 0 ↔ z = 0 ∨ J0 z = 1 := by
  constructor
  · intro hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hz0)))
  · rintro (rfl | hJ)
    · simp
    · simp [hJ]

theorem besselSpectralBoundary_eq_square (n : ℕ) :
    besselSpectralBoxBoundary n = squareBoundarySet (besselSpectralBoxRadius n) := rfl

end J0RadialUniqueness
