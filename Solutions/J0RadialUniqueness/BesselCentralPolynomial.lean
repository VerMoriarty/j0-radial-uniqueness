import Solutions.J0RadialUniqueness.BesselCosinePoisson
import Solutions.J0RadialUniqueness.RootExponentialSeriesSmooth

/-! The central polynomial of the actual Bessel cosine series.  The pole
polynomial is first written as a polynomial in the square of its argument.
Dividing its coefficients by the positive Poisson moments gives an explicit
even, nonconstant polynomial.  Actual Poisson inversion then identifies the
cosine series with that polynomial on the whole closed unit interval. -/

noncomputable section

open Set Polynomial
open scoped Topology BigOperators ContDiff

namespace J0RadialUniqueness

theorem besselPolePolynomial_coeff_even (M : ℕ) {k : ℕ}
    (hk : k ∈ Finset.range (M + 2)) :
    (besselPolePolynomial M).coeff (2 * k) =
      (-4 : ℂ) * (-1 / 4 : ℂ) ^ (M + 1) * inverseQCoeff (M + 1 - k) /
        (k.factorial : ℂ) ^ 2 := by
  unfold besselPolePolynomial
  rw [finset_sum_coeff, Finset.sum_eq_single k]
  · simp only [coeff_monomial, ite_true]
  · intro j hj hjne
    have hne : 2 * j ≠ 2 * k := by omega
    simp only [coeff_monomial, if_neg hne]
  · exact fun hnot => False.elim (hnot hk)

/-- The polynomial in the squared radius uses exactly the even coefficients
of the actual origin-residue polynomial. -/
def besselPoleHalfPolynomial (M : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (M + 2),
    monomial k ((besselPolePolynomial M).coeff (2 * k))

theorem besselPoleHalfPolynomial_coeff (M : ℕ) {k : ℕ}
    (hk : k ∈ Finset.range (M + 2)) :
    (besselPoleHalfPolynomial M).coeff k = (besselPolePolynomial M).coeff (2 * k) := by
  unfold besselPoleHalfPolynomial
  rw [finset_sum_coeff, Finset.sum_eq_single k]
  · simp only [coeff_monomial, ite_true]
  · intro j hj hjne
    simp only [coeff_monomial, if_neg hjne]
  · exact fun hnot => False.elim (hnot hk)

theorem besselPoleHalfPolynomial_eval_square (M : ℕ) (t : ℂ) :
    (besselPoleHalfPolynomial M).eval (t ^ 2) = (besselPolePolynomial M).eval t := by
  simp only [besselPoleHalfPolynomial, eval_finset_sum, eval_monomial]
  conv_rhs => rw [besselPolePolynomial, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [besselPolePolynomial_coeff_even M hk, eval_monomial, pow_mul]

theorem besselPoleHalfPolynomial_highest_coeff (M : ℕ) :
    (besselPoleHalfPolynomial M).coeff (M + 1) =
      (besselPolePolynomial M).coeff (2 * (M + 1)) :=
  besselPoleHalfPolynomial_coeff M (Finset.mem_range.mpr (by omega))

theorem besselPoleHalfPolynomial_highest_coeff_ne_zero (M : ℕ) :
    (besselPoleHalfPolynomial M).coeff (M + 1) ≠ 0 := by
  rw [besselPoleHalfPolynomial_highest_coeff]
  exact besselPolePolynomial_highest_coeff_ne_zero M

theorem besselPoleHalfPolynomial_natDegree (M : ℕ) :
    (besselPoleHalfPolynomial M).natDegree = M + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ (besselPoleHalfPolynomial_highest_coeff_ne_zero M)
  unfold besselPoleHalfPolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hk; omega)

/-- Coefficient extraction from the explicit inverse-moment polynomial. -/
theorem evenPoissonInversePolynomial_coeff_even (K : ℂ[X]) {k : ℕ}
    (hk : k ≤ K.natDegree) :
    (evenPoissonInversePolynomial K).coeff (2 * k) =
      K.coeff k / (evenPoissonMoment k : ℂ) := by
  unfold evenPoissonInversePolynomial
  rw [finset_sum_coeff, Finset.sum_eq_single k]
  · simp only [coeff_monomial, ite_true]
  · intro j hj hjne
    have hne : 2 * j ≠ 2 * k := by omega
    simp only [coeff_monomial, if_neg hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

def besselCentralPolynomial (M : ℕ) : ℂ[X] :=
  evenPoissonInversePolynomial (besselPoleHalfPolynomial M)

theorem besselCentralPolynomial_even (M : ℕ) :
    Function.Even (fun z : ℂ => (besselCentralPolynomial M).eval z) :=
  evenPoissonInversePolynomial_even (besselPoleHalfPolynomial M)

theorem besselCentralPolynomial_highest_coeff (M : ℕ) :
    (besselCentralPolynomial M).coeff (2 * (M + 1)) =
      (besselPoleHalfPolynomial M).coeff (M + 1) /
        (evenPoissonMoment (M + 1) : ℂ) := by
  apply evenPoissonInversePolynomial_coeff_even
  exact le_natDegree_of_ne_zero (besselPoleHalfPolynomial_highest_coeff_ne_zero M)

theorem besselCentralPolynomial_highest_coeff_ne_zero (M : ℕ) :
    (besselCentralPolynomial M).coeff (2 * (M + 1)) ≠ 0 := by
  rw [besselCentralPolynomial_highest_coeff]
  exact div_ne_zero (besselPoleHalfPolynomial_highest_coeff_ne_zero M)
    (Complex.ofReal_ne_zero.mpr (evenPoissonMoment_pos (M + 1)).ne')

theorem besselCentralPolynomial_natDegree (M : ℕ) :
    (besselCentralPolynomial M).natDegree = 2 * (M + 1) := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ (besselCentralPolynomial_highest_coeff_ne_zero M)
  unfold besselCentralPolynomial evenPoissonInversePolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [besselPoleHalfPolynomial_natDegree] at hk'
  exact (natDegree_monomial_le _).trans (by omega)

theorem besselCentralPolynomial_ne_constant (M : ℕ) (c : ℂ) :
    besselCentralPolynomial M ≠ C c := by
  intro heq
  have hh := congrArg (fun P : ℂ[X] => P.coeff (2 * (M + 1))) heq
  have hn : 2 * (M + 1) ≠ 0 := by omega
  simp only [coeff_C, if_neg hn] at hh
  exact besselCentralPolynomial_highest_coeff_ne_zero M hh

/-- The actual convergent cosine root series equals the explicit central
polynomial.  Both the Bessel spectral expansion and the Poisson transform
are the previously proved statements about the actual integrals. -/
theorem besselCosineSeries_eq_centralPolynomial (M : ℕ) (hM : 2 ≤ M) :
    ∀ x ∈ Icc (-1 : ℝ) 1,
      besselCosineSeries M x = (besselCentralPolynomial M).eval (x : ℂ) := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hc : ContinuousOn (besselCosineSeries M) (Icc (-1 : ℝ) 1) :=
    besselCosineSeries_continuousOn M (by norm_num) (by linarith)
  have hs : ContDiffOn ℝ 1 (besselCosineSeries M) (Ioo (-1 : ℝ) 1) :=
    besselCosineSeries_contDiffOn M 1 (by norm_num) (by push_cast; linarith)
  have hd : DifferentiableAt ℝ (besselCosineSeries M) 0 :=
    (hs.differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds (by constructor <;> norm_num))
  apply evenPoissonPolynomialRecovery_of_differentiable hc (besselCosineSeries_even M) hd
    (besselPoleHalfPolynomial M)
  intro t ht
  rw [evenPoissonTransform_besselCosineSeries_eq_radial M hM ht,
    besselRadialRootSeries_eq_polynomial M hM ht,
    besselPoleHalfPolynomial_eval_square]

end J0RadialUniqueness
