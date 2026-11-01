import Solutions.J0RadialUniqueness.CircularBesselIntegral
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Explicit polynomial inversion for the actual centered even Poisson mean.
This first stage proves the exact moments, constructs the even inverse
polynomial, and reduces a polynomial mean to a genuine zero-mean difference.
The analytic injectivity of that zero-mean difference is a separate stage. -/

noncomputable section

open MeasureTheory
open scoped Topology Interval BigOperators

namespace J0RadialUniqueness

def evenPoissonMoment (j : ℕ) : ℝ := ((2 * j).choose j : ℝ) / 4 ^ j

theorem evenPoissonMoment_pos (j : ℕ) : 0 < evenPoissonMoment j := by
  have hc : 0 < ((2 * j).choose j : ℝ) := by
    exact_mod_cast Nat.choose_pos (show j ≤ 2 * j by omega)
  exact div_pos hc (by positivity)

@[simp] theorem evenPoissonMoment_zero : evenPoissonMoment 0 = 1 := by
  norm_num [evenPoissonMoment]

theorem evenPoissonMoment_factorial_identity (j : ℕ) :
    ((2 * j).choose j : ℝ) * (j.factorial : ℝ) ^ 2 = ((2 * j).factorial : ℝ) := by
  have hh := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
  rw [show 2 * j - j = j by omega] at hh
  have hc := congrArg (fun k : ℕ => (k : ℝ)) hh
  push_cast at hc
  simpa only [pow_two, mul_assoc] using hc

theorem integral_cos_pow_even_eq_moment (j : ℕ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ (2 * j)) =
      2 * Real.pi * evenPoissonMoment j := by
  rw [integral_cos_pow_even_full, ← evenPoissonMoment_factorial_identity]
  unfold evenPoissonMoment
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ j ≠ 0 := by positivity
  field_simp [hf, hfour] <;> ring

def evenPoissonTransform (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  circularMean (fun x : Plane => h (x 0)) t 0

theorem centeredCircle_firstCoordinate (t θ : ℝ) :
    ((0 : Plane) + t • circleDirection θ) 0 = t * Real.cos θ := by
  simp only [zero_add, PiLp.smul_apply, circleDirection, PiLp.toLp_apply,
    Matrix.cons_val_zero, smul_eq_mul]

theorem evenPoissonTransform_eq_integral (h : ℝ → ℂ) (t : ℝ) :
    evenPoissonTransform h t = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), h (t * Real.cos θ) := by
  unfold evenPoissonTransform circularMean
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [centeredCircle_firstCoordinate]

@[simp] theorem evenPoissonTransform_zero (h : ℝ → ℂ) : evenPoissonTransform h 0 = h 0 := by
  have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  rw [evenPoissonTransform_eq_integral]
  simp only [zero_mul, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ hp, one_smul]

theorem evenPoissonTransform_const_mul (c : ℂ) (h : ℝ → ℂ) (t : ℝ) :
    evenPoissonTransform (fun x => c * h x) t = c * evenPoissonTransform h t := by
  simp only [evenPoissonTransform_eq_integral, intervalIntegral.integral_const_mul, Complex.real_smul]
  ring

theorem evenPoissonTransform_even_monomial (j : ℕ) (t : ℝ) :
    evenPoissonTransform (fun x : ℝ => (x : ℂ) ^ (2 * j)) t =
      (evenPoissonMoment j : ℂ) * (t : ℂ) ^ (2 * j) := by
  rw [evenPoissonTransform_eq_integral]
  have hfun : (fun θ : ℝ => ((t * Real.cos θ : ℝ) : ℂ) ^ (2 * j)) =
      fun θ : ℝ => (t : ℂ) ^ (2 * j) * ((Real.cos θ ^ (2 * j) : ℝ) : ℂ) := by
    funext θ
    simp only [Complex.ofReal_mul, mul_pow, Complex.ofReal_pow]
  rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_cos_pow_even_eq_moment, Complex.real_smul]
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp] <;> ring

theorem evenPoissonTransform_finsetSum {ι : Type*} (S : Finset ι) (h : ι → ℝ → ℂ)
    (hc : ∀ j ∈ S, Continuous (h j)) (t : ℝ) :
    evenPoissonTransform (fun x : ℝ => ∑ j ∈ S, h j x) t =
      ∑ j ∈ S, evenPoissonTransform (h j) t := by
  simp only [evenPoissonTransform_eq_integral]
  have hi (j : ι) (hj : j ∈ S) :
      IntervalIntegrable (fun θ : ℝ => h j (t * Real.cos θ)) volume 0 (2 * Real.pi) :=
    ((hc j hj).comp (continuous_const.mul Real.continuous_cos)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hi, Finset.smul_sum]

/-- The inverse moment polynomial has only even powers, with its coefficients
given explicitly by division by the positive central-binomial moments. -/
def evenPoissonInversePolynomial (K : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (K.natDegree + 1),
    Polynomial.monomial (2 * j) (K.coeff j / (evenPoissonMoment j : ℂ))

theorem evenPoissonInversePolynomial_eval (K : Polynomial ℂ) (x : ℂ) :
    (evenPoissonInversePolynomial K).eval x =
      ∑ j ∈ Finset.range (K.natDegree + 1), K.coeff j / (evenPoissonMoment j : ℂ) * x ^ (2 * j) := by
  simp only [evenPoissonInversePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem evenPoissonInversePolynomial_even (K : Polynomial ℂ) :
    Function.Even (fun x : ℂ => (evenPoissonInversePolynomial K).eval x) := by
  intro x
  simp only [evenPoissonInversePolynomial_eval]
  apply Finset.sum_congr rfl
  intro j _
  rw [(even_two_mul j).neg_pow]

/-- The explicitly constructed polynomial has exactly the prescribed actual
circle mean at every real radius. -/
theorem evenPoissonInversePolynomial_mean (K : Polynomial ℂ) (t : ℝ) :
    evenPoissonTransform (fun x : ℝ => (evenPoissonInversePolynomial K).eval (x : ℂ)) t =
      K.eval ((t : ℂ) ^ 2) := by
  have hfun : (fun x : ℝ => (evenPoissonInversePolynomial K).eval (x : ℂ)) =
      fun x : ℝ => ∑ j ∈ Finset.range (K.natDegree + 1),
        K.coeff j / (evenPoissonMoment j : ℂ) * (x : ℂ) ^ (2 * j) :=
    funext (fun x => evenPoissonInversePolynomial_eval K (x : ℂ))
  rw [hfun, evenPoissonTransform_finsetSum]
  · simp_rw [evenPoissonTransform_const_mul, evenPoissonTransform_even_monomial]
    rw [Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hμ : (evenPoissonMoment j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (evenPoissonMoment_pos j).ne'
    simp only [pow_mul]
    field_simp [hμ] <;> ring
  · intro j _
    exact continuous_const.mul ((Complex.continuous_ofReal).pow (2 * j))

@[simp] theorem evenPoissonInversePolynomial_eval_zero (K : Polynomial ℂ) :
    (evenPoissonInversePolynomial K).eval 0 = K.eval 0 := by
  have hh := evenPoissonInversePolynomial_mean K 0
  simpa only [evenPoissonTransform_zero, Complex.ofReal_zero, zero_pow (by norm_num : 2 ≠ 0)] using hh

theorem continuous_evenPoisson_integrand_on_unit_interval {h : ℝ → ℂ}
    (hh : ContinuousOn h (Set.Icc (-1 : ℝ) 1)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Continuous (fun θ : ℝ => h (t * Real.cos θ)) := by
  apply hh.comp_continuous (continuous_const.mul Real.continuous_cos)
  intro θ
  dsimp only [Pi.mul_apply]
  have h₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) ht.1
  have h₂ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) ht.1
  exact ⟨by nlinarith [ht.2], by nlinarith [ht.2]⟩

/-- Reduction to a true zero-mean difference on the entire closed unit
radius interval. This uses only continuity on the actual sampled segment. -/
theorem evenPoisson_polynomial_mean_difference_zero {h : ℝ → ℂ}
    (hh : ContinuousOn h (Set.Icc (-1 : ℝ) 1)) (K : Polynomial ℂ)
    (hmean : ∀ t ∈ Set.Icc (0 : ℝ) 1, evenPoissonTransform h t = K.eval ((t : ℂ) ^ 2)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      evenPoissonTransform (fun x : ℝ => h x - (evenPoissonInversePolynomial K).eval (x : ℂ)) t = 0 := by
  intro t ht
  have hhI := (continuous_evenPoisson_integrand_on_unit_interval hh ht).intervalIntegrable
    (μ := volume) 0 (2 * Real.pi)
  have hPI : IntervalIntegrable (fun θ : ℝ =>
      (evenPoissonInversePolynomial K).eval ((t * Real.cos θ : ℝ) : ℂ)) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact (evenPoissonInversePolynomial K).continuous.comp
      (Complex.continuous_ofReal.comp (continuous_const.mul Real.continuous_cos))
  have hsub : evenPoissonTransform (fun x : ℝ => h x - (evenPoissonInversePolynomial K).eval (x : ℂ)) t =
      evenPoissonTransform h t -
        evenPoissonTransform (fun x : ℝ => (evenPoissonInversePolynomial K).eval (x : ℂ)) t := by
    simp only [evenPoissonTransform_eq_integral]
    rw [intervalIntegral.integral_sub hhI hPI, smul_sub]
  rw [hsub, hmean t ht, evenPoissonInversePolynomial_mean, sub_self]

theorem evenPoisson_polynomial_difference_even {h : ℝ → ℂ} (hh : Function.Even h)
    (K : Polynomial ℂ) :
    Function.Even (fun x : ℝ => h x - (evenPoissonInversePolynomial K).eval (x : ℂ)) := by
  intro x
  dsimp only
  have he := evenPoissonInversePolynomial_even K (x : ℂ)
  dsimp only at he
  rw [hh x, Complex.ofReal_neg, he]

theorem evenPoisson_polynomial_difference_zero_at_zero {h : ℝ → ℂ} (K : Polynomial ℂ)
    (hmean : ∀ t ∈ Set.Icc (0 : ℝ) 1, evenPoissonTransform h t = K.eval ((t : ℂ) ^ 2)) :
    h 0 - (evenPoissonInversePolynomial K).eval ((0 : ℝ) : ℂ) = 0 := by
  have hh := hmean 0 ⟨le_refl 0, by norm_num⟩
  simp only [evenPoissonTransform_zero, Complex.ofReal_zero, zero_pow (by norm_num : 2 ≠ 0)] at hh
  rw [Complex.ofReal_zero, evenPoissonInversePolynomial_eval_zero, hh, sub_self]

end J0RadialUniqueness
