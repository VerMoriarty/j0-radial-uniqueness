import Solutions.J0RadialUniqueness.FiniteHigherPoleSubtraction
import Solutions.J0RadialUniqueness.QAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! The genuine origin-pole coefficient in the Bessel spectral construction.
The polynomial is identified with the iterated divided difference of the
actual analytic numerator J₀(tz)/Q(-z²/4). Its highest coefficient is nonzero.
The proof uses convergent scalar power series, including their actual Cauchy
product; no formal coefficient is substituted for an analytic coefficient. -/

noncomputable section

open Filter Set Polynomial
open scoped Topology

namespace J0RadialUniqueness

theorem iteratedDSlope_eq_function_iterate (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    iteratedDSlope f a n = (Function.swap dslope a)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratedDSlope, Function.iterate_succ_apply', ← ih, Function.swap]

/-- Coefficients extracted by the actual repeated divided difference agree
with the coefficients of any genuine local power-series expansion. -/
theorem iteratedDSlope_eq_powerSeries_coeff {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) (n : ℕ) :
    iteratedDSlope f 0 n 0 = p.coeff n := by
  have hh := (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero (1 : Fin 0 → ℂ)
  change (FormalMultilinearSeries.fslope^[n] p).coeff 0 =
    ((Function.swap dslope 0)^[n] f) 0 at hh
  rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
    ← iteratedDSlope_eq_function_iterate] at hh
  exact hh.symm

def inverseQCoeff (n : ℕ) : ℂ := iteratedDSlope (fun w : ℂ => (Q w)⁻¹) 0 n 0

@[simp] theorem inverseQCoeff_zero : inverseQCoeff 0 = 1 := by
  simp [inverseQCoeff]

theorem inverseQ_analyticAt_zero : AnalyticAt ℂ (fun w : ℂ => (Q w)⁻¹) 0 :=
  (Q_analyticAt 0).inv (by simp)

theorem inverseQ_hasFPowerSeriesAt :
    HasFPowerSeriesAt (fun w : ℂ => (Q w)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ inverseQCoeff) 0 := by
  obtain ⟨p, hp⟩ := inverseQ_analyticAt_zero
  have heq : p = FormalMultilinearSeries.ofScalars ℂ inverseQCoeff := by
    apply FormalMultilinearSeries.ext
    intro n
    apply ContinuousMultilinearMap.ext
    intro v
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, FormalMultilinearSeries.coeff_ofScalars]
    rw [← iteratedDSlope_eq_powerSeries_coeff hp n]
    rfl
  rw [← heq]
  exact hp

theorem scaledF_hasFPowerSeriesAt (c : ℂ) :
    HasFPowerSeriesAt (fun w : ℂ => F (c * w))
      (FormalMultilinearSeries.ofScalars ℂ (fun n => c ^ n / (n.factorial : ℂ) ^ 2)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  refine Eventually.of_forall (fun w => ?_)
  have hfun : (fun n : ℕ => w ^ n •
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => c ^ n / (n.factorial : ℂ) ^ 2)).coeff n) = fTerm (c * w) := by
    funext n
    simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, fTerm, mul_pow]
    ring
  rw [hfun, zero_add]
  exact (fTerm_summable (c * w)).hasSum

def scalarTaylorConvolution (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- The scalar power-series product is justified by absolute summability of
the two actual local series. -/
theorem scalar_powerSeries_mul {f g : ℂ → ℂ} {a b : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0) :
    HasFPowerSeriesAt (fun w : ℂ => f w * g w)
      (FormalMultilinearSeries.ofScalars ℂ (scalarTaylorConvolution a b)) 0 := by
  rw [hasFPowerSeriesAt_iff] at hf hg ⊢
  filter_upwards [hf, hg] with w hfw hgw
  simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add] at hfw hgw ⊢
  have hh := hasSum_sum_range_mul_of_summable_norm hfw.summable.norm hgw.summable.norm
  rw [hfw.tsum_eq, hgw.tsum_eq] at hh
  have hfun : (fun n : ℕ => w ^ n * scalarTaylorConvolution a b n) =
      fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (w ^ k * a k) * (w ^ (n - k) * b (n - k)) := by
    funext n
    simp only [scalarTaylorConvolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hpow : w ^ k * w ^ (n - k) = w ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    rw [← hpow]
    ring
  rw [hfun]
  exact hh

def quadraticTaylorCoeff (c : ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n % 2 = 0 then c ^ (n / 2) * a (n / 2) else 0

@[simp] theorem quadraticTaylorCoeff_even (c : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    quadraticTaylorCoeff c a (2 * n) = c ^ n * a n := by
  simp [quadraticTaylorCoeff]

@[simp] theorem quadraticTaylorCoeff_odd (c : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    quadraticTaylorCoeff c a (2 * n + 1) = 0 := by
  simp [quadraticTaylorCoeff, Nat.add_mod, Nat.mul_mod]

/-- Quadratic substitution into an actual convergent series, established by
the even/odd partition of its terms. -/
theorem scalar_powerSeries_comp_quadratic {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0) (c : ℂ) :
    HasFPowerSeriesAt (fun z : ℂ => f (c * z ^ 2))
      (FormalMultilinearSeries.ofScalars ℂ (quadraticTaylorCoeff c a)) 0 := by
  rw [hasFPowerSeriesAt_iff] at hf ⊢
  have hct : Tendsto (fun z : ℂ => c * z ^ 2) (𝓝 0) (𝓝 0) := by
    have hh : Tendsto (fun z : ℂ => c * z ^ 2) (𝓝 0) (𝓝 (c * (0 : ℂ) ^ 2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto
    simpa only [zero_pow two_ne_zero, mul_zero] using hh
  filter_upwards [hct.eventually hf] with z hz
  simp only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul] at hz ⊢
  have heven : HasSum (fun n : ℕ => z ^ (2 * n) * quadraticTaylorCoeff c a (2 * n))
      (f (c * z ^ 2)) := by
    convert! hz using 1
    funext n
    rw [quadraticTaylorCoeff_even, mul_pow, pow_mul]
    ring
  have hodd : HasSum (fun n : ℕ => z ^ (2 * n + 1) * quadraticTaylorCoeff c a (2 * n + 1))
      (0 : ℂ) := by
    simp only [quadraticTaylorCoeff_odd, mul_zero]
    exact hasSum_zero
  have hh : HasSum (fun n : ℕ => z ^ n * quadraticTaylorCoeff c a n)
      (f (c * z ^ 2) + 0) := HasSum.even_add_odd heven hodd
  simpa only [add_zero] using hh

def besselPoleNumerator (t z : ℂ) : ℂ := J0 (t * z) / Q (-z ^ 2 / 4)

def besselPoleNumeratorCoeff (t : ℂ) : ℕ → ℂ :=
  quadraticTaylorCoeff (-1 / 4)
    (scalarTaylorConvolution (fun n => (t ^ 2) ^ n / (n.factorial : ℂ) ^ 2) inverseQCoeff)

theorem besselPoleNumerator_hasFPowerSeriesAt (t : ℂ) :
    HasFPowerSeriesAt (besselPoleNumerator t)
      (FormalMultilinearSeries.ofScalars ℂ (besselPoleNumeratorCoeff t)) 0 := by
  have hh := scalar_powerSeries_comp_quadratic
    (scalar_powerSeries_mul (scaledF_hasFPowerSeriesAt (t ^ 2)) inverseQ_hasFPowerSeriesAt)
    (-1 / 4 : ℂ)
  have hfun : (fun z : ℂ => F (t ^ 2 * ((-1 / 4) * z ^ 2)) *
      (Q ((-1 / 4) * z ^ 2))⁻¹) = besselPoleNumerator t := by
    funext z
    have h₁ : t ^ 2 * ((-1 / 4) * z ^ 2) = -(t * z) ^ 2 / 4 := by ring
    have h₂ : (-1 / 4 : ℂ) * z ^ 2 = -z ^ 2 / 4 := by ring
    change F (t ^ 2 * ((-1 / 4) * z ^ 2)) * (Q ((-1 / 4) * z ^ 2))⁻¹ =
      F (-(t * z) ^ 2 / 4) / Q (-z ^ 2 / 4)
    rw [h₁, h₂] <;> rfl
  change HasFPowerSeriesAt (fun z : ℂ => F (t ^ 2 * ((-1 / 4) * z ^ 2)) *
    (Q ((-1 / 4) * z ^ 2))⁻¹) _ 0 at hh
  rw [hfun] at hh
  exact hh

/-- This polynomial is exactly the origin residue of
J₀(tz)/(z^(2M+1)(J₀(z)-1)). -/
def besselPolePolynomial (M : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (M + 2),
    monomial (2 * k)
      ((-4 : ℂ) * (-1 / 4 : ℂ) ^ (M + 1) * inverseQCoeff (M + 1 - k) /
        (k.factorial : ℂ) ^ 2)

theorem besselPolePolynomial_eval (M : ℕ) (t : ℂ) :
    (besselPolePolynomial M).eval t =
      -4 * iteratedDSlope (besselPoleNumerator t) 0 (2 * (M + 1)) 0 := by
  rw [iteratedDSlope_eq_powerSeries_coeff (besselPoleNumerator_hasFPowerSeriesAt t),
    FormalMultilinearSeries.coeff_ofScalars]
  simp only [besselPoleNumeratorCoeff, quadraticTaylorCoeff_even, scalarTaylorConvolution,
    besselPolePolynomial, eval_finset_sum, eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr (by congr 1 <;> omega)
  intro k hk
  rw [pow_mul]
  ring

theorem besselPolePolynomial_highest_coeff (M : ℕ) :
    (besselPolePolynomial M).coeff (2 * (M + 1)) =
      (-4 : ℂ) * (-1 / 4 : ℂ) ^ (M + 1) / ((M + 1).factorial : ℂ) ^ 2 := by
  unfold besselPolePolynomial
  rw [finset_sum_coeff, Finset.sum_eq_single (M + 1)]
  · simp only [coeff_monomial, ite_true, Nat.sub_self, inverseQCoeff_zero, mul_one]
  · intro k hk hkne
    have hne : 2 * (M + 1) ≠ 2 * k := by omega
    simp only [coeff_monomial, if_neg hne.symm]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

theorem besselPolePolynomial_highest_coeff_ne_zero (M : ℕ) :
    (besselPolePolynomial M).coeff (2 * (M + 1)) ≠ 0 := by
  rw [besselPolePolynomial_highest_coeff]
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  · exact pow_ne_zero _ (by exact_mod_cast (M + 1).factorial_ne_zero)

/-- The origin residue is an actual nonconstant even polynomial. -/
theorem besselPolePolynomial_ne_constant (M : ℕ) (c : ℂ) : besselPolePolynomial M ≠ C c := by
  intro heq
  have hh := congrArg (fun P : ℂ[X] => P.coeff (2 * (M + 1))) heq
  have hn : 2 * (M + 1) ≠ 0 := by omega
  simp only [coeff_C, if_neg hn] at hh
  exact besselPolePolynomial_highest_coeff_ne_zero M hh

end J0RadialUniqueness
