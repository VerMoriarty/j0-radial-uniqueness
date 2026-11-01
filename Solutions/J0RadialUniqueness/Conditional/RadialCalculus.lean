import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Real-variable calculus used by the radial escape argument.
The function and its derivative are explicit parameters. In particular,
no claim that the actual Bessel function satisfies these hypotheses is assumed globally. -/

noncomputable section

namespace J0RadialUniqueness

/-- A radial logarithmic derivative bound integrates to a strict logarithmic lower bound.
The proof uses the mean-value monotonicity theorem and does not require an additional
continuity assumption on the derivative. -/
theorem logarithmic_growth_of_radial_derivative
    (l d : ℝ → ℝ) (k : ℝ) (hstart : l 1 = 0)
    (hderiv : ∀ t : ℝ, 1 ≤ t → HasDerivAt l (d t) t)
    (hbound : ∀ t : ℝ, 1 ≤ t → k < t * d t)
    {c : ℝ} (hc : 1 < c) : k * Real.log c < l c := by
  let g : ℝ → ℝ := fun t => l t - k * Real.log t
  have hgderiv (t : ℝ) (ht : 1 ≤ t) :
      HasDerivAt g (d t - k * t⁻¹) t := by
    have htpos : 0 < t := by linarith
    exact (hderiv t ht).sub ((Real.hasDerivAt_log htpos.ne').const_mul k)
  have hgpos (t : ℝ) (ht : 1 ≤ t) : 0 < d t - k * t⁻¹ := by
    have htpos : 0 < t := by linarith
    have hdiv : k / t < d t := (div_lt_iff₀ htpos).mpr (by
      simpa only [mul_comm] using hbound t ht)
    simpa only [div_eq_mul_inv] using sub_pos.mpr hdiv
  have hmono : StrictMonoOn g (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro t ht
      exact (hgderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 1 ≤ t := interior_subset ht
      rw [(hgderiv t ht').deriv]
      exact hgpos t ht'
  have hgc : g 1 < g c := hmono (by simp) hc.le hc
  dsimp [g] at hgc
  rw [hstart, Real.log_one] at hgc
  linarith

/-- The exponent used in Proposition 5.1. This remains a generic calculus statement. -/
theorem logarithmic_growth_seven_twentyfifths
    (l d : ℝ → ℝ) (hstart : l 1 = 0)
    (hderiv : ∀ t : ℝ, 1 ≤ t → HasDerivAt l (d t) t)
    (hbound : ∀ t : ℝ, 1 ≤ t → (7 / 25 : ℝ) < t * d t)
    {c : ℝ} (hc : 1 < c) : (7 / 25 : ℝ) * Real.log c < l c :=
  logarithmic_growth_of_radial_derivative l d (7 / 25) hstart hderiv hbound hc

/-- Once the imaginary coordinate is at least one half, the polynomial prefactor cannot
outgrow the exponential decay along the outward ray. -/
theorem outward_exponential_factor_le_one
    {τ y : ℝ} (hτ : 1 ≤ τ) (hy : (1 / 2 : ℝ) ≤ y) :
    τ * Real.exp (-2 * (τ - 1) * y) ≤ 1 := by
  have hτpos : 0 < τ := by linarith
  have hlog : Real.log τ ≤ τ - 1 := Real.log_le_sub_one_of_pos hτpos
  have hprod : 0 ≤ (τ - 1) * (2 * y - 1) :=
    mul_nonneg (sub_nonneg.mpr hτ) (by linarith)
  calc
    τ * Real.exp (-2 * (τ - 1) * y) =
        Real.exp (Real.log τ + (-2 * (τ - 1) * y)) := by
      rw [Real.exp_add, Real.exp_log hτpos]
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)

/-- The exact initial-separation hypothesis in the paper implies the outward factor bound. -/
theorem outward_exponential_factor_le_one_of_separation
    {τ y : ℝ} (hτ : 1 ≤ τ) (hy : (7 / 5 : ℝ) < y) :
    τ * Real.exp (-2 * (τ - 1) * y) ≤ 1 :=
  outward_exponential_factor_le_one hτ (by linarith)

/-- Propagation of the small quantity `rho * exp (-2*y)` along an outward ray.
The arbitrary upper bound permits direct use with the paper's `11/50`. -/
theorem outward_rho_exp_bound
    {τ ρ y B : ℝ} (hτ : 1 ≤ τ) (hρ : 0 ≤ ρ)
    (hy : (1 / 2 : ℝ) ≤ y) (hbound : ρ * Real.exp (-2 * y) < B) :
    (τ * ρ) * Real.exp (-2 * (τ * y)) < B := by
  have hfactor := outward_exponential_factor_le_one hτ hy
  have hbase : 0 ≤ ρ * Real.exp (-2 * y) :=
    mul_nonneg hρ (Real.exp_pos _).le
  have hscale : (τ * ρ) * Real.exp (-2 * (τ * y)) =
      (ρ * Real.exp (-2 * y)) * (τ * Real.exp (-2 * (τ - 1) * y)) := by
    have he : -2 * (τ * y) = -2 * y + -2 * (τ - 1) * y := by ring
    rw [he, Real.exp_add]
    ring
  rw [hscale]
  calc
    (ρ * Real.exp (-2 * y)) * (τ * Real.exp (-2 * (τ - 1) * y)) ≤
        (ρ * Real.exp (-2 * y)) * 1 := mul_le_mul_of_nonneg_left hfactor hbase
    _ = ρ * Real.exp (-2 * y) := mul_one _
    _ < B := hbound

/-- The propagated `11/50` estimate with exactly the paper's initial hypotheses. -/
theorem outward_rho_exp_eleven_fiftieths
    {τ ρ y : ℝ} (hτ : 1 ≤ τ) (hρ : 0 ≤ ρ)
    (hy : (7 / 5 : ℝ) < y) (hbound : ρ * Real.exp (-2 * y) < (11 / 50 : ℝ)) :
    (τ * ρ) * Real.exp (-2 * (τ * y)) < (11 / 50 : ℝ) :=
  outward_rho_exp_bound hτ hρ (by linarith) hbound

/-- Pure exponential decay also persists along the outward ray. -/
theorem outward_exp_bound
    {τ y B : ℝ} (hτ : 1 ≤ τ) (hy : 0 ≤ y)
    (hbound : Real.exp (-2 * y) < B) : Real.exp (-2 * (τ * y)) < B := by
  have hprod : 0 ≤ (τ - 1) * y := mul_nonneg (sub_nonneg.mpr hτ) hy
  exact lt_of_le_of_lt (Real.exp_le_exp.mpr (by nlinarith)) hbound

end J0RadialUniqueness
