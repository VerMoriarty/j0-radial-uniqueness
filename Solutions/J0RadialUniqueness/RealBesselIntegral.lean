import Solutions.J0RadialUniqueness.CircularBesselIntegral
import Definitions.J0RadialUniqueness.Analytic
import Mathlib.Tactic

/-! The real Bessel integral on the source's half-circle interval. Reflection
of the actual continuous integrand identifies the two half-circle integrals,
so this adapter follows from the proved complex full-circle series formula.
Every real parameter, including zero, is retained. -/

noncomputable section

open MeasureTheory
open scoped Interval Topology

namespace J0RadialUniqueness

theorem integral_exp_mul_cos_half (w : ℂ) :
    (∫ t : ℝ in (0 : ℝ)..Real.pi, Complex.exp (w * (Real.cos t : ℂ))) =
      (Real.pi : ℂ) * J0 (Complex.I * w) := by
  let f : ℝ → ℂ := fun t => Complex.exp (w * (Real.cos t : ℂ))
  have hf : Continuous f := by unfold f; fun_prop
  have hfirst : IntervalIntegrable f volume (0 : ℝ) Real.pi := hf.intervalIntegrable _ _
  have hsecond : IntervalIntegrable f volume Real.pi (2 * Real.pi) := hf.intervalIntegrable _ _
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := Real.pi) f (2 * Real.pi)
  rw [show 2 * Real.pi - Real.pi = Real.pi by ring, sub_zero] at hreflect
  have hsame : (∫ t : ℝ in (0 : ℝ)..Real.pi, f (2 * Real.pi - t)) =
      ∫ t : ℝ in (0 : ℝ)..Real.pi, f t := by
    apply intervalIntegral.integral_congr
    intro t _
    change Complex.exp (w * (Real.cos (2 * Real.pi - t) : ℂ)) =
      Complex.exp (w * (Real.cos t : ℂ))
    rw [Real.cos_two_pi_sub]
  have hdouble : (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), f t) =
      (2 : ℂ) * ∫ t : ℝ in (0 : ℝ)..Real.pi, f t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hsecond,
      ← hreflect, hsame]
    ring
  have hfull := integral_exp_mul_cos_eq_J0 w
  change (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), f t) =
    ((2 * Real.pi : ℝ) : ℂ) * J0 (Complex.I * w) at hfull
  rw [hdouble] at hfull
  push_cast at hfull
  change (∫ t : ℝ in (0 : ℝ)..Real.pi, f t) = _
  linear_combination (1 / 2 : ℂ) * hfull

/-- The exact cited real-parameter half-circle formula, with actual
integrability and no restriction excluding the zero parameter. -/
theorem real_bessel_integral : RealBesselIntegralStatement := by
  intro x
  have hf : Continuous (fun t : ℝ =>
      Complex.exp (Complex.I * (x : ℂ) * (Real.cos t : ℂ))) := by fun_prop
  refine ⟨hf.intervalIntegrable _ _, ?_⟩
  have hh := integral_exp_mul_cos_half (Complex.I * (x : ℂ))
  have hJ : J0 (Complex.I * (Complex.I * (x : ℂ))) = J0 (x : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, J0_neg]
  rw [hJ] at hh
  rw [hh]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]

end J0RadialUniqueness
