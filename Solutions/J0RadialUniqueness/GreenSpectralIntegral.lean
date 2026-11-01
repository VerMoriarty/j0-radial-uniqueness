import Solutions.J0RadialUniqueness.FAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Exact spectral integral of the compact radial logarithmic Green kernel.

The endpoint `t = 0` is handled by the actual total real logarithm: the factor
`t * log (r/t)` extends continuously there.  A continuous primitive computes
all its monomial moments, and a summable majorant justifies integration of the
actual factorial series defining J0. No spectral synthesis theorem is assumed.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace J0RadialUniqueness

def greenRadialWeight (r t : ℝ) : ℝ := t * Real.log (r / t)

def greenRadialMonomial (r : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * n) * greenRadialWeight r t

def greenRadialPrimitive (r : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * n + 1) * greenRadialWeight r t / (2 * (n : ℝ) + 2) +
    t ^ (2 * n + 2) / (2 * (n : ℝ) + 2) ^ 2

theorem greenRadialWeight_eq {r : ℝ} (hr : 0 < r) (t : ℝ) :
    greenRadialWeight r t = t * Real.log r - t * Real.log t := by
  by_cases ht : t = 0
  · simp [greenRadialWeight, ht]
  · rw [greenRadialWeight, Real.log_div hr.ne' ht, mul_sub]

/-- The apparent logarithmic singularity has a continuous zero endpoint. -/
theorem continuous_greenRadialWeight {r : ℝ} (hr : 0 < r) :
    Continuous (greenRadialWeight r) := by
  have heq : greenRadialWeight r = fun t : ℝ => t * Real.log r - t * Real.log t :=
    funext (greenRadialWeight_eq hr)
  rw [heq]
  exact (continuous_id.mul continuous_const).sub Real.continuous_mul_log

theorem greenRadialWeight_nonneg {r t : ℝ} (ht : 0 < t) (htr : t ≤ r) :
    0 ≤ greenRadialWeight r t := by
  unfold greenRadialWeight
  apply mul_nonneg ht.le
  apply Real.log_nonneg
  exact (one_le_div ht).mpr htr

theorem greenRadialWeight_hasDerivAt {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    HasDerivAt (greenRadialWeight r) (Real.log (r / t) - 1) t := by
  have heq : greenRadialWeight r = fun u : ℝ => u * Real.log r - u * Real.log u :=
    funext (greenRadialWeight_eq hr)
  rw [heq]
  have h := ((hasDerivAt_id t).mul_const (Real.log r)).sub
    (Real.hasDerivAt_mul_log ht.ne')
  apply h.congr_deriv
  rw [Real.log_div hr.ne' ht.ne']
  simp only [one_mul]
  ring

theorem continuous_greenRadialMonomial {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Continuous (greenRadialMonomial r n) :=
  (continuous_id.pow (2 * n)).mul (continuous_greenRadialWeight hr)

theorem intervalIntegrable_greenRadialMonomial {r : ℝ} (hr : 0 < r) (n : ℕ) :
    IntervalIntegrable (greenRadialMonomial r n) volume 0 r :=
  (continuous_greenRadialMonomial hr n).intervalIntegrable 0 r

theorem continuous_greenRadialPrimitive {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Continuous (greenRadialPrimitive r n) := by
  unfold greenRadialPrimitive
  exact (((continuous_id.pow (2 * n + 1)).mul
    (continuous_greenRadialWeight hr)).div_const _).add
      ((continuous_id.pow (2 * n + 2)).div_const _)

theorem greenRadialPrimitive_hasDerivAt {r t : ℝ} (hr : 0 < r)
    (n : ℕ) (ht : 0 < t) :
    HasDerivAt (greenRadialPrimitive r n) (greenRadialMonomial r n t) t := by
  have hden : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  have h := ((((hasDerivAt_id t).pow (2 * n + 1)).mul
    (greenRadialWeight_hasDerivAt hr ht)).div_const (2 * (n : ℝ) + 2)).add
      (((hasDerivAt_id t).pow (2 * n + 2)).div_const ((2 * (n : ℝ) + 2) ^ 2))
  apply h.congr_deriv
  have he1 : 2 * n + 1 - 1 = 2 * n := by omega
  have he2 : 2 * n + 2 - 1 = 2 * n + 1 := by omega
  simp only [he1, he2, Pi.pow_apply, Pi.mul_apply, id_eq,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_one]
  unfold greenRadialMonomial greenRadialWeight
  simp only [pow_succ, Pi.pow_apply, Pi.mul_apply, id_eq]
  field_simp [hden]
  <;> ring

/-- Exact logarithmic monomial moment, with convergence at zero included. -/
theorem integral_greenRadialMonomial {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..r, greenRadialMonomial r n t) =
      r ^ (2 * n + 2) / (2 * (n : ℝ) + 2) ^ 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.le
    (continuous_greenRadialPrimitive hr n).continuousOn
    (fun t ht => greenRadialPrimitive_hasDerivAt hr n ht.1)
    (intervalIntegrable_greenRadialMonomial hr n)
  simpa [greenRadialPrimitive, greenRadialWeight, hr.ne',
    show 2 * n + 1 ≠ 0 by omega, show 2 * n + 2 ≠ 0 by omega] using h

theorem intervalIntegrable_pow_mul_log_ratio {r : ℝ} (hr : 0 < r) (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ (2 * n + 1) * Real.log (r / t)) volume 0 r := by
  convert! intervalIntegrable_greenRadialMonomial hr n using 1
  funext t
  simp only [greenRadialMonomial, greenRadialWeight, pow_succ]
  ring

theorem integral_pow_mul_log_ratio {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..r, t ^ (2 * n + 1) * Real.log (r / t)) =
      r ^ (2 * n + 2) / (2 * (n : ℝ) + 2) ^ 2 := by
  convert! integral_greenRadialMonomial hr n using 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [greenRadialMonomial, greenRadialWeight, pow_succ]
  ring

theorem integral_unit_pow_mul_neg_log (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..1, t ^ (2 * n + 1) * (-Real.log t)) =
      1 / (2 * (n : ℝ) + 2) ^ 2 := by
  simpa only [one_div, Real.log_inv, one_pow] using
    integral_pow_mul_log_ratio (by norm_num : (0 : ℝ) < 1) n

def greenBesselTerm (r : ℝ) (ζ : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  greenRadialWeight r t • fTerm (-((t : ℂ) * ζ) ^ 2 / 4) n

theorem greenBesselTerm_eq (r : ℝ) (ζ : ℂ) (n : ℕ) (t : ℝ) :
    greenBesselTerm r ζ n t = (greenRadialMonomial r n t : ℂ) * fTerm (-ζ ^ 2 / 4) n := by
  have harg : -((t : ℂ) * ζ) ^ 2 / 4 = (t : ℂ) ^ 2 * (-ζ ^ 2 / 4) := by ring
  simp only [greenBesselTerm, greenRadialMonomial, Complex.ofReal_mul, Complex.ofReal_pow,
    fTerm, harg, mul_pow, ← pow_mul, Complex.real_smul]
  ring

theorem continuous_greenBesselTerm {r : ℝ} (hr : 0 < r) (ζ : ℂ) (n : ℕ) :
    Continuous (greenBesselTerm r ζ n) := by
  have heq : greenBesselTerm r ζ n =
      fun t : ℝ => (greenRadialMonomial r n t : ℂ) * fTerm (-ζ ^ 2 / 4) n :=
    funext (greenBesselTerm_eq r ζ n)
  rw [heq]
  exact (Complex.continuous_ofReal.comp (continuous_greenRadialMonomial hr n)).mul continuous_const

theorem norm_greenBesselTerm_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (htr : t ≤ r)
    (ζ : ℂ) (n : ℕ) :
    ‖greenBesselTerm r ζ n t‖ ≤
      greenRadialWeight r t * ‖fTerm (-((r : ℂ) * ζ) ^ 2 / 4) n‖ := by
  have hbase : ‖-((t : ℂ) * ζ) ^ 2 / 4‖ ≤ ‖-((r : ℂ) * ζ) ^ 2 / 4‖ := by
    simp only [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hr]
    gcongr
  have hterm : ‖fTerm (-((t : ℂ) * ζ) ^ 2 / 4) n‖ ≤
      ‖fTerm (-((r : ℂ) * ζ) ^ 2 / 4) n‖ := by
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hbase n
    simp only [norm_div] at hpow
    simp only [fTerm, norm_div, norm_pow]
    exact div_le_div_of_nonneg_right hpow (sq_nonneg ‖(n.factorial : ℂ)‖)
  rw [greenBesselTerm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (greenRadialWeight_nonneg ht htr)]
  exact mul_le_mul_of_nonneg_left hterm (greenRadialWeight_nonneg ht htr)

/-- The summable bound proves the interchange for the actual J0 factorial series. -/
theorem hasSum_integral_greenBesselTerm {r : ℝ} (hr : 0 < r) (ζ : ℂ) :
    HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..r, greenBesselTerm r ζ n t)
      (∫ t : ℝ in (0 : ℝ)..r, greenRadialWeight r t • J0 ((t : ℂ) * ζ)) := by
  let w : ℂ := -((r : ℂ) * ζ) ^ 2 / 4
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n t => greenRadialWeight r t * ‖fTerm w n‖)
  · intro n
    exact (continuous_greenBesselTerm hr ζ n).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hr.le] at ht
    exact norm_greenBesselTerm_le hr ht.1 ht.2 ζ n
  · exact Filter.Eventually.of_forall fun t _ => ((fTerm_summable w).norm).mul_left _
  · simpa only [tsum_mul_left] using
      (continuous_greenRadialWeight hr).intervalIntegrable (0 : ℝ) r |>.mul_const
        (∑' n : ℕ, ‖fTerm w n‖)
  · refine Filter.Eventually.of_forall fun t _ => ?_
    simpa only [greenBesselTerm, J0, F] using
      (fTerm_summable (-((t : ℂ) * ζ) ^ 2 / 4)).hasSum.const_smul (greenRadialWeight r t)

theorem integral_greenBesselTerm {r : ℝ} (hr : 0 < r) (ζ : ℂ) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..r, greenBesselTerm r ζ n t) =
      ((r : ℂ) ^ 2 / 4) *
        ((-((r : ℂ) * ζ) ^ 2 / 4) ^ n / ((n + 1).factorial : ℂ) ^ 2) := by
  have heq : greenBesselTerm r ζ n =
      fun t : ℝ => (greenRadialMonomial r n t : ℂ) * fTerm (-ζ ^ 2 / 4) n :=
    funext (greenBesselTerm_eq r ζ n)
  rw [heq, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    integral_greenRadialMonomial hr n]
  have harg : -((r : ℂ) * ζ) ^ 2 / 4 = (r : ℂ) ^ 2 * (-ζ ^ 2 / 4) := by ring
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  have hden : 2 * (n : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show 2 * (n : ℝ) + 2 ≠ 0 by positivity)
  rw [harg, mul_pow, ← pow_mul, Nat.factorial_succ]
  unfold fTerm
  push_cast
  simp only [pow_add]
  field_simp [hfac, hn, hden]
  <;> ring

theorem intervalIntegrable_greenBessel {r : ℝ} (hr : 0 < r) (ζ : ℂ) :
    IntervalIntegrable (fun t : ℝ => (t * Real.log (r / t)) • J0 ((t : ℂ) * ζ)) volume 0 r := by
  have hJ : Continuous (fun t : ℝ => J0 ((t : ℂ) * ζ)) := by
    unfold J0
    exact F_differentiable.continuous.comp (by fun_prop)
  exact ((continuous_greenRadialWeight hr).smul hJ).intervalIntegrable 0 r

/-- Exact compact radial Green-kernel spectral function, including ζ = 0. -/
theorem integral_greenBessel_eq_Q {r : ℝ} (hr : 0 < r) (ζ : ℂ) :
    (∫ t : ℝ in (0 : ℝ)..r, (t * Real.log (r / t)) • J0 ((t : ℂ) * ζ)) =
      ((r : ℂ) ^ 2 / 4) * Q (-((r : ℂ) * ζ) ^ 2 / 4) := by
  have hsum := hasSum_integral_greenBesselTerm hr ζ
  have heq : (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..r, greenBesselTerm r ζ n t) =
      (fun n : ℕ => ((r : ℂ) ^ 2 / 4) *
        ((-((r : ℂ) * ζ) ^ 2 / 4) ^ n / ((n + 1).factorial : ℂ) ^ 2)) :=
    funext (integral_greenBesselTerm hr ζ)
  rw [heq] at hsum
  have hQ := (qTerm_summable (-((r : ℂ) * ζ) ^ 2 / 4)).hasSum.mul_left ((r : ℂ) ^ 2 / 4)
  exact hsum.unique hQ

end J0RadialUniqueness
