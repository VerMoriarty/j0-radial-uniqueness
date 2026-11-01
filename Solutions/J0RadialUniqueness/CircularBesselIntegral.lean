import Solutions.J0RadialUniqueness.Series
import Definitions.J0RadialUniqueness.TwoRadius
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! The complex-parameter circular Bessel integral, proved from the exponential
series and the elementary cosine moments.  The exchange of sum and integral uses
an explicit summable majorant `‖w‖^n / n!` on the entire integration interval.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace J0RadialUniqueness

/-- The full-period even cosine moment, with its exact factorial normalization. -/
theorem integral_cos_pow_even_full (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos t ^ (2 * n)) =
      2 * Real.pi * ((2 * n).factorial : ℝ) /
        (4 ^ n * (n.factorial : ℝ) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hindex : 2 * (n + 1) = 2 * n + 2 := by omega
    have hfac : ((2 * n + 2).factorial : ℝ) =
        (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * ((2 * n).factorial : ℝ) := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    rw [hindex, integral_cos_pow (2 * n)]
    simp only [Real.sin_two_pi, Real.sin_zero, mul_zero, sub_self, zero_div, zero_add]
    rw [ih, hfac, Nat.factorial_succ]
    simp only [pow_succ]
    push_cast
    field_simp [hnf, hn1, hn2]
    <;> ring

/-- All full-period odd cosine moments vanish. -/
theorem integral_cos_pow_odd_full (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos t ^ (2 * n + 1)) = 0 := by
  simpa only [pow_zero, one_mul, Real.sin_zero, Real.sin_two_pi,
    intervalIntegral.integral_same] using
    (integral_sin_pow_mul_cos_pow_odd (a := 0) (b := 2 * Real.pi) 0 n)

/-- The n-th term in the exponential series inside the circular integral. -/
def circularExpSeriesTerm (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (w * (Real.cos t : ℂ)) ^ n / (n.factorial : ℂ)

theorem integral_circularExpSeriesTerm (w : ℂ) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w n t) =
      (w ^ n / (n.factorial : ℂ)) *
        ((∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos t ^ n : ℝ) : ℂ) := by
  calc
    _ = ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
        (w ^ n / (n.factorial : ℂ)) * ((Real.cos t ^ n : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [circularExpSeriesTerm, Complex.ofReal_pow, mul_pow]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

theorem integral_circularExpSeriesTerm_even (w : ℂ) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w (2 * n) t) =
      ((2 * Real.pi : ℝ) : ℂ) * fTerm (w ^ 2 / 4) n := by
  have hfac : ((2 * n).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [integral_circularExpSeriesTerm, integral_cos_pow_even_full]
  unfold fTerm
  push_cast
  simp only [div_pow, pow_mul]
  field_simp [hfac, hnf]
  <;> ring

theorem integral_circularExpSeriesTerm_odd (w : ℂ) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w (2 * n + 1) t) = 0 := by
  rw [integral_circularExpSeriesTerm, integral_cos_pow_odd_full]
  simp

/-- The exponential series is dominated by a constant-in-angle summable sequence. -/
theorem norm_circularExpSeriesTerm_le (w : ℂ) (n : ℕ) (t : ℝ) :
    ‖circularExpSeriesTerm w n t‖ ≤ ‖w‖ ^ n / (n.factorial : ℝ) := by
  have hbase : ‖w * (Real.cos t : ℂ)‖ ≤ ‖w‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg w) (Real.abs_cos_le_one t)
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hbase n
  simpa only [circularExpSeriesTerm, norm_div, norm_pow, Complex.norm_natCast] using
    (div_le_div_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ n.factorial))

/-- Integrating the exponential series is justified by dominated convergence. -/
theorem hasSum_integral_circularExpSeriesTerm (w : ℂ) :
    HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w n t)
      (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), Complex.exp (w * (Real.cos t : ℂ))) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => ‖w‖ ^ n / (n.factorial : ℝ))
  · intro n
    have hc : Continuous (circularExpSeriesTerm w n) := by
      unfold circularExpSeriesTerm
      fun_prop
    exact hc.aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun t ht => norm_circularExpSeriesTerm_le w n t
  · exact Filter.Eventually.of_forall fun t ht => Real.summable_pow_div_factorial ‖w‖
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have h := NormedSpace.expSeries_div_hasSum_exp (w * (Real.cos t : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at h
    exact h

/-- The complex-parameter circular Bessel integral, with exact factor `2π`. -/
theorem integral_exp_mul_cos (w : ℂ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), Complex.exp (w * (Real.cos t : ℂ))) =
      ((2 * Real.pi : ℝ) : ℂ) * F (w ^ 2 / 4) := by
  have he : HasSum
      (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w (2 * n) t)
      (((2 * Real.pi : ℝ) : ℂ) * F (w ^ 2 / 4)) := by
    have hfun :
        (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w (2 * n) t) =
          fun n : ℕ => ((2 * Real.pi : ℝ) : ℂ) * fTerm (w ^ 2 / 4) n := by
      funext n
      exact integral_circularExpSeriesTerm_even w n
    rw [hfun]
    convert! (fTerm_summable (w ^ 2 / 4)).hasSum.mul_left
      ((2 * Real.pi : ℝ) : ℂ) using 1 <;> rfl
  have ho : HasSum
      (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w (2 * n + 1) t)
      (0 : ℂ) := by
    simp only [integral_circularExpSeriesTerm_odd]
    exact hasSum_zero
  have hs := HasSum.even_add_odd
    (f := fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w n t) he ho
  have hs' : HasSum
      (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circularExpSeriesTerm w n t)
      (((2 * Real.pi : ℝ) : ℂ) * F (w ^ 2 / 4)) := by
    simpa only [add_zero] using hs
  exact (hasSum_integral_circularExpSeriesTerm w).unique hs'

/-- Translating the series normalization to the paper's actual `J0`. -/
theorem J0_I_mul_eq_F (w : ℂ) : J0 (Complex.I * w) = F (w ^ 2 / 4) := by
  unfold J0
  congr 1
  rw [mul_pow, Complex.I_sq]
  ring

theorem integral_exp_mul_cos_eq_J0 (w : ℂ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), Complex.exp (w * (Real.cos t : ℂ))) =
      ((2 * Real.pi : ℝ) : ℂ) * J0 (Complex.I * w) := by
  rw [J0_I_mul_eq_F, integral_exp_mul_cos]

/-- Pointwise factorization along the actual plane circle from `TwoRadius`. -/
theorem spectralExponential_circle_factor (lam : ℂ) (r : ℝ) (x : Plane) (t : ℝ) :
    spectralExponential lam (x + r • circleDirection t) =
      spectralExponential lam x * Complex.exp ((lam * (r : ℂ)) * (Real.cos t : ℂ)) := by
  unfold spectralExponential
  rw [← Complex.exp_add]
  congr 1
  simp only [PiLp.add_apply, PiLp.smul_apply, circleDirection, PiLp.toLp_apply,
    Matrix.cons_val_zero, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- The exact complex spherical-mean multiplier for the explicit plane exponential. -/
theorem circularMean_spectralExponential (lam : ℂ) (r : ℝ) (x : Plane) :
    circularMean (spectralExponential lam) r x =
      spectralExponential lam x * J0 (Complex.I * lam * (r : ℂ)) := by
  have hfun :
      (fun t : ℝ => spectralExponential lam (x + r • circleDirection t)) =
        fun t : ℝ => spectralExponential lam x *
          Complex.exp ((lam * (r : ℂ)) * (Real.cos t : ℂ)) := by
    funext t
    exact spectralExponential_circle_factor lam r x t
  unfold circularMean
  rw [hfun, intervalIntegral.integral_const_mul, integral_exp_mul_cos_eq_J0]
  rw [Complex.real_smul]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [mul_assoc]
  field_simp [hpi]
  <;> ring

end J0RadialUniqueness
