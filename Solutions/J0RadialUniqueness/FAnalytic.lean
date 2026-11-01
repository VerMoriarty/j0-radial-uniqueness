import Definitions.J0RadialUniqueness.Analytic
import Solutions.J0RadialUniqueness.Series
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-!
The actual factorial series `F` is entire.  Its formal power series has
infinite radius by comparison with the exponential series.  These are
unconditional results about the definitions in the paper.
-/

noncomputable section

namespace J0RadialUniqueness

/-- The scalar power series of the paper's function F, centered at zero. -/
def FPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => 1 / (n.factorial : ℂ) ^ 2)

/-- The exponential-series majorant gives an infinite convergence radius. -/
theorem FPowerSeries_radius : FPowerSeries.radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  convert (fTerm_summable (((r : ℝ) : ℂ))).norm using 1
  ext n
  simp [FPowerSeries, FormalMultilinearSeries.ofScalars_norm, fTerm,
    norm_div, norm_pow, Complex.norm_natCast,
    Complex.norm_of_nonneg r.coe_nonneg, div_eq_mul_inv, mul_comm]

/-- The defining series of F is its power series throughout the complex plane. -/
theorem F_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall F FPowerSeries 0 ⊤ where
  r_le := by rw [FPowerSeries_radius]
  r_pos := by simp
  hasSum {y} _ := by
    have hfun : (fun n : ℕ => FPowerSeries n (fun _ => y)) = fTerm y := by
      funext n
      simp [FPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq, fTerm,
        div_eq_mul_inv, mul_comm]
    rw [hfun, zero_add]
    exact (fTerm_summable y).hasSum

/-- F is analytic at every complex point. -/
theorem F_analyticAt (w : ℂ) : AnalyticAt ℂ F w :=
  F_hasFPowerSeriesOnBall.analyticAt_of_mem (by simp)

theorem F_analyticOnNhd : AnalyticOnNhd ℂ F Set.univ :=
  fun w _ => F_analyticAt w

theorem F_differentiable : Differentiable ℂ F :=
  fun w => (F_analyticAt w).differentiableAt

/-- Derivatives of this entire scalar series are again entire. -/
theorem F_deriv_analyticOnNhd : AnalyticOnNhd ℂ (deriv F) Set.univ :=
  F_analyticOnNhd.deriv

theorem F_deriv_differentiable : Differentiable ℂ (deriv F) :=
  fun w => (F_deriv_analyticOnNhd w (Set.mem_univ w)).differentiableAt

/-- The first power-series coefficient is one, including at the singular ODE point. -/
theorem deriv_F_zero : deriv F 0 = 1 := by
  simpa [FPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq] using
    F_hasFPowerSeriesOnBall.hasFPowerSeriesAt.deriv

end J0RadialUniqueness
