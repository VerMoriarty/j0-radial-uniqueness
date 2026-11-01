import Solutions.J0RadialUniqueness.FAnalytic

/-! Entire analyticity of the actual shifted-factorial series Q. -/

noncomputable section

namespace J0RadialUniqueness

def QPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => 1 / ((n + 1).factorial : ℂ) ^ 2)

theorem QPowerSeries_radius : QPowerSeries.radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  convert (qTerm_summable (((r : ℝ) : ℂ))).norm using 1
  ext n
  simp [QPowerSeries, FormalMultilinearSeries.ofScalars_norm,
    norm_div, norm_pow, Complex.norm_natCast,
    Complex.norm_of_nonneg r.coe_nonneg, div_eq_mul_inv, mul_comm]

theorem Q_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall Q QPowerSeries 0 ⊤ where
  r_le := by rw [QPowerSeries_radius]
  r_pos := by simp
  hasSum {y} _ := by
    have hfun : (fun n : ℕ => QPowerSeries n (fun _ => y)) =
        (fun n : ℕ => y ^ n / ((n + 1).factorial : ℂ) ^ 2) := by
      funext n
      simp [QPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq,
        div_eq_mul_inv, mul_comm]
    rw [hfun, zero_add]
    exact (qTerm_summable y).hasSum

theorem Q_analyticAt (w : ℂ) : AnalyticAt ℂ Q w :=
  Q_hasFPowerSeriesOnBall.analyticAt_of_mem (by simp)

theorem Q_analyticOnNhd : AnalyticOnNhd ℂ Q Set.univ := fun w _ => Q_analyticAt w

theorem Q_differentiable : Differentiable ℂ Q :=
  fun w => (Q_analyticAt w).differentiableAt

theorem Q_continuous : Continuous Q := Q_differentiable.continuous

end J0RadialUniqueness
