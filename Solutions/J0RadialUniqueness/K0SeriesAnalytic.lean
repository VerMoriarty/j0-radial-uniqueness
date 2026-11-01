import Solutions.J0RadialUniqueness.K0Connection
import Solutions.J0RadialUniqueness.FODE
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
The independently defined logarithmic K₀ series is analytic throughout the
slit plane. Its harmonic-number correction is an entire function.
-/

noncomputable section

namespace J0RadialUniqueness

def harmonicF (w : ℂ) : ℂ := ∑' n : ℕ, (harmonic n : ℂ) * fTerm w n

def harmonicFPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => (harmonic n : ℂ) / (n.factorial : ℂ) ^ 2)

theorem harmonic_fTerm_summable (w : ℂ) :
    Summable (fun n : ℕ => (harmonic n : ℂ) * fTerm w n) := by
  apply (Real.summable_pow_div_factorial ‖w‖).of_norm_bounded
  intro n
  have hbounds := harmonic_real_bounds n
  have hnf : (n : ℝ) ≤ n.factorial := by exact_mod_cast Nat.self_le_factorial n
  have hh : ‖(harmonic n : ℂ)‖ ≤ (n.factorial : ℝ) := by
    rw [Complex.norm_ratCast, abs_of_nonneg hbounds.1]
    exact hbounds.2.trans hnf
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    ‖(harmonic n : ℂ) * fTerm w n‖ =
        ‖(harmonic n : ℂ)‖ * (‖w‖ ^ n / (n.factorial : ℝ) ^ 2) := by
      simp [fTerm, norm_mul, norm_div, norm_pow]
    _ ≤ (n.factorial : ℝ) * (‖w‖ ^ n / (n.factorial : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = ‖w‖ ^ n / (n.factorial : ℝ) := by field_simp [hf] <;> ring

theorem harmonicFPowerSeries_radius : harmonicFPowerSeries.radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  convert (harmonic_fTerm_summable (((r : ℝ) : ℂ))).norm using 1
  ext n
  simp [harmonicFPowerSeries, FormalMultilinearSeries.ofScalars_norm, fTerm,
    norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_of_nonneg r.coe_nonneg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem harmonicF_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall harmonicF harmonicFPowerSeries 0 ⊤ where
  r_le := by rw [harmonicFPowerSeries_radius]
  r_pos := by simp
  hasSum {y} _ := by
    have hfun : (fun n : ℕ => harmonicFPowerSeries n (fun _ => y)) =
        (fun n : ℕ => (harmonic n : ℂ) * fTerm y n) := by
      funext n
      simp [harmonicFPowerSeries, FormalMultilinearSeries.ofScalars_apply_eq, fTerm,
        div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    rw [hfun, zero_add]
    exact (harmonic_fTerm_summable y).hasSum

theorem harmonicF_analyticAt (w : ℂ) : AnalyticAt ℂ harmonicF w :=
  harmonicF_hasFPowerSeriesOnBall.analyticAt_of_mem (by simp)

theorem harmonicF_analyticOnNhd : AnalyticOnNhd ℂ harmonicF Set.univ :=
  fun w _ => harmonicF_analyticAt w

theorem harmonicF_differentiable : Differentiable ℂ harmonicF :=
  fun w => (harmonicF_analyticAt w).differentiableAt

theorem harmonicF_deriv_differentiable : Differentiable ℂ (deriv harmonicF) :=
  fun w => (harmonicF_analyticOnNhd.deriv w (Set.mem_univ w)).differentiableAt

@[simp] theorem harmonicF_zero : harmonicF 0 = 0 := by
  unfold harmonicF
  have hfun : (fun n : ℕ => (harmonic n : ℂ) * fTerm 0 n) = fun _ => (0 : ℂ) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp
    · simp [fTerm, zero_pow hn]
  rw [hfun]
  simp

def modifiedI0 (z : ℂ) : ℂ := F (z ^ 2 / 4)

def K0Correction (z : ℂ) : ℂ := harmonicF (z ^ 2 / 4)

theorem modifiedI0_analyticAt (z : ℂ) : AnalyticAt ℂ modifiedI0 z := by
  have hq : AnalyticAt ℂ (fun w : ℂ => w ^ 2 / 4) z := by fun_prop
  exact AnalyticAt.comp (x := z) (g := F) (f := fun w : ℂ => w ^ 2 / 4)
    (F_analyticAt (z ^ 2 / 4)) hq

theorem K0Correction_analyticAt (z : ℂ) : AnalyticAt ℂ K0Correction z := by
  have hq : AnalyticAt ℂ (fun w : ℂ => w ^ 2 / 4) z := by fun_prop
  exact AnalyticAt.comp (x := z) (g := harmonicF) (f := fun w : ℂ => w ^ 2 / 4)
    (harmonicF_analyticAt (z ^ 2 / 4)) hq

theorem slitPlane_div_two {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z / 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with hr | hi
  · left
    simpa using div_pos hr (by norm_num : (0 : ℝ) < 2)
  · right
    simpa using div_ne_zero hi (by norm_num : (2 : ℝ) ≠ 0)

theorem K0Series_analyticAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ K0Series z := by
  have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log (w / 2)) z :=
    (analyticAt_id.div_const).clog (slitPlane_div_two hz)
  have hA : AnalyticAt ℂ (fun w : ℂ => F (w ^ 2 / 4)) z := modifiedI0_analyticAt z
  have hB : AnalyticAt ℂ (fun w : ℂ => harmonicF (w ^ 2 / 4)) z := K0Correction_analyticAt z
  change AnalyticAt ℂ
    (fun w : ℂ => -(Complex.log (w / 2) + (Real.eulerMascheroniConstant : ℂ)) *
      F (w ^ 2 / 4) + harmonicF (w ^ 2 / 4)) z
  exact ((hlog.add analyticAt_const).neg.mul hA).add hB

theorem K0Series_analyticOnNhd : AnalyticOnNhd ℂ K0Series Complex.slitPlane :=
  fun _ hz => K0Series_analyticAt hz

theorem K0Series_differentiableOn : DifferentiableOn ℂ K0Series Complex.slitPlane :=
  K0Series_analyticOnNhd.differentiableOn

end J0RadialUniqueness
