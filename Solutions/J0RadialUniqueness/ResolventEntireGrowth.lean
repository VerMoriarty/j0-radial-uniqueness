import Solutions.J0RadialUniqueness.EntireSeriesGrowth
import Solutions.J0RadialUniqueness.PlanarHelmholtzResolvent

/-! The actual entire resolvent has order one in its spectral parameter.

Multiplication by the polar Jacobian removes the logarithmic singularity.
The explicit weighted formula is jointly continuous, including radius zero,
and equals s times the independently defined resolvent. The bound below is
uniform over the full compact radial interval; its constant is independent of
the complex spectral parameter. No Paley--Wiener or growth premise is used.
-/

noncomputable section

open Set
open scoped Topology

namespace J0RadialUniqueness

theorem helmholtzResolventWeightedT_eq_expanded (r : ℝ) (lam : ℂ) (s : ℝ) :
    helmholtzResolventWeightedT r lam s =
      ((greenRadialWeight r s : ℂ) *
        (((r : ℂ) ^ 2 / 4) * (Q (helmholtzResolventArg lam r) * helmholtzP lam s) +
          ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)) +
      ((s : ℂ) ^ 3 / 4) *
        (helmholtzP lam r * harmonicDividedDifference (helmholtzResolventArg lam s)) -
      ((r : ℂ) ^ 2 * (s : ℂ) / 4) *
        (harmonicDividedDifference (helmholtzResolventArg lam r) * helmholtzP lam s)) /
        (2 * (Real.pi : ℂ)) := by
  unfold helmholtzResolventWeightedT
  ring

@[simp] theorem helmholtzResolventWeightedT_zero (r : ℝ) (lam : ℂ) :
    helmholtzResolventWeightedT r lam 0 = 0 := by
  rw [helmholtzResolventWeightedT_eq]
  simp

theorem helmholtzResolventWeightedT_parameter_analyticAt (r s : ℝ) (lam : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => helmholtzResolventWeightedT r z s) lam := by
  have heq : (fun z : ℂ => helmholtzResolventWeightedT r z s) =
      fun z : ℂ => (s : ℂ) * helmholtzResolventT r z s :=
    funext (fun z => helmholtzResolventWeightedT_eq r z s)
  rw [heq]
  exact analyticAt_const.mul (helmholtzResolventT_parameter_analyticAt r s lam)

theorem intervalIntegrable_helmholtzResolventWeightedT {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    IntervalIntegrable (helmholtzResolventWeightedT r lam) MeasureTheory.volume 0 r := by
  have hc : Continuous (helmholtzResolventWeightedT r lam) :=
    (continuous_helmholtzResolventWeightedT_joint hr).comp
      (continuous_const.prodMk continuous_id)
  exact hc.intervalIntegrable 0 r

theorem norm_helmholtzP_le_exp_radius {s : ℝ} (hs : 0 ≤ s) (lam : ℂ) :
    ‖helmholtzP lam s‖ ≤ Real.exp (s * ‖lam‖) := by
  rw [helmholtzP_eq_F_arg]
  exact norm_F_helmholtzResolventArg_le hs lam

theorem complex_norm_mul_le_square {u v : ℂ} {E : ℝ}
    (hu : ‖u‖ ≤ E) (hv : ‖v‖ ≤ E) (hE : 0 ≤ E) : ‖u * v‖ ≤ E ^ 2 := by
  rw [norm_mul, pow_two]
  exact mul_le_mul hu hv (norm_nonneg _) hE

/-- A genuine uniform exponential-type bound on the full polar radial interval.
The coefficient power may be taken to be zero: no spectral polynomial is needed. -/
theorem helmholtzResolventWeightedT_uniform_exp_bound {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ, ∀ s ∈ Icc (0 : ℝ) r,
      ‖helmholtzResolventWeightedT r lam s‖ ≤ C * Real.exp (2 * r * ‖lam‖) := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) r)).exists_bound_of_continuousOn
    (continuous_greenRadialWeight hr).continuousOn
  let M : ℝ := 1 + |K|
  have hM : 0 < M := by dsimp [M]; positivity
  have hgreen (s : ℝ) (hs : s ∈ Icc (0 : ℝ) r) : ‖(greenRadialWeight r s : ℂ)‖ ≤ M := by
    rw [Complex.norm_real]
    exact (hK s hs).trans (by dsimp [M]; linarith [le_abs_self K])
  let C : ℝ := (M * r ^ 2 / 2 + r ^ 3 / 2) / (2 * Real.pi) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro lam s hs
  have hs0 : 0 ≤ s := hs.1
  have hsr : s ≤ r := hs.2
  let E : ℝ := Real.exp (r * ‖lam‖)
  have hEpos : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hr.le (norm_nonneg lam))
  have hEsq : E ^ 2 = Real.exp (2 * r * ‖lam‖) := by
    dsimp [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsE : Real.exp (s * ‖lam‖) ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg lam)
  have hQr : ‖Q (helmholtzResolventArg lam r)‖ ≤ E := norm_Q_helmholtzResolventArg_le hr.le lam
  have hQs : ‖Q (helmholtzResolventArg lam s)‖ ≤ E :=
    (norm_Q_helmholtzResolventArg_le hs.1 lam).trans hsE
  have hDr : ‖harmonicDividedDifference (helmholtzResolventArg lam r)‖ ≤ E :=
    norm_D_helmholtzResolventArg_le hr.le lam
  have hDs : ‖harmonicDividedDifference (helmholtzResolventArg lam s)‖ ≤ E :=
    (norm_D_helmholtzResolventArg_le hs.1 lam).trans hsE
  have hPr : ‖helmholtzP lam r‖ ≤ E := norm_helmholtzP_le_exp_radius hr.le lam
  have hPs : ‖helmholtzP lam s‖ ≤ E := (norm_helmholtzP_le_exp_radius hs.1 lam).trans hsE
  have hQPs := complex_norm_mul_le_square hQr hPs hEpos.le
  have hPDs := complex_norm_mul_le_square hPr hDs hEpos.le
  have hDPs := complex_norm_mul_le_square hDr hPs hEpos.le
  have hQs2 : ‖Q (helmholtzResolventArg lam s)‖ ≤ E ^ 2 := by
    have hEE : E ≤ E ^ 2 := by nlinarith
    exact hQs.trans hEE
  have hcr : ‖(r : ℂ) ^ 2 / 4‖ = r ^ 2 / 4 := by
    simp [norm_div, norm_pow, Complex.norm_of_nonneg hr.le]
  have hcs : ‖(s : ℂ) ^ 2 / 4‖ ≤ r ^ 2 / 4 := by
    simp only [norm_div, norm_pow, Complex.norm_of_nonneg hs.1, Complex.norm_ofNat]
    gcongr
  have hcs3 : ‖(s : ℂ) ^ 3 / 4‖ ≤ r ^ 3 / 4 := by
    simp only [norm_div, norm_pow, Complex.norm_of_nonneg hs.1, Complex.norm_ofNat]
    gcongr
  have hcrs : ‖(r : ℂ) ^ 2 * (s : ℂ) / 4‖ ≤ r ^ 3 / 4 := by
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_of_nonneg hs.1,
      Complex.norm_of_nonneg hr.le, Complex.norm_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hs.2 (sq_nonneg r)]
  have hU :
      ‖((r : ℂ) ^ 2 / 4) * (Q (helmholtzResolventArg lam r) * helmholtzP lam s)‖ ≤
        (r ^ 2 / 4) * E ^ 2 := by
    rw [norm_mul, hcr]
    exact mul_le_mul_of_nonneg_left hQPs (by positivity)
  have hV : ‖((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)‖ ≤
      (r ^ 2 / 4) * E ^ 2 := by
    rw [norm_mul]
    exact mul_le_mul hcs hQs2 (norm_nonneg _) (by positivity)
  have hW : ‖((s : ℂ) ^ 3 / 4) *
      (helmholtzP lam r * harmonicDividedDifference (helmholtzResolventArg lam s))‖ ≤
        (r ^ 3 / 4) * E ^ 2 := by
    rw [norm_mul]
    exact mul_le_mul hcs3 hPDs (norm_nonneg _) (by positivity)
  have hZ : ‖((r : ℂ) ^ 2 * (s : ℂ) / 4) *
      (harmonicDividedDifference (helmholtzResolventArg lam r) * helmholtzP lam s)‖ ≤
        (r ^ 3 / 4) * E ^ 2 := by
    rw [norm_mul]
    exact mul_le_mul hcrs hDPs (norm_nonneg _) (by positivity)
  have hblock :
      ‖((r : ℂ) ^ 2 / 4) * (Q (helmholtzResolventArg lam r) * helmholtzP lam s) +
        ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)‖ ≤ (r ^ 2 / 2) * E ^ 2 := by
    exact (norm_add_le _ _).trans (by linarith)
  have hfirst :
      ‖(greenRadialWeight r s : ℂ) *
        (((r : ℂ) ^ 2 / 4) * (Q (helmholtzResolventArg lam r) * helmholtzP lam s) +
          ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s))‖ ≤
        M * ((r ^ 2 / 2) * E ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul (hgreen s hs) hblock (norm_nonneg _) hM.le
  have hnum :
      ‖(greenRadialWeight r s : ℂ) *
          (((r : ℂ) ^ 2 / 4) * (Q (helmholtzResolventArg lam r) * helmholtzP lam s) +
            ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)) +
        ((s : ℂ) ^ 3 / 4) *
          (helmholtzP lam r * harmonicDividedDifference (helmholtzResolventArg lam s)) -
        ((r : ℂ) ^ 2 * (s : ℂ) / 4) *
          (harmonicDividedDifference (helmholtzResolventArg lam r) * helmholtzP lam s)‖ ≤
        (M * r ^ 2 / 2 + r ^ 3 / 2) * E ^ 2 := by
    calc
      _ ≤ ‖(greenRadialWeight r s : ℂ) *
          (((r : ℂ) ^ 2 / 4) * (Q (helmholtzResolventArg lam r) * helmholtzP lam s) +
            ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)) +
        ((s : ℂ) ^ 3 / 4) *
          (helmholtzP lam r * harmonicDividedDifference (helmholtzResolventArg lam s))‖ +
        ‖((r : ℂ) ^ 2 * (s : ℂ) / 4) *
          (harmonicDividedDifference (helmholtzResolventArg lam r) * helmholtzP lam s)‖ := norm_sub_le _ _
      _ ≤ (M * r ^ 2 / 2 + r ^ 3 / 2) * E ^ 2 := by
        have hh := norm_add_le
          ((greenRadialWeight r s : ℂ) *
            (((r : ℂ) ^ 2 / 4) * (Q (helmholtzResolventArg lam r) * helmholtzP lam s) +
              ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)))
          (((s : ℂ) ^ 3 / 4) *
            (helmholtzP lam r * harmonicDividedDifference (helmholtzResolventArg lam s)))
        linarith
  rw [helmholtzResolventWeightedT_eq_expanded]
  rw [norm_div, show ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi by simp [norm_mul, abs_of_pos Real.pi_pos]]
  calc
    _ ≤ ((M * r ^ 2 / 2 + r ^ 3 / 2) * E ^ 2) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hnum Real.two_pi_pos.le
    _ = ((M * r ^ 2 / 2 + r ^ 3 / 2) / (2 * Real.pi)) * Real.exp (2 * r * ‖lam‖) := by
      rw [hEsq]
      ring
    _ ≤ C * Real.exp (2 * r * ‖lam‖) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      dsimp [C]
      linarith

end J0RadialUniqueness
