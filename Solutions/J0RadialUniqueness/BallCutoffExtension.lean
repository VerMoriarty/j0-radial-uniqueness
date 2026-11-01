import Solutions.J0RadialUniqueness.RootExponentialSeriesSmooth
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! A finite-order smooth function on a larger ball admits an actual compact
global extension agreeing on the prescribed smaller ball. The outside proof
uses the zero germ of the cutoff and never assumes a global smooth extension
of an arbitrary function on an open ball. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace J0RadialUniqueness

theorem exists_contDiff_compact_ball_extension (n : ℕ) {f : Plane → ℂ} {R T : ℝ}
    (hR : 0 < R) (hRT : R < T) (hf : ContDiffOn ℝ (n : ℕ∞ω) f (planeBall T)) :
    ∃ g : Plane → ℂ, ContDiff ℝ (n : ℕ∞ω) g ∧ HasCompactSupport g ∧
      EqOn g f (planeBall R) := by
  let χ : ContDiffBump (0 : Plane) :=
    { rIn := R, rOut := (R + T) / 2, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let g : Plane → ℂ := fun x => χ x • f x
  have hχ : ContDiff ℝ ∞ (χ : Plane → ℝ) := χ.contDiff
  have hχn : ContDiff ℝ (n : ℕ∞ω) (χ : Plane → ℝ) := (contDiff_infty.mp hχ) n
  have hsg : ContDiff ℝ (n : ℕ∞ω) g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ planeBall T
    · exact hχn.contDiffAt.smul (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hx))
    · have hxχ : x ∉ tsupport (χ : Plane → ℝ) := by
        intro hxs
        rw [χ.tsupport_eq] at hxs
        have hn : ‖x‖ ≤ (R + T) / 2 := by
          simpa only [Metric.mem_closedBall, dist_zero_right, χ] using hxs
        apply hx
        change dist x 0 < T
        rw [dist_zero_right]
        linarith
      have heχ : (χ : Plane → ℝ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
        notMem_tsupport_iff_eventuallyEq.mp hxχ
      have heg : g =ᶠ[𝓝 x] (fun _ : Plane => (0 : ℂ)) := by
        filter_upwards [heχ] with y hy
        change χ y • f y = 0
        rw [hy, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heg
  have hcg : HasCompactSupport g := by
    apply χ.hasCompactSupport.mono
    intro x hx
    change χ x ≠ 0
    intro hzero
    exact hx (by simp only [g, hzero, zero_smul])
  refine ⟨g, hsg, hcg, ?_⟩
  intro x hx
  change χ x • f x = f x
  rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_smul]

theorem firstCoordinate_abs_le_norm (x : Plane) : |x 0| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0

theorem coordinate_lift_contDiffOn_ball (n : ℕ) {h : ℝ → ℂ} {T : ℝ}
    (hh : ContDiffOn ℝ (n : ℕ∞ω) h (Ioo (-T) T)) :
    ContDiffOn ℝ (n : ℕ∞ω) (fun x : Plane => h (x 0)) (planeBall T) := by
  apply hh.comp (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).contDiff.contDiffOn
  intro x hx
  have hn : ‖x‖ < T := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
  have hab := (firstCoordinate_abs_le_norm x).trans_lt hn
  exact abs_lt.mp hab

end J0RadialUniqueness
