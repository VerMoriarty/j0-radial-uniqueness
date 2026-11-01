import Solutions.J0RadialUniqueness.FRightHalfPlane
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
A genuine uniform gap for the actual factorial series F on the exterior of the
closed right half-plane. Compactness is used only on the unit semicircle;
the already proved radial energy monotonicity then controls every larger radius.
-/

noncomputable section

open Set
open scoped Topology

namespace J0RadialUniqueness

def rightUnitSemicircle : Set ℂ := {w | 0 ≤ w.re ∧ ‖w‖ = 1}

theorem isCompact_rightUnitSemicircle : IsCompact rightUnitSemicircle := by
  have hclosed : IsClosed rightUnitSemicircle :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_eq continuous_norm continuous_const)
  apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hclosed
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hw.2.le

/-- The pointwise strict bound has a uniform positive margin on the actual
compact unit semicircle. -/
theorem exists_F_unit_rightHalfPlane_norm_gap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ rightUnitSemicircle, 1 + ε ≤ ‖F w‖ := by
  have hcont : Continuous (fun w : ℂ => ‖F w‖) := F_differentiable.continuous.norm
  have hstrict (w : ℂ) (hw : w ∈ rightUnitSemicircle) : (1 : ℝ) < ‖F w‖ := by
    have hw0 : w ≠ 0 := by
      intro hzero
      have hh : (0 : ℝ) = 1 := by simpa only [hzero, norm_zero] using hw.2
      exact zero_ne_one hh
    exact F_rightHalfPlane w hw0 hw.1
  obtain ⟨c, hc, hbound⟩ := isCompact_rightUnitSemicircle.exists_forall_le'
    hcont.continuousOn hstrict
  refine ⟨c - 1, by linarith, ?_⟩
  intro w hw
  have hh := hbound w hw
  linarith

def rightUnitDirection (w : ℂ) : ℂ := ‖w‖⁻¹ • w

theorem rightUnitDirection_mem {w : ℂ} (hwre : 0 ≤ w.re) (hw : 1 ≤ ‖w‖) :
    rightUnitDirection w ∈ rightUnitSemicircle := by
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw
  constructor
  · change 0 ≤ (‖w‖⁻¹ • w).re
    rw [Complex.smul_re]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg w)) hwre
  · change ‖‖w‖⁻¹ • w‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

theorem norm_smul_rightUnitDirection {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖w‖ • rightUnitDirection w = w := by
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw
  simp only [rightUnitDirection, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- Radial squared-norm monotonicity gives actual norm monotonicity from the
unit direction to any exterior point of the closed right half-plane. -/
theorem norm_F_rightUnitDirection_le {w : ℂ} (hwre : 0 ≤ w.re) (hw : 1 ≤ ‖w‖) :
    ‖F (rightUnitDirection w)‖ ≤ ‖F w‖ := by
  have hdir := rightUnitDirection_mem hwre hw
  have hdir0 : rightUnitDirection w ≠ 0 := by
    intro hzero
    have hh : (0 : ℝ) = 1 := by simpa only [hzero, norm_zero] using hdir.2
    exact zero_ne_one hh
  have hmono := (FRayNormSq_strictMonoOn_of_ode F_ode_statement
    (rightUnitDirection w) hdir0 hdir.1).monotoneOn
  have hY := hmono (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (show ‖w‖ ∈ Ici 0 from norm_nonneg w) hw
  have hscale : (‖w‖ : ℂ) * rightUnitDirection w = w := by
    simpa only [Complex.real_smul] using norm_smul_rightUnitDirection hw
  have hsq : ‖F (rightUnitDirection w)‖ ^ 2 ≤ ‖F w‖ ^ 2 := by
    simpa only [FRayNormSq, FRay, Complex.ofReal_one, one_mul, hscale] using hY
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The same positive constant controls both the excess modulus and the mean
defect throughout the exterior closed right half-plane. -/
theorem F_uniform_gap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, 0 ≤ w.re → 1 ≤ ‖w‖ →
      1 + ε ≤ ‖F w‖ ∧ ε ≤ ‖1 - F w‖ := by
  obtain ⟨ε, hε, hunit⟩ := exists_F_unit_rightHalfPlane_norm_gap
  refine ⟨ε, hε, ?_⟩
  intro w hwre hw
  have hlower : 1 + ε ≤ ‖F w‖ :=
    (hunit (rightUnitDirection w) (rightUnitDirection_mem hwre hw)).trans
      (norm_F_rightUnitDirection_le hwre hw)
  refine ⟨hlower, ?_⟩
  have hreverse : ‖F w‖ - 1 ≤ ‖1 - F w‖ := by
    simpa only [norm_one, norm_sub_rev] using norm_sub_norm_le (F w) (1 : ℂ)
  linarith

theorem F_uniform_norm_gap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, 0 ≤ w.re → 1 ≤ ‖w‖ → 1 + ε ≤ ‖F w‖ := by
  obtain ⟨ε, hε, hgap⟩ := F_uniform_gap
  exact ⟨ε, hε, fun w hwre hw => (hgap w hwre hw).1⟩

theorem F_uniform_defect_gap :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, 0 ≤ w.re → 1 ≤ ‖w‖ → ε ≤ ‖1 - F w‖ := by
  obtain ⟨ε, hε, hgap⟩ := F_uniform_gap
  exact ⟨ε, hε, fun w hwre hw => (hgap w hwre hw).2⟩

end J0RadialUniqueness
