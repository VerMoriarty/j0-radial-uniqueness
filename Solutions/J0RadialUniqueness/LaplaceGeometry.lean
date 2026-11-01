import Definitions.J0RadialUniqueness.Analytic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
open Set

namespace J0RadialUniqueness

/-- Compactification of the unbounded integration parameter preserves nonvanishing. -/
theorem laplace_compactified_ne_zero {w : ℂ} (hw : w ∈ Complex.slitPlane)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ((2 * (1 - s) : ℝ) : ℂ) * w + (s : ℂ) ≠ 0 := by
  by_cases he : s = 1
  · simp [he]
  have hsp : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 he)
  rcases hw with hr | hi
  · have hpos : 0 < (((2 * (1 - s) : ℝ) : ℂ) * w + (s : ℂ)).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) hr) hs.1
    intro hz
    rw [hz] at hpos
    norm_num at hpos
  · have him : (((2 * (1 - s) : ℝ) : ℂ) * w + (s : ℂ)).im ≠ 0 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      exact mul_ne_zero (by positivity) hi
    intro hz
    apply him
    rw [hz]
    rfl

/-- On each compact subset of the slit plane, both denominators have uniform positive bounds.
The base bound holds for every nonnegative integration parameter, including zero. -/
theorem laplace_compact_uniform_lower {L : Set ℂ} (hL : IsCompact L)
    (hsub : L ⊆ Complex.slitPlane) :
    ∃ m c : ℝ, 0 < m ∧ 0 < c ∧
      (∀ w ∈ L, m ≤ ‖w‖) ∧
      (∀ w ∈ L, ∀ t : ℝ, 0 ≤ t → c ≤ ‖1 + (t : ℂ) / (2 * w)‖) := by
  obtain ⟨m, hm, hmb⟩ := hL.exists_forall_le' continuous_norm.continuousOn
    (fun w hw => norm_pos_iff.mpr (Complex.slitPlane_ne_zero (hsub hw)))
  obtain ⟨M, hM, hMb⟩ := hL.isBounded.exists_pos_norm_le
  have hprod : IsCompact (L ×ˢ Icc (0 : ℝ) 1) := hL.prod isCompact_Icc
  have hcont : Continuous (fun p : ℂ × ℝ =>
      ‖((2 * (1 - p.2) : ℝ) : ℂ) * p.1 + (p.2 : ℂ)‖) := by fun_prop
  obtain ⟨η, hη, hηb⟩ := hprod.exists_forall_le' hcont.continuousOn
    (fun p hp => norm_pos_iff.mpr (laplace_compactified_ne_zero (hsub hp.1) hp.2))
  refine ⟨m, η / (2 * M), hm, by positivity, hmb, ?_⟩
  intro w hw t ht
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hm (hmb w hw)
  have hwnz : w ≠ 0 := norm_pos_iff.mp hwpos
  have ht1 : 0 < 1 + t := by linarith
  let s : ℝ := t / (1 + t)
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg ht ht1.le, (div_le_one ht1).mpr ?_⟩
    linarith
  have hηw := hηb (w, s) ⟨hw, hs⟩
  have he : 2 * w + (t : ℂ) = ((1 + t : ℝ) : ℂ) *
      (((2 * (1 - s) : ℝ) : ℂ) * w + (s : ℂ)) := by
    dsimp only [s]
    push_cast
    have htc : (1 : ℂ) + (t : ℂ) ≠ 0 := by exact_mod_cast ht1.ne'
    field_simp [htc]
    ring
  have hN : η ≤ ‖2 * w + (t : ℂ)‖ := by
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht1]
    nlinarith [norm_nonneg (((2 * (1 - s) : ℝ) : ℂ) * w + (s : ℂ))]
  have hbase : 1 + (t : ℂ) / (2 * w) = (2 * w + (t : ℂ)) / (2 * w) := by
    field_simp
  rw [hbase, norm_div, norm_mul]
  norm_num
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * M)
    (by positivity : 0 < 2 * ‖w‖)).mpr
  have hupper := hMb w hw
  nlinarith [mul_le_mul_of_nonneg_left hupper hη.le,
    mul_le_mul_of_nonneg_right hN hM.le]

/-- A compact neighborhood suitable for a single complex derivative-under-integral call. -/
theorem laplace_local_uniform_lower {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ∃ r m c : ℝ, 0 < r ∧ 0 < m ∧ 0 < c ∧
      Metric.closedBall w r ⊆ Complex.slitPlane ∧
      (∀ z ∈ Metric.closedBall w r, m ≤ ‖z‖) ∧
      (∀ z ∈ Metric.closedBall w r, ∀ t : ℝ, 0 ≤ t →
        c ≤ ‖1 + (t : ℂ) / (2 * z)‖) := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp Complex.isOpen_slitPlane w hw
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hsub : Metric.closedBall w r ⊆ Complex.slitPlane := by
    intro z hz
    apply hεsub
    change dist z w ≤ r at hz
    change dist z w < ε
    exact lt_of_le_of_lt hz (by change ε / 2 < ε; linarith)
  obtain ⟨m, c, hm, hc, hmb, hcb⟩ :=
    laplace_compact_uniform_lower (isCompact_closedBall w r) hsub
  exact ⟨r, m, c, hr, hm, hc, hsub, hmb, hcb⟩

end J0RadialUniqueness
