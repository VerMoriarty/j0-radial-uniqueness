import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The integral Grönwall step for the local annular Volterra problem.
The primitive is the actual interval integral of the norm. -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace J0RadialUniqueness

theorem continuous_zero_of_norm_le_volterra_integral {v : ℝ → ℂ}
    (hv : Continuous v) {a b C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ t ∈ Icc a b, ‖v t‖ ≤ C * ∫ s : ℝ in a..t, ‖v s‖) :
    ∀ t ∈ Icc a b, v t = 0 := by
  let E : ℝ → ℝ := fun t => ∫ s : ℝ in a..t, ‖v s‖
  have hd (t : ℝ) : HasDerivAt E ‖v t‖ t :=
    intervalIntegral.integral_hasDerivAt_right (hv.norm.intervalIntegrable a t)
      (hv.norm.stronglyMeasurableAtFilter volume (𝓝 t)) hv.norm.continuousAt
  have hc : Continuous E := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hzero : ∀ t ∈ Icc a b, E t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hc.continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    · simp [E]
    · intro t ht
      have hh := hle t ⟨ht.1, ht.2.le⟩
      change ‖v t‖ ≤ C * E t at hh
      simpa only [Real.norm_eq_abs, abs_norm] using
        hh.trans (mul_le_mul_of_nonneg_left (le_abs_self (E t)) hC)
  intro t ht
  apply norm_eq_zero.mp
  have hh := hle t ht
  change ‖v t‖ ≤ C * E t at hh
  rw [hzero t ht, mul_zero] at hh
  exact le_antisymm hh (norm_nonneg _)

end J0RadialUniqueness
