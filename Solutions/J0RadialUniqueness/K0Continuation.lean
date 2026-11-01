import Solutions.J0RadialUniqueness.LaplaceAnalytic
import Solutions.J0RadialUniqueness.K0SeriesAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter
open scoped Topology

namespace J0RadialUniqueness

/-- Identity continuation is applied at the regular point one, inside the whole
connected slit plane. The singular endpoint zero is never an initial-value point. -/
theorem laplaceIdentification_of_positive_real
    (hpos : ∀ x : ℝ, 0 < x → laplaceK (x : ℂ) = K0Series (x : ℂ)) :
    KLaplaceIdentificationStatement := by
  have hk := laplaceK_differentiableOn.analyticOnNhd Complex.isOpen_slitPlane
  have hs := K0Series_analyticOnNhd
  have hc : IsPreconnected Complex.slitPlane :=
    (Complex.starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected
  let u : ℕ → ℂ := fun n => ((1 + (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝 (1 : ℂ)) := by
    have hr : Tendsto (fun n : ℕ => 1 + (1 / ((n : ℝ) + 1))) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact hr.ofReal
  have hun : ∀ᶠ n : ℕ in atTop, u n ∈ ({(1 : ℂ)} : Set ℂ)ᶜ := by
    filter_upwards [] with n
    change u n ≠ 1
    intro he
    have he' := congrArg Complex.re he
    dsimp [u] at he'
    change (1 + 1 / ((n : ℝ) + 1)) = 1 at he'
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hup : Tendsto u atTop (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, hun⟩
  have he : ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), laplaceK z = K0Series z := by
    apply hup.frequently
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    exact hpos _ (by positivity)
  exact hk.eqOn_of_preconnected_of_frequently_eq hs hc (by simp) he

end J0RadialUniqueness
