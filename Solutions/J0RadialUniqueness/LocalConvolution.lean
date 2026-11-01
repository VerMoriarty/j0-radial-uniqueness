import Solutions.J0RadialUniqueness.CircularMeanDomain
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory Set

namespace J0RadialUniqueness

/-- Kernel-first real scalar convolution, with the actual Lebesgue integral. -/
def localConvolution (k : Plane → ℝ) (f : Plane → ℂ) (x : Plane) : ℂ :=
  ∫ y : Plane, k y • f (x - y)

theorem norm_sub_lt_of_inner_ball {x y : Plane} {R ε : ℝ}
    (hx : x ∈ planeBall (R - ε)) (hy : ‖y‖ ≤ ε) : x - y ∈ planeBall R := by
  have hxn : ‖x‖ < R - ε := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
  change dist (x - y) 0 < R
  rw [dist_zero_right]
  exact (norm_sub_le x y).trans_lt (by linarith)

/-- A compact-radius convolution depends only on the ambient AE class within
the larger ball. This is a local lemma, with no extension theorem or Fourier input. -/
theorem localConvolution_congr_on_inner_ball {k : Plane → ℝ} {f g : Plane → ℂ}
    {R ε : ℝ} (hk : ∀ y : Plane, k y ≠ 0 → ‖y‖ ≤ ε)
    (hfg : f =ᵐ[volume.restrict (planeBall R)] g)
    {x : Plane} (hx : x ∈ planeBall (R - ε)) :
    localConvolution k f x = localConvolution k g x := by
  have h : ∀ᵐ u : Plane, u ∈ planeBall R → f u = g u :=
    (ae_restrict_iff' (show MeasurableSet (planeBall R) from measurableSet_ball)).mp hfg
  have he := ((volume : Measure Plane).measurePreserving_sub_left x).quasiMeasurePreserving.ae h
  apply integral_congr_ae
  filter_upwards [he] with y hy
  by_cases hky : k y = 0
  · simp [hky]
  · rw [hy (norm_sub_lt_of_inner_ball hx (hk y hky))]

/-- The sum of support radii bounds the support of the actual convolution.
Integrability is unnecessary for this vanishing statement: the integrand is zero. -/
theorem localConvolution_eq_zero_outside_sum {k : Plane → ℝ} {f : Plane → ℂ}
    {a b : ℝ} (hk : ∀ y : Plane, k y ≠ 0 → ‖y‖ ≤ a)
    (hf : ∀ y : Plane, f y ≠ 0 → ‖y‖ ≤ b)
    {x : Plane} (hx : a + b < ‖x‖) : localConvolution k f x = 0 := by
  unfold localConvolution
  have hi : (fun y : Plane => k y • f (x - y)) = 0 := by
    funext y
    by_cases hky : k y = 0
    · simp [hky]
    by_cases hfy : f (x - y) = 0
    · simp [hfy]
    have hn : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      simpa only [add_sub_cancel] using norm_add_le y (x - y)
    have := hk y hky
    have := hf (x - y) hfy
    exfalso
    linarith
  rw [hi]
  change (∫ _y : Plane, (0 : ℂ)) = 0
  exact integral_zero _ _

end J0RadialUniqueness
