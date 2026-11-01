import Solutions.J0RadialUniqueness.PlanarGreenKernel
import Mathlib.MeasureTheory.Measure.OpenPos

/-! From the paper's a.e. circular identities to the actual Green equations
for a smooth input. The passage to pointwise identities uses continuity on the
open natural center domain and positivity of Lebesgue measure. -/

noncomputable section

open MeasureTheory Laplacian
open scoped ContDiff

namespace J0RadialUniqueness

theorem continuous_circularMean_center_of_continuous {f : Plane → ℂ}
    (hf : Continuous f) (r : ℝ) : Continuous (circularMean f r) := by
  have hrd : Continuous (fun p : Plane × ℝ => r • circleDirection p.2) := by
    convert! (show Continuous (fun _ : Plane × ℝ => r) from continuous_const).smul
      (continuous_circleDirection.comp continuous_snd) using 1 <;> rfl
  have hj : Continuous (fun p : Plane × ℝ => f (p.1 + r • circleDirection p.2)) :=
    hf.comp (continuous_fst.add hrd)
  have hi : Continuous (fun x : Plane =>
      ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), f (x + r • circleDirection t)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x : Plane => fun t : ℝ => f (x + r • circleDirection t))
    convert! hj using 1 <;> rfl
  exact continuous_const.smul hi

theorem meanIdentityOn_eqOn_of_continuous {f : Plane → ℂ} (hf : Continuous f)
    (r : ℝ) {U : Set Plane} (hU : IsOpen U) (hmean : MeanIdentityOn f r U) :
    Set.EqOn (circularMean f r) f U :=
  Measure.eqOn_open_of_ae_eq hmean hU (continuous_circularMean_center_of_continuous hf r).continuousOn
    hf.continuousOn

theorem localConvolution_planarGreen_laplacian_eq_zero_of_meanIdentity
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) {R r : ℝ} (hr : 0 < r)
    (hmean : MeanIdentityOn f r (planeBall (R - r))) :
    ∀ x ∈ planeBall (R - r), localConvolution (planarGreenKernel r) (laplacian f) x = 0 := by
  have heq := meanIdentityOn_eqOn_of_continuous hf.continuous r Metric.isOpen_ball hmean
  intro x hx
  rw [localConvolution_planarGreen_laplacian hf x hr, heq hx, sub_self]

end J0RadialUniqueness
