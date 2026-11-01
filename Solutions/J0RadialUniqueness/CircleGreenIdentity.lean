import Solutions.J0RadialUniqueness.CircleLaplacianODE
import Solutions.J0RadialUniqueness.GreenSpectralIntegral
import Mathlib.Tactic

/-! Integrating the actual circular-mean ODE to its logarithmic Green identity.

The primitive `t log(r/t) M'(t) + M(t)` is continuous at zero. Its derivative is
computed only at positive t, so there is no hidden differentiability claim for
the logarithm at the endpoint. The result here is the exact radial integral;
identification with a planar convolution is a separate polar-coordinate step.
-/

noncomputable section

open MeasureTheory Laplacian
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

theorem laplacian_contDiff_infty {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (laplacian f) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hddf : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hdf.fderiv_right (by simp)
  have heq : laplacian f = fun y : Plane =>
      fderiv ℝ (fderiv ℝ f) y circleAxis0 circleAxis0 +
        fderiv ℝ (fderiv ℝ f) y circleAxis1 circleAxis1 := funext (laplacian_eq_axes f)
  rw [heq]
  exact ((hddf.clm_apply contDiff_const).clm_apply contDiff_const).add
    ((hddf.clm_apply contDiff_const).clm_apply contDiff_const)

def circleGreenPrimitive (f : Plane → ℂ) (x : Plane) (r t : ℝ) : ℂ :=
  greenRadialWeight r t • circleRadialSlope f x t + circleProfile f x t

theorem continuous_circleGreenPrimitive {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) : Continuous (circleGreenPrimitive f x r) :=
  ((continuous_greenRadialWeight hr).smul (circleRadialSlope_differentiable hf x).continuous).add
    (circleProfile_differentiable hf x).continuous

theorem circleGreenPrimitive_hasDerivAt {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    HasDerivAt (circleGreenPrimitive f x r)
      (greenRadialWeight r t • circularMean (laplacian f) t x) t := by
  have h := ((greenRadialWeight_hasDerivAt hr ht).smul
    (circleRadialSlope_hasDerivAt hf x t)).add (circleProfile_hasDerivAt hf x t)
  apply h.congr_deriv
  have hode := circleProfile_radial_ode hf x ht
  rw [circleProfile_second_deriv hf x t, circleProfile_deriv hf x t] at hode
  rw [← hode]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [greenRadialWeight, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_mul]
  field_simp [htC]
  <;> ring

theorem intervalIntegrable_circleGreenLaplacian {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun t : ℝ => greenRadialWeight r t • circularMean (laplacian f) t x)
      volume 0 r := by
  have hc : Continuous (fun t : ℝ => circularMean (laplacian f) t x) :=
    (circleProfile_differentiable (laplacian_contDiff_infty hf) x).continuous
  exact ((continuous_greenRadialWeight hr).smul hc).intervalIntegrable 0 r

@[simp] theorem circleGreenPrimitive_zero (f : Plane → ℂ) (x : Plane) (r : ℝ) :
    circleGreenPrimitive f x r 0 = f x := by
  simp [circleGreenPrimitive, greenRadialWeight]

@[simp] theorem circleGreenPrimitive_radius (f : Plane → ℂ) (x : Plane) {r : ℝ} (hr : 0 < r) :
    circleGreenPrimitive f x r r = circularMean f r x := by
  simp [circleGreenPrimitive, greenRadialWeight, hr.ne', circleProfile]

/-- The radial Green identity is a direct FTC consequence of the actual mean ODE. -/
theorem integral_circleGreen_laplacian {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in (0 : ℝ)..r, (t * Real.log (r / t)) • circularMean (laplacian f) t x) =
      circularMean f r x - f x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.le
    (continuous_circleGreenPrimitive hf x hr).continuousOn
    (fun t ht => circleGreenPrimitive_hasDerivAt hf x hr ht.1)
    (intervalIntegrable_circleGreenLaplacian hf x hr)
  simpa only [greenRadialWeight, circleGreenPrimitive_zero,
    circleGreenPrimitive_radius f x hr] using h

end J0RadialUniqueness
