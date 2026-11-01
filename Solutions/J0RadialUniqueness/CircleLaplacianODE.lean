import Solutions.J0RadialUniqueness.CircleLaplacian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! The radial Laplace equation for the actual circular mean.

The angular acceleration is computed by the chain rule and integrated over a
full period. A direct bilinear identity in the two standard coordinates supplies
the trace. No angular integral, radial ODE, mean-value property or Green identity
is an input to these proofs.
-/

noncomputable section

open MeasureTheory Laplacian Set
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

def circleAxis0 : Plane := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
def circleAxis1 : Plane := (EuclideanSpace.basisFun (Fin 2) ℝ) 1

def circleTangent (t : ℝ) : Plane := WithLp.toLp 2 ![-Real.sin t, Real.cos t]

theorem circleDirection_eq_axes (t : ℝ) :
    circleDirection t = Real.cos t • circleAxis0 + Real.sin t • circleAxis1 := by
  ext i
  fin_cases i <;>
    simp [circleDirection, circleAxis0, circleAxis1,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem circleTangent_eq_axes (t : ℝ) :
    circleTangent t = (-Real.sin t) • circleAxis0 + Real.cos t • circleAxis1 := by
  ext i
  fin_cases i <;>
    simp [circleTangent, circleAxis0, circleAxis1,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem circleDirection_hasDerivAt (t : ℝ) : HasDerivAt circleDirection (circleTangent t) t := by
  have heq : circleDirection = fun s : ℝ =>
      Real.cos s • circleAxis0 + Real.sin s • circleAxis1 := funext circleDirection_eq_axes
  rw [heq, circleTangent_eq_axes]
  exact ((Real.hasDerivAt_cos t).smul_const circleAxis0).add
    ((Real.hasDerivAt_sin t).smul_const circleAxis1)

theorem circleTangent_hasDerivAt (t : ℝ) : HasDerivAt circleTangent (-circleDirection t) t := by
  have heq : circleTangent = fun s : ℝ =>
      (-Real.sin s) • circleAxis0 + Real.cos s • circleAxis1 := funext circleTangent_eq_axes
  rw [heq, circleDirection_eq_axes]
  convert! (((Real.hasDerivAt_sin t).neg).smul_const circleAxis0).add
    ((Real.hasDerivAt_cos t).smul_const circleAxis1) using 1 <;>
    simp only [neg_add, neg_smul]

theorem continuous_circleTangent : Continuous circleTangent :=
  continuous_iff_continuousAt.mpr (fun t => (circleTangent_hasDerivAt t).continuousAt)

/-- Rotation preserves the trace of every real bilinear map in dimension two.
Symmetry of the bilinear map is not needed. -/
theorem circle_bilinear_trace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : Plane →L[ℝ] Plane →L[ℝ] V) (t : ℝ) :
    B (circleDirection t) (circleDirection t) + B (circleTangent t) (circleTangent t) =
      B circleAxis0 circleAxis0 + B circleAxis1 circleAxis1 := by
  have htrig : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    simpa only [add_comm] using Real.sin_sq_add_cos_sq t
  calc
    _ = (Real.cos t ^ 2 + Real.sin t ^ 2) • B circleAxis0 circleAxis0 +
        (Real.cos t ^ 2 + Real.sin t ^ 2) • B circleAxis1 circleAxis1 := by
      rw [circleDirection_eq_axes, circleTangent_eq_axes]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_add, smul_smul]
      module
    _ = _ := by rw [htrig, one_smul, one_smul]

theorem laplacian_eq_axes (f : Plane → ℂ) (y : Plane) :
    laplacian f y = fderiv ℝ (fderiv ℝ f) y circleAxis0 circleAxis0 +
      fderiv ℝ (fderiv ℝ f) y circleAxis1 circleAxis1 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, circleAxis0, circleAxis1]

def circleTangentialSecond (f : Plane → ℂ) (x : Plane) (r t : ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ f) (x + r • circleDirection t) (circleTangent t) (circleTangent t)

def circleAngularSlope (f : Plane → ℂ) (x : Plane) (r t : ℝ) : ℂ :=
  fderiv ℝ f (x + r • circleDirection t) (r • circleTangent t)

def circleAngularAccel (f : Plane → ℂ) (x : Plane) (r t : ℝ) : ℂ :=
  r ^ 2 • circleTangentialSecond f x r t - r • circleSlopeIntegrand f x r t

theorem circle_trace_laplacian (f : Plane → ℂ) (x : Plane) (r t : ℝ) :
    circleAccelIntegrand f x r t + circleTangentialSecond f x r t =
      laplacian f (x + r • circleDirection t) := by
  rw [laplacian_eq_axes]
  exact circle_bilinear_trace (fderiv ℝ (fderiv ℝ f) (x + r • circleDirection t)) t

theorem circleAngularParameter_hasDerivAt (x : Plane) (r t : ℝ) :
    HasDerivAt (fun s : ℝ => x + r • circleDirection s) (r • circleTangent t) t := by
  exact ((circleDirection_hasDerivAt t).const_smul r).const_add x

theorem circleAngularSlope_hasDerivAt {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r t : ℝ) :
    HasDerivAt (circleAngularSlope f x r) (circleAngularAccel f x r t) t := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd := ((hdf.differentiable (by simp)).differentiableAt
    (x := x + r • circleDirection t)).hasFDerivAt
  have hcomp := hd.comp_hasDerivAt t (circleAngularParameter_hasDerivAt x r t)
  have h := hcomp.clm_apply ((circleTangent_hasDerivAt t).const_smul r)
  convert! h using 1 <;>
    simp only [circleAngularSlope, circleAngularAccel, circleTangentialSecond, circleSlopeIntegrand,
      Function.comp_apply, Pi.smul_apply,
      map_smul, ContinuousLinearMap.smul_apply, map_neg, smul_neg, smul_smul,
      sub_eq_add_neg, pow_two]

theorem continuous_circleTangentialSecond {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) : Continuous (circleTangentialSecond f x r) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hddf : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hdf.fderiv_right (by simp)
  have hp : Continuous (fun t : ℝ => x + r • circleDirection t) :=
    continuous_const.add (continuous_circleDirection.const_smul r)
  exact ((hddf.continuous.comp hp).clm_apply continuous_circleTangent).clm_apply
    continuous_circleTangent

theorem continuous_circleAngularAccel {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) : Continuous (circleAngularAccel f x r) := by
  have hs : Continuous (circleSlopeIntegrand f x r) :=
    (continuous_circleSlopeIntegrand hf x).comp (continuous_const.prodMk continuous_id)
  exact ((continuous_circleTangentialSecond hf x r).const_smul (r ^ 2)).sub (hs.const_smul r)

/-- The angular first derivative has identical endpoints on the full circle. -/
theorem circleAngularSlope_period_endpoints (f : Plane → ℂ) (x : Plane) (r : ℝ) :
    circleAngularSlope f x r (2 * Real.pi) = circleAngularSlope f x r 0 := by
  simp [circleAngularSlope, circleDirection, circleTangent]

/-- The angular acceleration has zero actual integral over one full period. -/
theorem integral_circleAngularAccel {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circleAngularAccel f x r t) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => circleAngularSlope_hasDerivAt hf x r t)
    ((continuous_circleAngularAccel hf x r).intervalIntegrable 0 (2 * Real.pi))
  rw [circleAngularSlope_period_endpoints, sub_self] at h
  exact h

theorem circleAngular_integrated_relation {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    r ^ 2 • (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circleTangentialSecond f x r t) -
      r • (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circleSlopeIntegrand f x r t) = 0 := by
  have ht := (continuous_circleTangentialSecond hf x r).intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  have hs := intervalIntegrable_circleSlopeIntegrand hf x r
  have ht' : IntervalIntegrable (fun t : ℝ => r ^ 2 • circleTangentialSecond f x r t)
      volume 0 (2 * Real.pi) := by
    convert! ht.smul (r ^ 2) using 1 <;> rfl
  have hs' : IntervalIntegrable (fun t : ℝ => r • circleSlopeIntegrand f x r t)
      volume 0 (2 * Real.pi) := by
    convert! hs.smul r using 1 <;> rfl
  have h := integral_circleAngularAccel hf x r
  change (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
    r ^ 2 • circleTangentialSecond f x r t - r • circleSlopeIntegrand f x r t) = 0 at h
  rw [intervalIntegral.integral_sub ht' hs',
    intervalIntegral.integral_smul, intervalIntegral.integral_smul] at h
  exact h

/-- The radial Laplace equation, in a form valid also at radius zero. -/
theorem circleRadial_scaled_ode {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    r ^ 2 • circleRadialAccel f x r + r • circleRadialSlope f x r =
      r ^ 2 • circularMean (laplacian f) r x := by
  let c : ℝ := (2 * Real.pi)⁻¹
  let T : ℂ := c • ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circleTangentialSecond f x r t
  have htrace : circularMean (laplacian f) r x = circleRadialAccel f x r + T := by
    have ha := intervalIntegrable_circleAccelIntegrand hf x r
    have ht := (continuous_circleTangentialSecond hf x r).intervalIntegrable (μ := volume) 0 (2 * Real.pi)
    unfold circularMean circleRadialAccel T c
    rw [← smul_add, ← intervalIntegral.integral_add ha ht]
    apply congrArg (fun z : ℂ => ((2 * Real.pi)⁻¹ : ℝ) • z)
    apply intervalIntegral.integral_congr
    intro t _
    exact (circle_trace_laplacian f x r t).symm
  have hangular : r ^ 2 • T - r • circleRadialSlope f x r = 0 := by
    change r ^ 2 • (c • _) - r • (c • _) = 0
    rw [smul_comm (r ^ 2) c, smul_comm r c, ← smul_sub,
      circleAngular_integrated_relation hf x r, smul_zero]
  rw [htrace, smul_add]
  exact congrArg (fun z : ℂ => r ^ 2 • circleRadialAccel f x r + z)
    (sub_eq_zero.mp hangular).symm

theorem circleProfile_scaled_ode {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    r ^ 2 • deriv (deriv (circleProfile f x)) r + r • deriv (circleProfile f x) r =
      r ^ 2 • circularMean (laplacian f) r x := by
  rw [circleProfile_second_deriv hf x r, circleProfile_deriv hf x r]
  exact circleRadial_scaled_ode hf x r

/-- The usual radial ODE, for a positive radius, for the actual circular mean. -/
theorem circleProfile_radial_ode {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (circleProfile f x)) r + deriv (circleProfile f x) r / (r : ℂ) =
      circularMean (laplacian f) r x := by
  have h := circleProfile_scaled_ode hf x r
  simp only [Complex.real_smul, Complex.ofReal_pow] at h
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdiv := congrArg (fun z : ℂ => z / (r : ℂ) ^ 2) h
  convert! hdiv using 1 <;> field_simp [hrC] <;> ring

end J0RadialUniqueness
