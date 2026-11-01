import Solutions.J0RadialUniqueness.HelmholtzBallUniqueContinuation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Rotation covariance for the actual angular Fourier integrals. The integer
character and its period are proved explicitly; no Fourier expansion is an
input. These identities are used in the annular circular-mean transform. -/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace J0RadialUniqueness

theorem circleDirection_periodic : Function.Periodic circleDirection (2 * Real.pi) := by
  intro θ
  ext i
  fin_cases i <;> simp [circleDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem helmholtzAngularWeight_periodic (m : ℤ) :
    Function.Periodic (helmholtzAngularWeight m) (2 * Real.pi) := by
  intro θ
  have he : Complex.exp ((-Complex.I * (m : ℂ)) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    convert! Complex.exp_int_mul_two_pi_mul_I (-m) using 1 <;> congr 1 <;> push_cast <;> ring
  simp only [helmholtzAngularWeight, Complex.ofReal_add, mul_add, Complex.exp_add, he, mul_one]

theorem helmholtzAngularWeight_phase_shift (m : ℤ) (θ β : ℝ) :
    helmholtzAngularWeight m θ =
      Complex.exp (Complex.I * (m : ℂ) * (β : ℂ)) * helmholtzAngularWeight m (θ + β) := by
  unfold helmholtzAngularWeight
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem complex_rotation_polar (z : ℂ) (θ : ℝ) :
    complexToPlane (Complex.exp ((θ : ℂ) * Complex.I) * z) =
      ‖z‖ • circleDirection (θ + z.arg) := by
  apply complexToPlane.symm.injective
  simp only [LinearIsometryEquiv.symm_apply_apply, map_smul,
    complexToPlane_symm_circleDirection, Complex.real_smul]
  calc
    _ = Complex.exp ((θ : ℂ) * Complex.I) *
        ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) :=
      congrArg (fun w : ℂ => Complex.exp ((θ : ℂ) * Complex.I) * w)
        (Complex.norm_mul_exp_arg_mul_I z).symm
    _ = _ := by rw [Complex.ofReal_add, add_mul, Complex.exp_add]; ring

def angularFourierAt (f : Plane → ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    helmholtzAngularWeight m θ * f (complexToPlane (Complex.exp ((θ : ℂ) * Complex.I) * z))

theorem angularFourierAt_eq_radial_mode (f : Plane → ℂ) (m : ℤ) (z : ℂ) :
    angularFourierAt f m z =
      Complex.exp (Complex.I * (m : ℂ) * (z.arg : ℂ)) * helmholtzFourierMode f m ‖z‖ := by
  let F : ℝ → ℂ := fun θ => helmholtzAngularWeight m θ * f (‖z‖ • circleDirection θ)
  have hp : Function.Periodic F (2 * Real.pi) := by
    intro θ
    change helmholtzAngularWeight m (θ + 2 * Real.pi) *
        f (‖z‖ • circleDirection (θ + 2 * Real.pi)) = _
    rw [helmholtzAngularWeight_periodic m θ, circleDirection_periodic θ]
  have hshift : (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F (θ + z.arg)) =
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_zero, add_comm] using hp.intervalIntegral_add_eq z.arg 0
  unfold angularFourierAt
  calc
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (Complex.I * (m : ℂ) * (z.arg : ℂ)) * F (θ + z.arg) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [F]
      rw [complex_rotation_polar, helmholtzAngularWeight_phase_shift m θ z.arg]
      ring
    _ = Complex.exp (Complex.I * (m : ℂ) * (z.arg : ℂ)) *
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F (θ + z.arg) :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := by
      rw [hshift]
      simp only [F, helmholtzFourierMode, circleValueIntegrand, zero_add]

end J0RadialUniqueness
