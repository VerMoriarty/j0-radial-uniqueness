import Solutions.J0RadialUniqueness.CircularMeanFourier
import Solutions.J0RadialUniqueness.ChebyshevAbelKernel

/-! Pairing opposite angular parameters in the actual Fourier projection.
The input function may be complex-valued: only the geometric phase is paired,
while its radial Fourier coefficient is kept as the same complex coefficient. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace J0RadialUniqueness

theorem exp_real_phase_add_negative (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I)) =
      2 * (Real.cos t : ℂ) := by
  rw [show -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I by ring, ← Complex.two_cos]
  simp

theorem chebyshev_natAbs_cos_arg (m : ℤ) {z : ℂ} (hz : z ≠ 0) :
    chebyshevTValue m.natAbs (z.re / ‖z‖) = Real.cos ((m : ℝ) * z.arg) := by
  unfold chebyshevTValue
  rw [Polynomial.Chebyshev.T_natAbs, ← Complex.cos_arg hz,
    Polynomial.Chebyshev.T_real_cos]

theorem angular_phase_conjugate_sum (m : ℤ) {z : ℂ} (hi : 0 < z.im) :
    Complex.exp (Complex.I * (m : ℂ) * (z.arg : ℂ)) +
        Complex.exp (Complex.I * (m : ℂ) * ((conj z).arg : ℂ)) =
      2 * (chebyshevTValue m.natAbs (z.re / ‖z‖) : ℂ) := by
  have hz : z ≠ 0 := by intro h; have := hi; rw [h] at this; exact lt_irrefl _ this
  have harg : z.arg ≠ Real.pi := ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne'))
  have he (t : ℝ) : Complex.I * (m : ℂ) * (t : ℂ) =
      (((m : ℝ) * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hn : Complex.I * (m : ℂ) * ((-z.arg : ℝ) : ℂ) =
      -(((((m : ℝ) * z.arg : ℝ) : ℂ)) * Complex.I) := by push_cast; ring
  rw [Complex.arg_conj, if_neg harg, he z.arg, hn, exp_real_phase_add_negative]
  rw [← chebyshev_natAbs_cos_arg m hz]

theorem angularFourierAt_conjugate_pair (f : Plane → ℂ) (m : ℤ) {z : ℂ}
    (hi : 0 < z.im) :
    angularFourierAt f m z + angularFourierAt f m (conj z) =
      2 * (chebyshevTValue m.natAbs (z.re / ‖z‖) : ℂ) * helmholtzFourierMode f m ‖z‖ := by
  rw [angularFourierAt_eq_radial_mode, angularFourierAt_eq_radial_mode, Complex.norm_conj,
    ← add_mul, angular_phase_conjugate_sum m hi]

theorem continuous_angularFourierAt {f : Plane → ℂ} (hf : Continuous f) (m : ℤ) :
    Continuous (angularFourierAt f m) := by
  have hp : Continuous (fun p : ℂ × ℝ =>
      Complex.exp ((p.2 : ℂ) * Complex.I) * p.1) := by fun_prop
  have hj : Continuous (fun p : ℂ × ℝ =>
      helmholtzAngularWeight m p.2 * f (complexToPlane
        (Complex.exp ((p.2 : ℂ) * Complex.I) * p.1))) :=
    ((continuous_helmholtzAngularWeight m).comp continuous_snd).mul
      (hf.comp (complexToPlane.continuous.comp hp))
  unfold angularFourierAt
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun z : ℂ => fun θ : ℝ => helmholtzAngularWeight m θ *
      f (complexToPlane (Complex.exp ((θ : ℂ) * Complex.I) * z)))
  convert! hj using 1 <;> rfl

def circleChord (ρ r α : ℝ) : ℂ :=
  (ρ : ℂ) + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)

theorem circleChord_im_pos {ρ r α : ℝ} (hr : 0 < r) (hα : α ∈ Set.Ioo (0 : ℝ) Real.pi) :
    0 < (circleChord ρ r α).im := by
  simpa only [circleChord, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, add_zero, zero_add, Complex.exp_ofReal_mul_I_im] using
      mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2)

theorem circleChord_reflect (ρ r α : ℝ) :
    circleChord ρ r (2 * Real.pi - α) = conj (circleChord ρ r α) := by
  have he : (((2 * Real.pi - α : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I + -((α : ℂ) * Complex.I) := by push_cast; ring
  unfold circleChord
  rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  simp [← Complex.exp_conj]

end J0RadialUniqueness
