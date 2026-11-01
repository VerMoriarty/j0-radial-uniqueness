import Solutions.J0RadialUniqueness.CompactHelmholtzResolvent
import Solutions.J0RadialUniqueness.K0Identification
import Solutions.J0RadialUniqueness.ExactDecomposition
import Solutions.J0RadialUniqueness.AmplitudeUniform

/-! An actual connection formula for the boundary-conditioned radial companion.
The determinant uses both independent K₀ series, subsequently identified with
the proved Laplace integrals. No compact-distribution existence theorem or
growth estimate is supplied as a hypothesis. -/

noncomputable section

namespace J0RadialUniqueness

theorem K0Series_I_mul_helmholtz (lam : ℂ) (s : ℝ) :
    K0Series (Complex.I * ((s : ℂ) * lam)) =
      -(Complex.log (Complex.I * ((s : ℂ) * lam) / 2) +
        (Real.eulerMascheroniConstant : ℂ)) * helmholtzP lam s + helmholtzH lam s := by
  have he : Complex.I * ((s : ℂ) * lam) = Complex.I * lam * (s : ℂ) := by ring
  rw [he]
  rfl

theorem log_I_mul_scale_difference {lam : ℂ} (hlam : lam ≠ 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Complex.log (Complex.I * ((r : ℂ) * lam) / 2) -
        Complex.log (Complex.I * ((s : ℂ) * lam) / 2) =
      (Real.log (r / s) : ℂ) := by
  have hw : Complex.I * lam / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero Complex.I_ne_zero hlam) (by norm_num)
  have he (t : ℝ) : Complex.I * ((t : ℂ) * lam) / 2 =
      (t : ℂ) * (Complex.I * lam / 2) := by ring
  rw [he r, he s, Complex.log_ofReal_mul hr hw, Complex.log_ofReal_mul hs hw,
    Real.log_div hr.ne' hs.ne', Complex.ofReal_sub]
  ring

theorem helmholtzResolventB_K0_determinant {lam : ℂ} (hlam : 0 < lam.re)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (2 * (Real.pi : ℂ) ^ 2 * Complex.I) * helmholtzResolventB r lam s =
      K0Series (-Complex.I * ((r : ℂ) * lam)) *
          K0Series (Complex.I * ((s : ℂ) * lam)) -
        K0Series (Complex.I * ((r : ℂ) * lam)) *
          K0Series (-Complex.I * ((s : ℂ) * lam)) := by
  have hre : 0 < ((r : ℂ) * lam).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_pos hr hlam
  have hse : 0 < ((s : ℂ) * lam).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_pos hs hlam
  have hcr := K0_connection ((r : ℂ) * lam) hre
  have hcs := K0_connection ((s : ℂ) * lam) hse
  rw [← helmholtzP_eq_J0] at hcr hcs
  have hlog := log_I_mul_scale_difference (rightHalfPlane_ne_zero hlam) hr hs
  have hlogs : (Real.log (r / s) : ℂ) = -helmholtzLogRatio r s := by
    unfold helmholtzLogRatio
    rw [Real.log_div hr.ne' hs.ne', Real.log_div hs.ne' hr.ne']
    push_cast
    ring
  rw [hlogs] at hlog
  have hprod :
      K0Series (-Complex.I * ((r : ℂ) * lam)) *
          K0Series (Complex.I * ((s : ℂ) * lam)) -
        K0Series (Complex.I * ((r : ℂ) * lam)) *
          K0Series (-Complex.I * ((s : ℂ) * lam)) =
      (Real.pi : ℂ) * Complex.I *
        (helmholtzP lam r * K0Series (Complex.I * ((s : ℂ) * lam)) -
          K0Series (Complex.I * ((r : ℂ) * lam)) * helmholtzP lam s) := by
    linear_combination
      -K0Series (Complex.I * ((s : ℂ) * lam)) * hcr +
        K0Series (Complex.I * ((r : ℂ) * lam)) * hcs
  have hin :
      helmholtzP lam r * K0Series (Complex.I * ((s : ℂ) * lam)) -
          K0Series (Complex.I * ((r : ℂ) * lam)) * helmholtzP lam s =
        2 * (Real.pi : ℂ) * helmholtzResolventB r lam s := by
    rw [K0Series_I_mul_helmholtz lam s, K0Series_I_mul_helmholtz lam r]
    unfold helmholtzResolventB
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi]
    rw [show Complex.I * lam * (r : ℂ) / 2 =
      Complex.I * ((r : ℂ) * lam) / 2 by ring]
    simp only [mul_assoc] at hlog ⊢
    linear_combination helmholtzP lam r * helmholtzP lam s * hlog
  rw [hprod, hin]
  ring

end J0RadialUniqueness
