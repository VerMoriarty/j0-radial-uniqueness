import Solutions.J0RadialUniqueness.RotatedK0Bounds

/-! A full-scale sector bound for the actual boundary-conditioned companion.
The radial argument may be arbitrarily small and positive. -/

noncomputable section

namespace J0RadialUniqueness

def rotatedK0Envelope (z : ℂ) : ℝ :=
  Real.sqrt (Real.pi / (2 * ‖z‖)) * (1 + kappa / ‖z‖)

theorem rotatedK0Envelope_nonneg {z : ℂ} : 0 ≤ rotatedK0Envelope z := by
  unfold rotatedK0Envelope
  have hk : 0 ≤ kappa := Real.rpow_nonneg (by norm_num) _
  positivity

theorem norm_K0Series_negI_le_envelope {z : ℂ} (hz : ClosedPrincipalSector z) :
    ‖K0Series (-Complex.I * z)‖ ≤ rotatedK0Envelope z * Real.exp (-z.im) := by
  convert norm_K0Series_negI_le hz using 1 <;> unfold rotatedK0Envelope <;> ring

theorem norm_K0Series_I_le_envelope {z : ℂ} (hz : ClosedPrincipalSector z) :
    ‖K0Series (Complex.I * z)‖ ≤ rotatedK0Envelope z * Real.exp z.im := by
  convert norm_K0Series_I_le hz using 1 <;> unfold rotatedK0Envelope <;> ring

theorem helmholtzResolventB_sector_bound {lam : ℂ} (hlam : ClosedPrincipalSector lam)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r) :
    (2 * Real.pi ^ 2) * ‖helmholtzResolventB r lam s‖ ≤
      2 * rotatedK0Envelope ((r : ℂ) * lam) * rotatedK0Envelope ((s : ℂ) * lam) *
        Real.exp ((r - s) * lam.im) := by
  let zr : ℂ := (r : ℂ) * lam
  let zs : ℂ := (s : ℂ) * lam
  have hzr : ClosedPrincipalSector zr := closedPrincipalSector_pos_scale hlam hr
  have hzs : ClosedPrincipalSector zs := closedPrincipalSector_pos_scale hlam hs
  have hnr := rotatedK0Envelope_nonneg (z := zr)
  have hns := rotatedK0Envelope_nonneg (z := zs)
  have hp := mul_le_mul (norm_K0Series_negI_le_envelope hzr)
    (norm_K0Series_I_le_envelope hzs) (norm_nonneg _)
    (mul_nonneg hnr (Real.exp_pos _).le)
  have hm := mul_le_mul (norm_K0Series_I_le_envelope hzr)
    (norm_K0Series_negI_le_envelope hzs) (norm_nonneg _)
    (mul_nonneg hnr (Real.exp_pos _).le)
  have hnorm := congrArg norm (helmholtzResolventB_K0_determinant hlam.2.2 hr hs)
  have hconst : ‖(2 * (Real.pi : ℂ) ^ 2 * Complex.I)‖ = 2 * Real.pi ^ 2 := by
    simp [norm_mul, norm_pow, abs_of_pos Real.pi_pos]
  rw [norm_mul, hconst] at hnorm
  have hsum :
      (2 * Real.pi ^ 2) * ‖helmholtzResolventB r lam s‖ ≤
        rotatedK0Envelope zr * rotatedK0Envelope zs *
          (Real.exp (-zr.im + zs.im) + Real.exp (zr.im - zs.im)) := by
    calc
      _ ≤ ‖K0Series (-Complex.I * zr) * K0Series (Complex.I * zs)‖ +
          ‖K0Series (Complex.I * zr) * K0Series (-Complex.I * zs)‖ := by
        rw [hnorm]
        exact norm_sub_le _ _
      _ ≤ (rotatedK0Envelope zr * Real.exp (-zr.im)) *
          (rotatedK0Envelope zs * Real.exp zs.im) +
          (rotatedK0Envelope zr * Real.exp zr.im) *
          (rotatedK0Envelope zs * Real.exp (-zs.im)) := by
        simpa only [norm_mul] using add_le_add hp hm
      _ = _ := by simp only [Real.exp_sub, Real.exp_add, Real.exp_neg]; ring
  have himr : zr.im = r * lam.im := by simp [zr]
  have hims : zs.im = s * lam.im := by simp [zs]
  have hdiff : -zr.im + zs.im ≤ (r - s) * lam.im := by
    rw [himr, hims]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsr) hlam.1]
  have hdiff' : zr.im - zs.im = (r - s) * lam.im := by rw [himr, hims]; ring
  have hexp := Real.exp_le_exp.mpr hdiff
  rw [hdiff'] at hsum
  calc
    _ ≤ rotatedK0Envelope zr * rotatedK0Envelope zs *
        (Real.exp (-zr.im + zs.im) + Real.exp ((r - s) * lam.im)) := hsum
    _ ≤ rotatedK0Envelope zr * rotatedK0Envelope zs *
        (2 * Real.exp ((r - s) * lam.im)) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hnr hns)
    _ = _ := by ring

end J0RadialUniqueness
