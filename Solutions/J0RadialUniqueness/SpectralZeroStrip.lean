import Solutions.J0RadialUniqueness.MeanDefectSpectrum

noncomputable section

namespace J0RadialUniqueness

theorem principal_one_point_exp_im_bound {z : ℂ} (hJ : J0 z = 1)
    (hz : PrincipalSector z) : Real.exp z.im < 4 * ‖z‖ := by
  have hr := one_point_norm_ge_four z (principalSector_ne_zero hz) hJ
  obtain ⟨hdom, _, _, hd, _⟩ := quantitative_separation z hJ hz
  obtain ⟨_, _, hm, _, _, _⟩ := amplitude_modulus_bounds z (principalSector_closed hz) hr
  have htri : (1 : ℝ) ≤ ‖1 + delta z‖ + ‖delta z‖ := by
    calc
      (1 : ℝ) = ‖((1 + delta z) - delta z)‖ := by simp
      _ ≤ ‖1 + delta z‖ + ‖delta z‖ := norm_sub_le _ _
  have hp : (1 / 2 : ℝ) < ‖AMinus z‖ * ‖1 + delta z‖ := by
    have hD : (7 / 8 : ℝ) < ‖1 + delta z‖ := by linarith
    nlinarith [norm_nonneg (AMinus z), norm_nonneg (1 + delta z)]
  have hroot : 0 < Real.sqrt (2 * Real.pi * ‖z‖) := by positivity
  have hn := congrArg norm (paper_factorization z hdom)
  rw [hJ, norm_one, norm_mul, norm_div, norm_mul, Complex.norm_exp,
    norm_half_power_denominator] at hn
  have he : (-Complex.I * (z - (Real.pi : ℂ) / 4)).re = z.im := by simp
  rw [he] at hn
  have hmass : Real.exp z.im * (‖AMinus z‖ * ‖1 + delta z‖) =
      Real.sqrt (2 * Real.pi * ‖z‖) := by
    have heq : Real.exp z.im * (‖AMinus z‖ * ‖1 + delta z‖) /
        Real.sqrt (2 * Real.pi * ‖z‖) = 1 := by
      calc
        _ = Real.exp z.im * ‖AMinus z‖ / Real.sqrt (2 * Real.pi * ‖z‖) *
            ‖1 + delta z‖ := by ring
        _ = 1 := hn.symm
    exact (div_eq_one_iff_eq hroot.ne').mp heq
  have hhalf : Real.exp z.im / 2 < Real.sqrt (2 * Real.pi * ‖z‖) := by
    rw [← hmass]
    nlinarith [Real.exp_pos z.im]
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi * ‖z‖ by positivity)
  have hsqhalf := (sq_lt_sq₀ (by positivity : (0 : ℝ) ≤ Real.exp z.im / 2)
    hroot.le).mpr hhalf
  have hsq : (Real.exp z.im) ^ 2 < 32 * ‖z‖ := by
    nlinarith [Real.pi_lt_four, Real.exp_pos z.im]
  have htarget : (Real.exp z.im) ^ 2 < (4 * ‖z‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (norm_nonneg z)]
  exact (sq_lt_sq₀ (Real.exp_pos _).le (by positivity)).mp htarget

theorem principal_one_point_log_strip {z : ℂ} (hJ : J0 z = 1)
    (hz : PrincipalSector z) : z.im < 2 * Real.log (2 + ‖z‖) := by
  have hr := one_point_norm_ge_four z (principalSector_ne_zero hz) hJ
  have hlog : z.im < Real.log (4 * ‖z‖) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr (principal_one_point_exp_im_bound hJ hz)
  have hcomp : Real.log (4 * ‖z‖) ≤ Real.log ((2 + ‖z‖) ^ 2) := by
    apply Real.log_le_log (by positivity)
    nlinarith [sq_nonneg ‖z‖]
  rw [Real.log_pow] at hcomp
  exact hlog.trans_le hcomp

theorem norm_quadrantRep (z : ℂ) : ‖quadrantRep z‖ = ‖z‖ := by
  have hs : ‖quadrantRep z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [quadrantRep, Complex.normSq_apply, sq_abs]
  nlinarith [norm_nonneg z, norm_nonneg (quadrantRep z)]

/-- The logarithmic strip condition used by the local spectral theorem is
proved for the actual roots, with an explicit constant. -/
theorem one_point_logarithmic_strip {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    |z.im| < 2 * Real.log (2 + ‖z‖) := by
  have hl := globalLocalization z hz hJ
  have h := principal_one_point_log_strip (J0_quadrantRep z hJ)
    (quadrantRep_in_principalSector z hl.1 hl.2.1)
  rw [norm_quadrantRep] at h
  exact h

end J0RadialUniqueness
