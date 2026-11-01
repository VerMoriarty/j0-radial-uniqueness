import Solutions.J0RadialUniqueness.AmplitudeUniform
import Solutions.J0RadialUniqueness.NumericalBounds
import Solutions.J0RadialUniqueness.Conditional.RaySeparation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

theorem norm_half_power_denominator (z : ℂ) :
    ‖Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)‖ =
      Real.sqrt (2 * Real.pi * ‖z‖) := by
  have hc : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hc, Complex.cpow_eq_pow, Complex.norm_cpow_real]
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  exact (Real.sqrt_eq_rpow _).symm

theorem one_point_sqrt_bound_of_exact (hexact : ExactDecompositionStatement)
    {z : ℂ} (hJ : J0 z = 1) (hz : PrincipalSector z) :
    Real.sqrt (2 * Real.pi * ‖z‖) ≤
      (17 / 16 : ℝ) * (Real.exp z.im + Real.exp (-z.im)) := by
  have hr := one_point_norm_ge_four z (principalSector_ne_zero hz) hJ
  obtain ⟨_, hp, _, hm, _, _⟩ := amplitude_modulus_bounds z (principalSector_closed hz) hr
  have he := congrArg (fun u : ℂ => u *
      Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ))
    (hexact z (lt_trans hz.1 hz.2))
  have hden : Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (principalSector_ne_zero hz)
  rw [hJ, one_mul, div_mul_cancel₀ _ hden] at he
  have h := norm_add_le
    (Complex.exp (Complex.I * (z - (Real.pi : ℂ) / 4)) * APlus z)
    (Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4)) * AMinus z)
  rw [← he, norm_half_power_denominator] at h
  have he1 : ‖Complex.exp (Complex.I * (z - (Real.pi : ℂ) / 4))‖ =
      Real.exp (-z.im) := by rw [Complex.norm_exp]; congr 1; simp
  have he2 : ‖Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4))‖ =
      Real.exp z.im := by rw [Complex.norm_exp]; congr 1; simp
  simp only [norm_mul, he1, he2] at h
  calc
    _ ≤ Real.exp (-z.im) * ‖APlus z‖ + Real.exp z.im * ‖AMinus z‖ := h
    _ ≤ Real.exp (-z.im) * (17 / 16) + Real.exp z.im * (17 / 16) :=
      add_le_add (mul_le_mul_of_nonneg_left hp.le (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left hm.le (Real.exp_pos _).le)
    _ = _ := by ring

theorem quantitativeSeparation_of_exact (hexact : ExactDecompositionStatement) :
    QuantitativeSeparationStatement := by
  intro z hJ hz
  have hr := one_point_norm_ge_four z (principalSector_ne_zero hz) hJ
  obtain ⟨hpl, hpu, hml, hmu, _, _⟩ :=
    amplitude_modulus_bounds z (principalSector_closed hz) hr
  have hdomain : z ∈ amplitudeDomain := by
    refine ⟨lt_trans hz.1 hz.2, mul_ne_zero ?_ ?_⟩ <;>
      apply norm_pos_iff.mp
    · linarith
    · linarith
  have hs := one_point_sqrt_bound_of_exact hexact hJ hz
  have hsqrt : Real.sqrt (8 * Real.pi) ≤ Real.sqrt (2 * Real.pi * ‖z‖) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hcosh : (11 / 5 : ℝ) < Real.cosh z.im := by
    rw [Real.cosh_eq]
    linarith [weighted_sqrt_eight_pi_gt_eleven_fifths]
  have hy : (7 / 5 : ℝ) < z.im := by
    by_contra hn
    have hm := Real.cosh_strictMonoOn.monotoneOn hz.1.le
      (by norm_num : (0 : ℝ) ≤ 7 / 5) (le_of_not_gt hn)
    linarith [cosh_seven_fifths_lt_eleven_fifths]
  have he : Real.exp (-2 * z.im) < (1 / 16 : ℝ) := by
    have h16 : (16 : ℝ) < Real.exp (2 * z.im) :=
      exp_fourteen_fifths_gt_sixteen.trans (Real.exp_lt_exp.mpr (by linarith))
    rw [show -2 * z.im = -(2 * z.im) by ring, Real.exp_neg]
    exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; exact h16)
  have hd : ‖delta z‖ < (17 / 240 : ℝ) := by
    rw [norm_delta]
    exact delta_lt_of_amplitudes (Real.exp_pos _).le he hpu hml
  have hexp : (Real.exp z.im)⁻¹ = Real.exp (-z.im) := (Real.exp_neg _).symm
  have hdecay : (Real.sqrt (2 * Real.pi * ‖z‖) * Real.exp (-z.im)) ≤
      (17 / 16 : ℝ) * (17 / 16) := by
    have hh := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-z.im)).le
    have heq : (Real.exp z.im + Real.exp (-z.im)) * Real.exp (-z.im) =
        1 + Real.exp (-2 * z.im) := by
      rw [add_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1 <;> ring_nf <;> simp
    calc
      _ ≤ (17 / 16) * ((Real.exp z.im + Real.exp (-z.im)) * Real.exp (-z.im)) := by
        simpa only [mul_assoc] using hh
      _ = (17 / 16) * (1 + Real.exp (-2 * z.im)) := by rw [heq]
      _ ≤ (17 / 16) * (17 / 16) := by linarith
  have hsq := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    (by norm_num : (0 : ℝ) ≤ (17 / 16) * (17 / 16))).mpr hdecay
  have hpow : (Real.sqrt (2 * Real.pi * ‖z‖) * Real.exp (-z.im)) ^ 2 =
      2 * Real.pi * (‖z‖ * Real.exp (-2 * z.im)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), pow_two, ← Real.exp_add]
    rw [show -z.im + -z.im = -2 * z.im by ring]
    ring
  rw [hpow] at hsq
  have hprod : 0 ≤ ‖z‖ * Real.exp (-2 * z.im) := by positivity
  have hre : ‖z‖ * Real.exp (-2 * z.im) < (11 / 50 : ℝ) := by
    nlinarith [Real.pi_gt_three]
  exact ⟨hdomain, hy, he, hd, hre⟩

end J0RadialUniqueness
