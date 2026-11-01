import Definitions.J0RadialUniqueness.Analytic
import Solutions.J0RadialUniqueness.Constants
import Solutions.J0RadialUniqueness.ZeroFree
import Solutions.J0RadialUniqueness.Conditional.RadialCalculus
import Mathlib.Analysis.Complex.Trigonometric

/-! Propagation along the actual outward ray, conditional only on the stated
initial separation, amplitude bounds, and exact factorization. -/

noncomputable section

namespace J0RadialUniqueness

/-- This identity is valid even if either amplitude vanishes. -/
theorem norm_delta (z : ℂ) :
    ‖delta z‖ = Real.exp (-2 * z.im) * (‖APlus z‖ / ‖AMinus z‖) := by
  unfold delta
  rw [norm_div, norm_mul, Complex.norm_exp]
  have hre : (2 * Complex.I * (z - (Real.pi : ℂ) / 4)).re = -2 * z.im := by
    simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hre]
  ring

theorem principalSector_real_mul {z : ℂ} {τ : ℝ}
    (hτ : 0 < τ) (hz : PrincipalSector z) : PrincipalSector ((τ : ℂ) * z) := by
  constructor
  · simpa [Complex.mul_im] using mul_pos hτ hz.1
  · simpa [Complex.mul_im, Complex.mul_re] using mul_lt_mul_of_pos_left hz.2 hτ

theorem principalSector_closed {z : ℂ} (hz : PrincipalSector z) :
    ClosedPrincipalSector z :=
  ⟨hz.1.le, hz.2.le, lt_trans hz.1 hz.2⟩

theorem principalSector_ne_zero {z : ℂ} (hz : PrincipalSector z) : z ≠ 0 := by
  intro he
  have hi := hz.1
  simpa [he] using hi

/-- The entire ray remains in the amplitude domain, the decaying term remains small,
and the actual Bessel function has no zero on the outward ray. -/
theorem raySeparation_of_initial_amplitudes_factorization
    (hsep : QuantitativeSeparationStatement)
    (hamp : AmplitudeModulusBoundsStatement)
    (hfact : FactorizationStatement) : RaySeparationStatement := by
  intro z hJ hz τ hτ
  let w : ℂ := (τ : ℂ) * z
  change w ∈ amplitudeDomain ∧ ‖delta w‖ < 17 / 240 ∧
    ‖w‖ * ‖delta w‖ < 187 / 750 ∧ J0 w ≠ 0
  have hτ0 : 0 < τ := by linarith
  have hwsector : PrincipalSector w := principalSector_real_mul hτ0 hz
  have hnorm : ‖w‖ = τ * ‖z‖ := by
    change ‖(τ : ℂ) * z‖ = τ * ‖z‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]
  have him : w.im = τ * z.im := by simp [w, Complex.mul_im]
  have hrbase : 4 ≤ ‖z‖ := one_point_norm_ge_four z (principalSector_ne_zero hz) hJ
  have hr : 4 ≤ ‖w‖ := by
    rw [hnorm]
    nlinarith [norm_nonneg z]
  obtain ⟨_, hybase, hebase, _, hrebase⟩ := hsep z hJ hz
  have he : Real.exp (-2 * w.im) < (1 / 16 : ℝ) := by
    rw [him]
    exact outward_exp_bound hτ hz.1.le hebase
  have hre : ‖w‖ * Real.exp (-2 * w.im) < (11 / 50 : ℝ) := by
    rw [hnorm, him]
    exact outward_rho_exp_eleven_fiftieths hτ (norm_nonneg z) hybase hrebase
  obtain ⟨hpl, hpu, hml, _, _, _⟩ := hamp w (principalSector_closed hwsector) hr
  have hp0 : APlus w ≠ 0 :=
    norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 15 / 16) hpl)
  have hm0 : AMinus w ≠ 0 :=
    norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 15 / 16) hml)
  have hdomain : w ∈ amplitudeDomain :=
    ⟨lt_trans hwsector.1 hwsector.2, mul_ne_zero hp0 hm0⟩
  have hd : ‖delta w‖ < (17 / 240 : ℝ) := by
    rw [norm_delta]
    exact delta_lt_of_amplitudes (Real.exp_pos _).le he hpu hml
  have hrd : ‖w‖ * ‖delta w‖ < (187 / 750 : ℝ) := by
    rw [norm_delta]
    exact weighted_delta_lt_of_amplitudes (norm_nonneg w) (Real.exp_pos _).le hre hpu hml
  have hDbase : 2 * (Real.pi : ℂ) * w ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)))
      (principalSector_ne_zero hwsector)
  have hD : Complex.cpow (2 * (Real.pi : ℂ) * w) (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hDbase)
  have hJnonzero : J0 w ≠ 0 := by
    rw [hfact w hdomain]
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hm0) hD)
      (one_add_ne_zero_of_norm_lt hd)
  exact ⟨hdomain, hd, hrd, hJnonzero⟩

end J0RadialUniqueness
