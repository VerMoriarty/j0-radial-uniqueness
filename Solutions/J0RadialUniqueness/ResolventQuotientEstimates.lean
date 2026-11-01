import Solutions.J0RadialUniqueness.ResolventParameterAnalytic
import Solutions.J0RadialUniqueness.ResolventPrincipalConvolutionBound
import Solutions.J0RadialUniqueness.SpectralSectorLowerBounds

/-! Estimates for the ordinary quotient of the actual compact resolvent
convolution by its actual mass.  The integral identities are valid before any
analytic division is performed.  The final vertical-line and diagonal estimates
use the proved lower bounds for the actual Bessel mean defect. -/

noncomputable section

open MeasureTheory Filter Set

namespace J0RadialUniqueness

def planarResolventBConvolution (r : ℝ) (u : Plane → ℂ) (x : Plane) (lam : ℂ) : ℂ :=
  ∫ y : Plane, planarHelmholtzResolventB r lam y * u (x - y)

/-- The genuine convolution version of `lam² T = G - B`. -/
theorem planarResolventTConvolution_mul_parameter_sq {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane) (lam : ℂ) :
    lam ^ 2 * planarResolventTConvolution r u x lam =
      localConvolution (planarGreenKernel r) u x - planarResolventBConvolution r u x lam := by
  have hiG := planarGreen_integrable_mul hu x hr
  have hiB := planarHelmholtzResolventB_integrable_mul hr lam hu x
  change lam ^ 2 * (∫ y : Plane, planarHelmholtzResolventT r lam y * u (x - y)) = _
  calc
    _ = ∫ y : Plane, lam ^ 2 * (planarHelmholtzResolventT r lam y * u (x - y)) :=
      (integral_const_mul _ _).symm
    _ = ∫ y : Plane, (planarGreenKernel r y : ℂ) * u (x - y) -
        planarHelmholtzResolventB r lam y * u (x - y) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        dsimp only
        rw [← sub_mul, ← planarHelmholtzResolventT_mul_parameter_sq]
        ring)
    _ = _ := by
      rw [integral_sub (by simpa only [Complex.real_smul] using hiG) hiB]
      simp only [localConvolution, planarResolventBConvolution, Complex.real_smul]

/-- Away from the mass zeros, the quotient is exactly the negative B action
divided by the Bessel mean defect when the Green action vanishes. -/
theorem planarResolventTConvolution_div_mass_eq {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0)
    {lam : ℂ} (hlam : lam ≠ 0) (hmass : helmholtzResolventMass r lam ≠ 0) :
    planarResolventTConvolution r u x lam / helmholtzResolventMass r lam =
      -planarResolventBConvolution r u x lam / (1 - J0 ((r : ℂ) * lam)) := by
  have hmul := planarResolventTConvolution_mul_parameter_sq hr hu x lam
  rw [hgreen, zero_sub] at hmul
  have hmassEq := helmholtzResolventMass_mul_parameter_sq r lam
  have hdefect : 1 - J0 ((r : ℂ) * lam) ≠ 0 := by
    rw [← hmassEq]
    exact mul_ne_zero (pow_ne_zero 2 hlam) hmass
  apply (div_eq_div_iff hmass hdefect).2
  rw [← hmassEq]
  calc
    _ = (lam ^ 2 * planarResolventTConvolution r u x lam) *
        helmholtzResolventMass r lam := by ring
    _ = _ := by rw [hmul]

theorem norm_real_mul_parameter {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    ‖(r : ℂ) * lam‖ = r * ‖lam‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- Cancellation of the square-root radial factor against the parameter norm. -/
theorem sqrt_scaled_parameter_div_norm {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Real.sqrt (2 * Real.pi * ‖(r : ℂ) * lam‖) / ‖lam‖ =
      Real.sqrt (2 * Real.pi * r) / Real.sqrt ‖lam‖ := by
  rw [norm_real_mul_parameter hr,
    show 2 * Real.pi * (r * ‖lam‖) = (2 * Real.pi * r) * ‖lam‖ by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * r)]
  rw [mul_div_assoc, Real.sqrt_div_self]
  rfl

/-- Real algebra used to combine the exponential numerator and denominator
estimates, without losing the square-root decay. -/
theorem quotient_bound_of_exponential_denominator {B C E D L d : ℝ}
    (hC : 0 ≤ C) (hE : 0 < E) (hD : 0 < D) (hL : 0 < L)
    (hB : B ≤ C * E / L) (hden : (1 + E / D) / 4 ≤ d) :
    B / d ≤ 4 * C * D / L := by
  have hd : 0 < d := lt_of_lt_of_le (by positivity) hden
  have hED : E / D ≤ 4 * d := by linarith
  have hEcross : E ≤ 4 * D * d := by
    have h := (div_le_iff₀ hD).mp hED
    nlinarith
  apply (div_le_iff₀ hd).2
  calc
    B ≤ C * E / L := hB
    _ ≤ C * (4 * D * d) / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEcross hC) hL.le
    _ = (4 * C * D / L) * d := by ring

/-- A conditional numerical step. The two final geometric wrappers below supply
its denominator premise from the actual Bessel estimates. -/
theorem planarResolventTConvolution_div_mass_bound_of_defect_lower
    {r : ℝ} (hr : 0 < r) {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0)
    {C : ℝ} (hC : 0 ≤ C) {lam : ℂ} (hL : 1 ≤ ‖lam‖)
    (hB : ‖planarResolventBConvolution r u x lam‖ ≤ C * Real.exp (r * lam.im) / ‖lam‖)
    (hden : (1 + Real.exp (((r : ℂ) * lam).im) /
      Real.sqrt (2 * Real.pi * ‖(r : ℂ) * lam‖)) / 4 ≤
        ‖1 - J0 ((r : ℂ) * lam)‖) :
    ‖planarResolventTConvolution r u x lam / helmholtzResolventMass r lam‖ ≤
      4 * C * Real.sqrt (2 * Real.pi * r) / Real.sqrt ‖lam‖ := by
  have hLpos : 0 < ‖lam‖ := by linarith
  have hlam : lam ≠ 0 := norm_pos_iff.mp hLpos
  have hρpos : 0 < ‖(r : ℂ) * lam‖ := by
    rw [norm_real_mul_parameter hr]
    exact mul_pos hr hLpos
  have hD : 0 < Real.sqrt (2 * Real.pi * ‖(r : ℂ) * lam‖) := by positivity
  have hexp : Real.exp (((r : ℂ) * lam).im) = Real.exp (r * lam.im) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hdefpos : 0 < ‖1 - J0 ((r : ℂ) * lam)‖ :=
    lt_of_lt_of_le (by positivity) hden
  have hdef : 1 - J0 ((r : ℂ) * lam) ≠ 0 := norm_pos_iff.mp hdefpos
  have hmass : helmholtzResolventMass r lam ≠ 0 := by
    intro hzero
    apply hdef
    rw [← helmholtzResolventMass_mul_parameter_sq, hzero, mul_zero]
  rw [planarResolventTConvolution_div_mass_eq hr hu x hgreen hlam hmass,
    norm_div, norm_neg]
  have hbound := quotient_bound_of_exponential_denominator hC
    (Real.exp_pos (((r : ℂ) * lam).im)) hD hLpos
    (by simpa only [hexp] using hB) hden
  calc
    _ ≤ 4 * C * Real.sqrt (2 * Real.pi * ‖(r : ℂ) * lam‖) / ‖lam‖ := hbound
    _ = 4 * C * Real.sqrt (2 * Real.pi * r) / Real.sqrt ‖lam‖ := by
      calc
        _ = 4 * C * (Real.sqrt (2 * Real.pi * ‖(r : ℂ) * lam‖) / ‖lam‖) := by ring
        _ = _ := by rw [sqrt_scaled_parameter_div_norm hr]; ring

/-- Uniform decay of the actual ordinary quotient on the specified vertical
lines in the closed principal sector. All denominator bounds are discharged. -/
theorem planarResolventTConvolution_div_mass_vertical_bound {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ, ClosedPrincipalSector lam → 1 ≤ ‖lam‖ →
      ∀ n : ℕ, (((r : ℂ) * lam).re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4) →
      256 ≤ r * ‖lam‖ →
      ‖planarResolventTConvolution r u x lam / helmholtzResolventMass r lam‖ ≤
        4 * C * Real.sqrt (2 * Real.pi * r) / Real.sqrt ‖lam‖ := by
  obtain ⟨C, hC, hB⟩ := resolventB_principal_convolution_bound hu x hr
  refine ⟨C, hC, ?_⟩
  intro lam hlam hL n hline hρ
  apply planarResolventTConvolution_div_mass_bound_of_defect_lower hr hu x hgreen hC.le hL
  · simpa only [planarResolventBConvolution, planarHelmholtzResolventB] using hB lam hlam hL
  · exact spectral_vertical_bound (closedPrincipalSector_pos_scale hlam hr) n hline
      (by simpa only [norm_real_mul_parameter hr] using hρ)

/-- On the positive diagonal the actual dominant exponential exceeds the
required threshold. The fixed cutoff is deliberately generous. -/
theorem diagonal_spectral_large_magnitude {z : ℂ}
    (hz : ClosedPrincipalSector z) (hdiag : z.im = z.re)
    (hρ : (10000 : ℝ) ≤ ‖z‖) :
    (2 : ℝ) ≤ z.im ∧
      4 ≤ Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖) := by
  have hnorm : ‖z‖ ≤ 2 * z.im := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz.2.2, abs_of_nonneg hz.1, ← hdiag] at h
    linarith
  have hy16 : (16 : ℝ) ≤ z.im := by linarith
  have hR8 : (8 : ℝ) ≤ ‖z‖ := by linarith
  have hRpos : 0 < ‖z‖ := by linarith
  have hysq := mul_nonneg hz.1 (sub_nonneg.mpr hy16)
  have he := Real.quadratic_le_exp_of_nonneg hz.1
  have hexp : 4 * ‖z‖ ≤ Real.exp z.im := by nlinarith
  have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg z)
  have hRsq := mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hR8)
  have hsqrt : Real.sqrt (2 * Real.pi * ‖z‖) ≤ ‖z‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨norm_nonneg z, ?_⟩
    nlinarith
  have hden : 0 < Real.sqrt (2 * Real.pi * ‖z‖) :=
    Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) hRpos)
  refine ⟨by linarith, (le_div_iff₀ hden).2 ?_⟩
  nlinarith only [hsqrt, hexp]

/-- The denominator estimate on the positive diagonal has no extra amplitude
or growth premise. -/
theorem spectral_positive_diagonal_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    (hdiag : z.im = z.re) (hρ : (10000 : ℝ) ≤ ‖z‖) :
    (1 + Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) / 4 ≤ ‖1 - J0 z‖ := by
  obtain ⟨hy, hlarge⟩ := diagonal_spectral_large_magnitude hz hdiag hρ
  exact spectral_high_magnitude_bound hz (by linarith) hy hlarge

/-- Uniform square-root decay on the actual positive principal diagonal. -/
theorem planarResolventTConvolution_div_mass_positive_diagonal_bound
    {r : ℝ} (hr : 0 < r) {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ, ClosedPrincipalSector lam → 1 ≤ ‖lam‖ →
      (((r : ℂ) * lam).im = ((r : ℂ) * lam).re) → 10000 ≤ r * ‖lam‖ →
      ‖planarResolventTConvolution r u x lam / helmholtzResolventMass r lam‖ ≤
        4 * C * Real.sqrt (2 * Real.pi * r) / Real.sqrt ‖lam‖ := by
  obtain ⟨C, hC, hB⟩ := resolventB_principal_convolution_bound hu x hr
  refine ⟨C, hC, ?_⟩
  intro lam hlam hL hdiag hρ
  apply planarResolventTConvolution_div_mass_bound_of_defect_lower hr hu x hgreen hC.le hL
  · simpa only [planarResolventBConvolution, planarHelmholtzResolventB] using hB lam hlam hL
  · exact spectral_positive_diagonal_bound (closedPrincipalSector_pos_scale hlam hr) hdiag
      (by simpa only [norm_real_mul_parameter hr] using hρ)

/-- A single uniform bound on the large-parameter parts of the two geometric
boundaries. This follows from the sharper decay estimates above. -/
theorem planarResolventTConvolution_div_mass_geometric_uniform_bound
    {r : ℝ} (hr : 0 < r) {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ lam : ℂ, ClosedPrincipalSector lam → 1 ≤ ‖lam‖ →
      ((∃ n : ℕ, ((r : ℂ) * lam).re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4 ∧
          256 ≤ r * ‖lam‖) ∨
        (((r : ℂ) * lam).im = ((r : ℂ) * lam).re ∧ 10000 ≤ r * ‖lam‖)) →
      ‖planarResolventTConvolution r u x lam / helmholtzResolventMass r lam‖ ≤ K := by
  obtain ⟨C, hC, hB⟩ := resolventB_principal_convolution_bound hu x hr
  let K : ℝ := 4 * C * Real.sqrt (2 * Real.pi * r)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro lam hlam hL hgeometry
  have hden : (1 + Real.exp (((r : ℂ) * lam).im) /
      Real.sqrt (2 * Real.pi * ‖(r : ℂ) * lam‖)) / 4 ≤
        ‖1 - J0 ((r : ℂ) * lam)‖ := by
    rcases hgeometry with ⟨n, hline, hρ⟩ | ⟨hdiag, hρ⟩
    · exact spectral_vertical_bound (closedPrincipalSector_pos_scale hlam hr) n hline
        (by simpa only [norm_real_mul_parameter hr] using hρ)
    · exact spectral_positive_diagonal_bound (closedPrincipalSector_pos_scale hlam hr) hdiag
        (by simpa only [norm_real_mul_parameter hr] using hρ)
  have hdecay := planarResolventTConvolution_div_mass_bound_of_defect_lower hr hu x hgreen
    hC.le hL (by
      simpa only [planarResolventBConvolution, planarHelmholtzResolventB] using hB lam hlam hL) hden
  have hroot : (1 : ℝ) ≤ Real.sqrt ‖lam‖ := Real.le_sqrt_of_sq_le (by simpa using hL)
  exact hdecay.trans (div_le_self hK.le hroot)

end J0RadialUniqueness
