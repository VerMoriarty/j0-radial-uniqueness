import Solutions.J0RadialUniqueness.EvenPoissonPolynomialRecovery
import Solutions.J0RadialUniqueness.AbelVolterraInjectivity
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! Actual injectivity of the centered Poisson mean for even functions.
The angular integral is first paired into a quadrant and then converted by
the proved sin² Jacobian. A clipped divided difference supplies the globally
continuous density required by the actual Abel injectivity theorem. Only
continuity on [-1,1] and differentiability at zero are used in injectivity. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Interval ContDiff

namespace J0RadialUniqueness

def unitSqrtClip (s : ℝ) : ℝ := Real.sqrt (max 0 (min s 1))

theorem continuous_unitSqrtClip : Continuous unitSqrtClip :=
  (continuous_const.max (continuous_id.min continuous_const)).sqrt

theorem unitSqrtClip_mem_unit (s : ℝ) : unitSqrtClip s ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩⟩
  simpa only [one_pow] using max_le (by norm_num : (0 : ℝ) ≤ 1) (min_le_right s 1)

theorem unitSqrtClip_of_mem_unit {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : unitSqrtClip s = Real.sqrt s := by
  simp only [unitSqrtClip, min_eq_left hs.2, max_eq_right hs.1]

def evenPoissonAbelDensity (h : ℝ → ℂ) (s : ℝ) : ℂ := dslope h 0 (unitSqrtClip s)

theorem continuous_evenPoissonAbelDensity {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) (hd : DifferentiableAt ℝ h 0) :
    Continuous (evenPoissonAbelDensity h) := by
  have hds : ContinuousOn (dslope h 0) (Icc (0 : ℝ) 1) := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hne
    · exact (continuousAt_dslope_same.mpr hd).continuousWithinAt
    · apply (continuousWithinAt_dslope_of_ne hne).mpr
      exact (hh.mono (fun y hy => ⟨by linarith [hy.1], hy.2⟩)) x hx
  exact hds.comp_continuous continuous_unitSqrtClip unitSqrtClip_mem_unit

theorem continuous_evenPoisson_clipped_numerator {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) : Continuous (fun s : ℝ => h (unitSqrtClip s)) := by
  apply hh.comp_continuous continuous_unitSqrtClip
  intro s
  have hs := unitSqrtClip_mem_unit s
  exact ⟨by linarith [hs.1], hs.2⟩

/-- The full actual circular integral is four times its quadrant integral for
an even numerator. All splitting integrals are genuinely integrable. -/
theorem integral_even_poisson_four_quadrants {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) (heven : Function.Even h)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), h (t * Real.cos θ)) =
      (4 : ℝ) • ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (t * Real.cos θ) := by
  let F : ℝ → ℂ := fun θ => h (t * Real.cos θ)
  have hF : Continuous F := continuous_evenPoisson_integrand_on_unit_interval hh ht
  have hp : Function.Periodic F Real.pi := by
    intro θ
    dsimp only [F]
    rw [Real.cos_add_pi, mul_neg, heven (t * Real.cos θ)]
  have hshift : (∫ θ : ℝ in Real.pi..(2 * Real.pi), F θ) = ∫ θ : ℝ in (0 : ℝ)..Real.pi, F θ := by
    simpa only [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] using
      hp.intervalIntegral_add_eq Real.pi 0
  have href (θ : ℝ) : F (Real.pi - θ) = F θ := by
    dsimp only [F]
    rw [Real.cos_pi_sub, mul_neg, heven (t * Real.cos θ)]
  have hreflection : (∫ θ : ℝ in (Real.pi / 2)..Real.pi, F θ) =
      ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ := by
    simpa only [href, sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] using
      (intervalIntegral.integral_comp_sub_left F (a := (0 : ℝ)) (b := Real.pi / 2) Real.pi).symm
  have hhalf := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (μ := volume) 0 (Real.pi / 2))
    (hF.intervalIntegrable (μ := volume) (Real.pi / 2) Real.pi)
  rw [hreflection] at hhalf
  have hfull := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (μ := volume) 0 Real.pi)
    (hF.intervalIntegrable (μ := volume) Real.pi (2 * Real.pi))
  rw [hshift] at hfull
  change (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ) =
    (4 : ℝ) • ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ
  simp only [Complex.real_smul, Complex.ofReal_ofNat]
  linear_combination -hfull - (2 : ℂ) * hhalf

theorem evenPoissonTransform_eq_quarter_sin {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) (heven : Function.Even h)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    evenPoissonTransform h t = (2 / Real.pi : ℝ) •
      ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (t * Real.sin θ) := by
  have hswitch : (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (t * Real.cos θ)) =
      ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (t * Real.sin θ) := by
    have hh' := intervalIntegral.integral_comp_sub_left (fun θ : ℝ => h (t * Real.cos θ))
      (a := (0 : ℝ)) (b := Real.pi / 2) (Real.pi / 2)
    simpa only [Real.cos_pi_div_two_sub, sub_self, sub_zero] using hh'.symm
  rw [evenPoissonTransform_eq_integral, integral_even_poisson_four_quadrants hh heven ht, hswitch,
    smul_smul]
  congr 1
  field_simp [Real.pi_ne_zero] <;> ring

theorem evenPoissonAbelDensity_eq_of_pos {h : ℝ → ℂ} (hzero : h 0 = 0)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    evenPoissonAbelDensity h s = (Real.sqrt s)⁻¹ • h (Real.sqrt s) := by
  have hsqrt : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs.1).ne'
  unfold evenPoissonAbelDensity
  rw [unitSqrtClip_of_mem_unit ⟨hs.1.le, hs.2.le⟩, dslope_of_ne h hsqrt, slope_def_module,
    sub_zero, hzero, sub_zero]

/-- The actual sin² substitution converts zero centered means into the first
Abel transform with kernel one. Its numerator is globally extended only by a
continuous clipping which agrees at every point used by the integral. -/
theorem evenPoisson_zero_means_imply_abel_zero {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) (heven : Function.Even h)
    (hzero : h 0 = 0)
    (hmean : ∀ t ∈ Icc (0 : ℝ) 1, evenPoissonTransform h t = 0) :
    ∀ p ∈ Icc (0 : ℝ) 1,
      (∫ s : ℝ in (0 : ℝ)..p, (Real.sqrt (p - s))⁻¹ • ((1 : ℂ) * evenPoissonAbelDensity h s)) = 0 := by
  intro p hp
  rcases eq_or_lt_of_le hp.1 with rfl | hp0
  · exact intervalIntegral.integral_same
  have ht : Real.sqrt p ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa only [one_pow] using hp.2⟩⟩
  have hQ : (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (Real.sqrt p * Real.sin θ)) = 0 := by
    have hz : (2 / Real.pi : ℝ) •
        (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (Real.sqrt p * Real.sin θ)) = 0 :=
      (evenPoissonTransform_eq_quarter_sin hh heven ht).symm.trans (hmean _ ht)
    exact (smul_eq_zero.mp hz).resolve_left (by positivity : (2 / Real.pi : ℝ) ≠ 0)
  have hBeta := abelBetaDensity_weighted_integrable_and_integral hp0
    (continuous_evenPoisson_clipped_numerator hh)
  have hBetaEq : (∫ s : ℝ in Ioo (0 : ℝ) p,
      abelBetaDensity p 0 s • h (unitSqrtClip s)) =
      (2 : ℝ) • ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (unitSqrtClip (abelAngleScalar p 0 θ)) := by
    convert! hBeta.2 using 1 <;> rfl
  have hangular : (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
      h (unitSqrtClip (abelAngleScalar p 0 θ))) =
      ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (Real.sqrt p * Real.sin θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have ha : p * Real.sin θ ^ 2 ∈ Icc (0 : ℝ) 1 := by
      have hm := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one θ) hp.1
      exact ⟨mul_nonneg hp.1 (sq_nonneg _), by nlinarith [hp.2]⟩
    dsimp only
    simp only [abelAngleScalar, sub_zero, zero_add]
    rw [unitSqrtClip_of_mem_unit ha, Real.sqrt_mul hp.1, Real.sqrt_sq_eq_abs, abs_of_nonneg hsin]
  have hBetaZero : (∫ s : ℝ in Ioo (0 : ℝ) p,
      abelBetaDensity p 0 s • h (unitSqrtClip s)) = 0 := by
    rw [hBetaEq, hangular, hQ, smul_zero]
  rw [intervalIntegral.integral_of_le hp.1, integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ s : ℝ in Ioo (0 : ℝ) p, abelBetaDensity p 0 s • h (unitSqrtClip s) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans_le hp.2⟩
      dsimp only
      rw [one_mul, evenPoissonAbelDensity_eq_of_pos hzero hs1,
        unitSqrtClip_of_mem_unit ⟨hs1.1.le, hs1.2.le⟩]
      simp only [abelBetaDensity, sub_zero, smul_smul]
    _ = 0 := hBetaZero

/-- Actual injectivity: evenness, continuity on the sampled interval, and one
central derivative suffice. There is no global smoothness hypothesis. -/
theorem evenPoissonTransform_injective_on_unit_interval {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) (heven : Function.Even h)
    (hd : DifferentiableAt ℝ h 0)
    (hmean : ∀ t ∈ Icc (0 : ℝ) 1, evenPoissonTransform h t = 0) :
    ∀ x ∈ Icc (-1 : ℝ) 1, h x = 0 := by
  have hzero : h 0 = 0 := by
    simpa only [evenPoissonTransform_zero] using hmean 0 ⟨le_refl 0, by norm_num⟩
  have hv := abelVolterraInjectivity_global (K := fun _ : ℝ × ℝ => (1 : ℂ)) contDiff_const
    (continuous_evenPoissonAbelDensity hh hd) (by norm_num : (0 : ℝ) < 1)
    (fun _ _ => one_ne_zero) (evenPoisson_zero_means_imply_abel_zero hh heven hzero hmean)
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : h x = 0 := by
    have hx2 : x ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [hx.1, hx.2]⟩
    have hz := hv (x ^ 2) hx2
    simp only [evenPoissonAbelDensity, unitSqrtClip_of_mem_unit hx2, Real.sqrt_sq hx.1] at hz
    have hrec := sub_smul_dslope_of_zero hzero x
    rw [sub_zero, hz, smul_zero] at hrec
    exact hrec.symm
  intro x hx
  rcases le_total 0 x with hxp | hxn
  · exact hpos x ⟨hxp, hx.2⟩
  · rw [← heven x]
    exact hpos (-x) ⟨by linarith, by linarith [hx.1]⟩

/-- Complete recovery with the explicit inverse-moment polynomial. -/
theorem evenPoissonPolynomialRecovery_of_differentiable {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) (heven : Function.Even h)
    (hd : DifferentiableAt ℝ h 0) (K : Polynomial ℂ)
    (hmean : ∀ t ∈ Icc (0 : ℝ) 1, evenPoissonTransform h t = K.eval ((t : ℂ) ^ 2)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, h x = (evenPoissonInversePolynomial K).eval (x : ℂ) := by
  let d : ℝ → ℂ := fun x => h x - (evenPoissonInversePolynomial K).eval (x : ℂ)
  have hPc : Continuous (fun x : ℝ => (evenPoissonInversePolynomial K).eval (x : ℂ)) :=
    (evenPoissonInversePolynomial K).continuous.comp Complex.continuous_ofReal
  have hPs : ContDiff ℝ 1 (fun z : ℂ => (evenPoissonInversePolynomial K).eval z) := by
    convert! (((evenPoissonInversePolynomial K).contDiff_aeval (𝕜 := ℂ) 1).restrict_scalars ℝ) using 1 <;> rfl
  have hPd : DifferentiableAt ℝ (fun x : ℝ => (evenPoissonInversePolynomial K).eval (x : ℂ)) 0 :=
    ((hPs.comp Complex.ofRealCLM.contDiff).differentiable one_ne_zero).differentiableAt
  have hdcont : ContinuousOn d (Icc (-1 : ℝ) 1) := hh.sub hPc.continuousOn
  have hdeven : Function.Even d := evenPoisson_polynomial_difference_even heven K
  have hddiff : DifferentiableAt ℝ d 0 := hd.sub hPd
  have hdmean : ∀ t ∈ Icc (0 : ℝ) 1, evenPoissonTransform d t = 0 :=
    evenPoisson_polynomial_mean_difference_zero hh K hmean
  intro x hx
  exact sub_eq_zero.mp (evenPoissonTransform_injective_on_unit_interval hdcont hdeven hddiff hdmean x hx)

/-- The requested local finite-C² interface. The regularity is used only on
the stated real neighborhood; no analytic or global C∞ extension is assumed. -/
theorem evenPoissonPolynomialRecovery_of_contDiffOn {h : ℝ → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hh : ContDiffOn ℝ 2 h (Ioo (-1 - ε) (1 + ε)))
    (heven : Function.Even h) (K : Polynomial ℂ)
    (hmean : ∀ t ∈ Icc (0 : ℝ) 1, evenPoissonTransform h t = K.eval ((t : ℂ) ^ 2)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, h x = (evenPoissonInversePolynomial K).eval (x : ℂ) := by
  have hsub : Icc (-1 : ℝ) 1 ⊆ Ioo (-1 - ε) (1 + ε) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h0 : (0 : ℝ) ∈ Ioo (-1 - ε) (1 + ε) := ⟨by linarith, by linarith⟩
  have hd : DifferentiableAt ℝ h 0 :=
    (hh.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds h0)
  exact evenPoissonPolynomialRecovery_of_differentiable (hh.continuousOn.mono hsub) heven hd K hmean

theorem exists_evenPolynomial_of_polynomial_poisson_mean {h : ℝ → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hh : ContDiffOn ℝ 2 h (Ioo (-1 - ε) (1 + ε)))
    (heven : Function.Even h) (K : Polynomial ℂ)
    (hmean : ∀ t ∈ Icc (0 : ℝ) 1, evenPoissonTransform h t = K.eval ((t : ℂ) ^ 2)) :
    ∃ H : Polynomial ℂ, Function.Even (fun z : ℂ => H.eval z) ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, h x = H.eval (x : ℂ) := by
  exact ⟨evenPoissonInversePolynomial K, evenPoissonInversePolynomial_even K,
    evenPoissonPolynomialRecovery_of_contDiffOn hε hh heven K hmean⟩

end J0RadialUniqueness
