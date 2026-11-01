import Solutions.J0RadialUniqueness.HelmholtzCircularMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Fourier.AddCircle
import Solutions.J0RadialUniqueness.PlaneHarmonicMeanValue

/-! Radial-mode foundations for unique continuation of a smooth Helmholtz
solution. The energy estimate below applies on positive intervals with bounded
variable coefficients. No analytic regularity or unique continuation theorem
is a hypothesis of these results. -/

noncomputable section

open MeasureTheory Set Filter Laplacian
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

/-- Zero initial data propagate for a complex second-order equation whose two
coefficients are bounded on an ordinary compact interval. -/
theorem boundedComplexODE_zero_of_initial_zero
    (u v A B : ℝ → ℂ) {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (v t) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (A t * u t + B t * v t) t)
    (hA : ∀ t ∈ Ioo a b, ‖A t‖ ≤ M)
    (hB : ∀ t ∈ Ioo a b, ‖B t‖ ≤ M)
    (hua : u a = 0) (hva : v a = 0) :
    ∀ t ∈ Icc a b, u t = 0 ∧ v t = 0 := by
  let C : ℝ := 1 + 3 * M
  let E : ℝ → ℝ := fun t => ‖u t‖ ^ 2 + ‖v t‖ ^ 2
  let D : ℝ → ℝ := fun t => 2 * inner ℝ (u t) (v t) +
    2 * inner ℝ (v t) (A t * u t + B t * v t)
  let W : ℝ → ℝ := fun t => Real.exp (-C * t) * E t
  have hE (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt E (D t) t :=
    (hdu t ht).norm_sq.add (hdv t ht).norm_sq
  have hD (t : ℝ) (ht : t ∈ Ioo a b) : D t ≤ C * E t := by
    have hi₁ := real_inner_le_norm (u t) (v t)
    have hi₂ : inner ℝ (v t) (A t * u t) ≤ ‖v t‖ * (‖A t‖ * ‖u t‖) := by
      simpa only [norm_mul] using real_inner_le_norm (v t) (A t * u t)
    have hi₃ : inner ℝ (v t) (B t * v t) ≤ ‖v t‖ * (‖B t‖ * ‖v t‖) := by
      simpa only [norm_mul] using real_inner_le_norm (v t) (B t * v t)
    have hAuv := mul_le_mul_of_nonneg_right (hA t ht)
      (mul_nonneg (norm_nonneg (u t)) (norm_nonneg (v t)))
    have hBvv := mul_le_mul_of_nonneg_right (hB t ht) (sq_nonneg ‖v t‖)
    have hcross : 2 * ‖u t‖ * ‖v t‖ ≤ ‖u t‖ ^ 2 + ‖v t‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖u t‖ - ‖v t‖)]
    have hcrossM := mul_le_mul_of_nonneg_left hcross hM
    have hMu := mul_nonneg hM (sq_nonneg ‖u t‖)
    dsimp only [D, C, E]
    rw [inner_add_right]
    nlinarith only [hi₁, hi₂, hi₃, hAuv, hBvv, hcross, hcrossM, hMu]
  have hW (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt W (Real.exp (-C * t) * (D t - C * E t)) t := by
    have he := (((hasDerivAt_id t).const_mul (-C)).exp).mul (hE t ht)
    convert! he using 1 <;> simp only [id_eq, mul_one] <;> ring
  have hWcont : ContinuousOn W (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((hu.norm.pow 2).add (hv.norm.pow 2))
  have hanti : AntitoneOn W (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hWcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hW t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hW t ht).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hD t ht))
  intro t ht
  have hWa : W a = 0 := by simp only [W, E, hua, hva, norm_zero, zero_pow two_ne_zero,
    zero_add, mul_zero]
  have hle : W t ≤ 0 := by
    simpa only [hWa] using hanti (show a ∈ Icc a b from ⟨le_rfl, hab⟩) ht ht.1
  have hE_le : E t ≤ 0 := by
    by_contra hn
    have hpos : 0 < Real.exp (-C * t) * E t :=
      mul_pos (Real.exp_pos _) (lt_of_not_ge hn)
    change Real.exp (-C * t) * E t ≤ 0 at hle
    linarith
  have hnormu : ‖u t‖ = 0 := by
    dsimp only [E] at hE_le
    nlinarith [sq_nonneg ‖v t‖, norm_nonneg (u t)]
  have hnormv : ‖v t‖ = 0 := by
    dsimp only [E] at hE_le
    nlinarith [sq_nonneg ‖u t‖, norm_nonneg (v t)]
  exact ⟨norm_eq_zero.mp hnormu, norm_eq_zero.mp hnormv⟩

def helmholtzModeCoefficientA (lam : ℂ) (m : ℤ) (t : ℝ) : ℂ :=
  (m : ℂ) ^ 2 / (t : ℂ) ^ 2 - lam ^ 2

def helmholtzModeCoefficientB (t : ℝ) : ℂ := -(t : ℂ)⁻¹

def helmholtzModeCoefficientBound (lam : ℂ) (m : ℤ) (δ : ℝ) : ℝ :=
  ‖lam‖ ^ 2 + (m : ℝ) ^ 2 / δ ^ 2 + δ⁻¹

theorem helmholtzModeCoefficientBound_nonneg (lam : ℂ) (m : ℤ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ helmholtzModeCoefficientBound lam m δ := by
  unfold helmholtzModeCoefficientBound
  positivity

/-- The inverse-square angular coefficient is bounded on every positive
interval. There is no invocation of a regular ODE theorem at radius zero. -/
theorem helmholtzModeCoefficient_norm_bound (lam : ℂ) (m : ℤ) {δ t : ℝ}
    (hδ : 0 < δ) (ht : δ ≤ t) :
    ‖helmholtzModeCoefficientA lam m t‖ ≤ helmholtzModeCoefficientBound lam m δ ∧
      ‖helmholtzModeCoefficientB t‖ ≤ helmholtzModeCoefficientBound lam m δ := by
  have htpos : 0 < t := hδ.trans_le ht
  have hsq : δ ^ 2 ≤ t ^ 2 := by nlinarith
  have hquot := div_le_div_of_nonneg_left (sq_nonneg (m : ℝ)) (sq_pos_of_pos hδ) hsq
  have hinv : t⁻¹ ≤ δ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hδ ht
  have hnorm : ‖(m : ℂ) ^ 2 / (t : ℂ) ^ 2‖ = (m : ℝ) ^ 2 / t ^ 2 := by
    simp only [norm_div, norm_pow, Complex.norm_intCast, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hA := norm_sub_le ((m : ℂ) ^ 2 / (t : ℂ) ^ 2) (lam ^ 2)
  rw [hnorm, norm_pow] at hA
  have hB : ‖helmholtzModeCoefficientB t‖ = t⁻¹ := by
    simp only [helmholtzModeCoefficientB, norm_neg, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos htpos]
  unfold helmholtzModeCoefficientBound
  constructor
  · change ‖(m : ℂ) ^ 2 / (t : ℂ) ^ 2 - lam ^ 2‖ ≤ _
    nlinarith [inv_nonneg.mpr hδ.le]
  · rw [hB]
    nlinarith [sq_nonneg ‖lam‖, div_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg δ)]

theorem helmholtzModeODE_zero_of_initial_zero
    (u v : ℝ → ℂ) (lam : ℂ) (m : ℤ) {δ b : ℝ} (hδ : 0 < δ) (hδb : δ ≤ b)
    (hu : ContinuousOn u (Icc δ b)) (hv : ContinuousOn v (Icc δ b))
    (hdu : ∀ t ∈ Ioo δ b, HasDerivAt u (v t) t)
    (hdv : ∀ t ∈ Ioo δ b, HasDerivAt v
      (helmholtzModeCoefficientA lam m t * u t + helmholtzModeCoefficientB t * v t) t)
    (huδ : u δ = 0) (hvδ : v δ = 0) :
    ∀ t ∈ Icc δ b, u t = 0 ∧ v t = 0 := by
  exact boundedComplexODE_zero_of_initial_zero u v
    (helmholtzModeCoefficientA lam m) helmholtzModeCoefficientB hδb
    (helmholtzModeCoefficientBound_nonneg lam m hδ) hu hv hdu hdv
    (fun t ht => (helmholtzModeCoefficient_norm_bound lam m hδ ht.1.le).1)
    (fun t ht => (helmholtzModeCoefficient_norm_bound lam m hδ ht.1.le).2) huδ hvδ

/-- The genuine angular Fourier character with integer mode number. -/
def helmholtzAngularWeight (m : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp ((-Complex.I * (m : ℂ)) * (θ : ℂ))

theorem helmholtzAngularWeight_hasDerivAt (m : ℤ) (θ : ℝ) :
    HasDerivAt (helmholtzAngularWeight m)
      ((-Complex.I * (m : ℂ)) * helmholtzAngularWeight m θ) θ := by
  have h := (((hasDerivAt_id (θ : ℂ)).const_mul (-Complex.I * (m : ℂ))).cexp).comp_ofReal
  convert! h using 1 <;>
    simp only [helmholtzAngularWeight, Function.comp_def, id_eq, mul_one] <;> ring

theorem continuous_helmholtzAngularWeight (m : ℤ) : Continuous (helmholtzAngularWeight m) :=
  continuous_iff_continuousAt.mpr fun θ => (helmholtzAngularWeight_hasDerivAt m θ).continuousAt

theorem helmholtzAngularWeight_period_endpoints (m : ℤ) :
    helmholtzAngularWeight m (2 * Real.pi) = helmholtzAngularWeight m 0 := by
  have hexp : (-Complex.I * (m : ℂ)) * (((2 : ℝ) * Real.pi : ℝ) : ℂ) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  simp only [helmholtzAngularWeight, hexp, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, Complex.exp_int_mul_two_pi_mul_I]

def helmholtzFourierMode (f : Plane → ℂ) (m : ℤ) (r : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
    helmholtzAngularWeight m θ * circleValueIntegrand f 0 r θ

def helmholtzFourierModeSlope (f : Plane → ℂ) (m : ℤ) (r : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
    helmholtzAngularWeight m θ * circleSlopeIntegrand f 0 r θ

def helmholtzFourierModeAccel (f : Plane → ℂ) (m : ℤ) (r : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
    helmholtzAngularWeight m θ * circleAccelIntegrand f 0 r θ

theorem helmholtzFourierMode_hasDerivAt {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (m : ℤ) (r : ℝ) :
    HasDerivAt (helmholtzFourierMode f m) (helmholtzFourierModeSlope f m r) r := by
  have hG : Continuous (fun p : ℝ × ℝ =>
      helmholtzAngularWeight m p.2 * circleValueIntegrand f 0 p.1 p.2) :=
    ((continuous_helmholtzAngularWeight m).comp continuous_snd).mul
      (continuous_circleValueIntegrand hf 0)
  have hH : Continuous (fun p : ℝ × ℝ =>
      helmholtzAngularWeight m p.2 * circleSlopeIntegrand f 0 p.1 p.2) :=
    ((continuous_helmholtzAngularWeight m).comp continuous_snd).mul
      (continuous_circleSlopeIntegrand hf 0)
  have h := hasDerivAt_intervalIntegral_of_joint_continuous
    (G := fun s θ => helmholtzAngularWeight m θ * circleValueIntegrand f 0 s θ)
    (H := fun s θ => helmholtzAngularWeight m θ * circleSlopeIntegrand f 0 s θ)
    hG hH
    (fun s θ => (circleValueIntegrand_hasDerivAt hf 0 s θ).const_mul (helmholtzAngularWeight m θ))
    0 (2 * Real.pi) r
  convert! h using 1 <;> rfl

theorem helmholtzFourierModeSlope_hasDerivAt {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (m : ℤ) (r : ℝ) :
    HasDerivAt (helmholtzFourierModeSlope f m) (helmholtzFourierModeAccel f m r) r := by
  have hG : Continuous (fun p : ℝ × ℝ =>
      helmholtzAngularWeight m p.2 * circleSlopeIntegrand f 0 p.1 p.2) :=
    ((continuous_helmholtzAngularWeight m).comp continuous_snd).mul
      (continuous_circleSlopeIntegrand hf 0)
  have hH : Continuous (fun p : ℝ × ℝ =>
      helmholtzAngularWeight m p.2 * circleAccelIntegrand f 0 p.1 p.2) :=
    ((continuous_helmholtzAngularWeight m).comp continuous_snd).mul
      (continuous_circleAccelIntegrand hf 0)
  have h := hasDerivAt_intervalIntegral_of_joint_continuous
    (G := fun s θ => helmholtzAngularWeight m θ * circleSlopeIntegrand f 0 s θ)
    (H := fun s θ => helmholtzAngularWeight m θ * circleAccelIntegrand f 0 s θ)
    hG hH
    (fun s θ => (circleSlopeIntegrand_hasDerivAt hf 0 s θ).const_mul (helmholtzAngularWeight m θ))
    0 (2 * Real.pi) r
  convert! h using 1 <;> rfl

/-- Integration by parts against the actual integer Fourier character. -/
theorem helmholtz_weighted_integral_derivative (m : ℤ) (v vp : ℝ → ℂ)
    (hv : Continuous v) (hvp : Continuous vp)
    (hd : ∀ θ : ℝ, HasDerivAt v (vp θ) θ)
    (hperiod : v (2 * Real.pi) = v 0) :
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, helmholtzAngularWeight m θ * vp θ) =
      -(-Complex.I * (m : ℂ)) *
        (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, helmholtzAngularWeight m θ * v θ) := by
  let c : ℂ := -Complex.I * (m : ℂ)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (continuous_helmholtzAngularWeight m).continuousOn hv.continuousOn
    (fun θ _ => helmholtzAngularWeight_hasDerivAt m θ) (fun θ _ => hd θ)
    ((continuous_const.mul (continuous_helmholtzAngularWeight m)).intervalIntegrable
      (μ := volume) 0 (2 * Real.pi))
    (hvp.intervalIntegrable (μ := volume) 0 (2 * Real.pi))
  rw [helmholtzAngularWeight_period_endpoints, hperiod, sub_self, zero_sub] at h
  have hi : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      ((-Complex.I * (m : ℂ)) * helmholtzAngularWeight m θ) * v θ) =
      (-Complex.I * (m : ℂ)) *
        (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, helmholtzAngularWeight m θ * v θ) := by
    simp_rw [mul_assoc]
    simpa only [mul_assoc] using
      (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := volume)
        (-Complex.I * (m : ℂ)) (fun θ : ℝ => helmholtzAngularWeight m θ * v θ))
  rw [hi] at h
  simpa only [neg_mul] using h

/-- The angular second derivative has Fourier multiplier `-m²`, proved by two
actual integrations by parts and the two periodic endpoint conditions. -/
theorem helmholtz_weighted_integral_second_derivative (m : ℤ) (v vp vpp : ℝ → ℂ)
    (hv : Continuous v) (hvp : Continuous vp) (hvpp : Continuous vpp)
    (hd : ∀ θ : ℝ, HasDerivAt v (vp θ) θ)
    (hdp : ∀ θ : ℝ, HasDerivAt vp (vpp θ) θ)
    (hperiod : v (2 * Real.pi) = v 0) (hperiodp : vp (2 * Real.pi) = vp 0) :
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, helmholtzAngularWeight m θ * vpp θ) =
      -(m : ℂ) ^ 2 *
        (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, helmholtzAngularWeight m θ * v θ) := by
  rw [helmholtz_weighted_integral_derivative m vp vpp hvp hvpp hdp hperiodp,
    helmholtz_weighted_integral_derivative m v vp hv hvp hd hperiod]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (m : ℂ) ^ 2 *
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, helmholtzAngularWeight m θ * v θ) * hI

theorem circleValueIntegrand_angular_hasDerivAt {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (r θ : ℝ) :
    HasDerivAt (circleValueIntegrand f 0 r) (circleAngularSlope f 0 r θ) θ := by
  have hd := ((hf.differentiable (by simp)).differentiableAt
    (x := (0 : Plane) + r • circleDirection θ)).hasFDerivAt
  convert! hd.comp_hasDerivAt θ (circleAngularParameter_hasDerivAt 0 r θ) using 1 <;> rfl

theorem continuous_circleAngularSlope {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (r : ℝ) : Continuous (circleAngularSlope f 0 r) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hp : Continuous (fun θ : ℝ => (0 : Plane) + r • circleDirection θ) :=
    continuous_const.add (continuous_circleDirection.const_smul r)
  exact (hdf.continuous.comp hp).clm_apply (continuous_circleTangent.const_smul r)

/-- The weighted angular acceleration of the original smooth function, with no
angular ODE identity assumed. -/
theorem helmholtzMode_angular_second_integral {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (m : ℤ) (r : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * circleAngularAccel f 0 r θ) =
      -(m : ℂ) ^ 2 * helmholtzFourierMode f m r := by
  exact helmholtz_weighted_integral_second_derivative m
    (circleValueIntegrand f 0 r) (circleAngularSlope f 0 r) (circleAngularAccel f 0 r)
    ((continuous_circleValueIntegrand hf 0).comp (continuous_const.prodMk continuous_id))
    (continuous_circleAngularSlope hf r) (continuous_circleAngularAccel hf 0 r)
    (circleValueIntegrand_angular_hasDerivAt hf r) (circleAngularSlope_hasDerivAt hf 0 r)
    (by simp [circleValueIntegrand, circleDirection]) (circleAngularSlope_period_endpoints f 0 r)

/-- The exact mode equation before inserting the Helmholtz PDE. -/
theorem helmholtzFourierMode_scaled_polar_identity {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (m : ℤ) (r : ℝ) :
    (r : ℂ) ^ 2 * helmholtzFourierModeAccel f m r +
        (r : ℂ) * helmholtzFourierModeSlope f m r =
      (r : ℂ) ^ 2 * (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        helmholtzAngularWeight m θ * laplacian f (r • circleDirection θ)) +
      (m : ℂ) ^ 2 * helmholtzFourierMode f m r := by
  have hAcont : Continuous (fun θ : ℝ =>
      helmholtzAngularWeight m θ * circleAccelIntegrand f 0 r θ) :=
    ((continuous_helmholtzAngularWeight m).mul
    ((continuous_circleAccelIntegrand hf 0).comp (continuous_const.prodMk continuous_id)))
  have hScont : Continuous (fun θ : ℝ =>
      helmholtzAngularWeight m θ * circleSlopeIntegrand f 0 r θ) :=
    ((continuous_helmholtzAngularWeight m).mul
    ((continuous_circleSlopeIntegrand hf 0).comp (continuous_const.prodMk continuous_id)))
  have hΔcont : Continuous (fun θ : ℝ =>
      helmholtzAngularWeight m θ * laplacian f (r • circleDirection θ)) := by
    have hfun : (fun θ : ℝ => circleAccelIntegrand f 0 r θ + circleTangentialSecond f 0 r θ) =
        (fun θ : ℝ => laplacian f (r • circleDirection θ)) := by
      funext θ
      simpa only [zero_add] using circle_trace_laplacian f 0 r θ
    apply (continuous_helmholtzAngularWeight m).mul
    rw [← hfun]
    exact ((continuous_circleAccelIntegrand hf 0).comp
      (continuous_const.prodMk continuous_id)).add (continuous_circleTangentialSecond hf 0 r)
  have hΔint := hΔcont.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  have hAint := hAcont.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  have hSbig : IntervalIntegrable (fun θ : ℝ => (r : ℂ) *
      (helmholtzAngularWeight m θ * circleSlopeIntegrand f 0 r θ))
      volume 0 (2 * Real.pi) :=
    (continuous_const.mul hScont).intervalIntegrable 0 (2 * Real.pi)
  have hΔAbig : IntervalIntegrable (fun θ : ℝ => (r : ℂ) ^ 2 *
      (helmholtzAngularWeight m θ * laplacian f (r • circleDirection θ) -
        helmholtzAngularWeight m θ * circleAccelIntegrand f 0 r θ))
      volume 0 (2 * Real.pi) :=
    (continuous_const.mul (hΔcont.sub hAcont)).intervalIntegrable 0 (2 * Real.pi)
  have hint : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * circleAngularAccel f 0 r θ) =
      (r : ℂ) ^ 2 *
        ((∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          helmholtzAngularWeight m θ * laplacian f (r • circleDirection θ)) -
          helmholtzFourierModeAccel f m r) -
        (r : ℂ) * helmholtzFourierModeSlope f m r := by
    calc
      _ = ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (r : ℂ) ^ 2 *
            (helmholtzAngularWeight m θ * laplacian f (r • circleDirection θ) -
              helmholtzAngularWeight m θ * circleAccelIntegrand f 0 r θ) -
            (r : ℂ) * (helmholtzAngularWeight m θ * circleSlopeIntegrand f 0 r θ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        have htr := circle_trace_laplacian f 0 r θ
        simp only [zero_add] at htr
        simp only [circleAngularAccel, Complex.real_smul, Complex.ofReal_pow]
        linear_combination (helmholtzAngularWeight m θ * (r : ℂ) ^ 2) * htr
      _ = _ := by
        rw [intervalIntegral.integral_sub hΔAbig hSbig,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hΔint hAint]
        rfl
  rw [helmholtzMode_angular_second_integral hf m r] at hint
  linear_combination hint

/-- Every actual angular Fourier mode of a Helmholtz solution satisfies the
inverse-square radial equation at every positive radius inside the ball. -/
theorem helmholtzFourierMode_radial_ode {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (lam : ℂ) {R : ℝ}
    (hΔ : ∀ y ∈ planeBall R, laplacian f y = -(lam ^ 2) * f y)
    (m : ℤ) {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    helmholtzFourierModeAccel f m r =
      helmholtzModeCoefficientA lam m r * helmholtzFourierMode f m r +
        helmholtzModeCoefficientB r * helmholtzFourierModeSlope f m r := by
  have hPDE : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * laplacian f (r • circleDirection θ)) =
      -(lam ^ 2) * helmholtzFourierMode f m r := by
    rw [helmholtzFourierMode, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hy : r • circleDirection θ ∈ planeBall R := by
      simpa only [planeBall, Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_eq_abs, norm_circleDirection, mul_one, abs_of_pos hr] using hrR
    dsimp only
    rw [hΔ _ hy]
    simp only [circleValueIntegrand, zero_add]
    ring
  have hscaled := helmholtzFourierMode_scaled_polar_identity hf m r
  rw [hPDE] at hscaled
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold helmholtzModeCoefficientA helmholtzModeCoefficientB
  field_simp [hrC]
  linear_combination hscaled

theorem helmholtzFourierMode_eq_zero_on_smaller_ball {f : Plane → ℂ} {a r : ℝ}
    (hzero : ∀ y ∈ planeBall a, f y = 0) (m : ℤ) (hr : 0 ≤ r) (hra : r < a) :
    helmholtzFourierMode f m r = 0 := by
  unfold helmholtzFourierMode
  have hfun : (fun θ : ℝ => helmholtzAngularWeight m θ * circleValueIntegrand f 0 r θ) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext θ
    have hy : r • circleDirection θ ∈ planeBall a := by
      simpa only [planeBall, Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_eq_abs, norm_circleDirection, mul_one, abs_of_nonneg hr] using hra
    simp only [circleValueIntegrand, zero_add, hzero _ hy, mul_zero]
  rw [hfun]
  simp only [intervalIntegral.integral_zero]

/-- The modes really have zero initial slope inside the smaller zero ball:
their derivative vanishes because the modes vanish on a genuine neighborhood. -/
theorem helmholtzFourierModeSlope_eq_zero_on_smaller_ball {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) {a r : ℝ} (hzero : ∀ y ∈ planeBall a, f y = 0)
    (m : ℤ) (hr : 0 < r) (hra : r < a) : helmholtzFourierModeSlope f m r = 0 := by
  have heq : helmholtzFourierMode f m =ᶠ[𝓝 r] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [Ioo_mem_nhds hr hra] with s hs
    exact helmholtzFourierMode_eq_zero_on_smaller_ball hzero m hs.1.le hs.2
  have hderiv := heq.deriv_eq
  rw [(helmholtzFourierMode_hasDerivAt hf m r).deriv] at hderiv
  simpa only [deriv_const] using hderiv

/-- All angular modes vanish throughout the larger ball, by applying bounded
coefficient uniqueness only on intervals whose left endpoint is positive. -/
theorem helmholtzFourierMode_eq_zero_on_ball {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (lam : ℂ) {a R : ℝ} (ha : 0 < a) (haR : a < R)
    (hΔ : ∀ y ∈ planeBall R, laplacian f y = -(lam ^ 2) * f y)
    (hzero : ∀ y ∈ planeBall a, f y = 0) (m : ℤ) {r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) : helmholtzFourierMode f m r = 0 := by
  by_cases hra : r < a
  · exact helmholtzFourierMode_eq_zero_on_smaller_ball hzero m hr hra
  have har : a ≤ r := le_of_not_gt hra
  let δ : ℝ := a / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδa : δ < a := by dsimp [δ]; linarith
  have hδr : δ ≤ r := (le_of_lt hδa).trans har
  have huc : Continuous (helmholtzFourierMode f m) :=
    continuous_iff_continuousAt.mpr fun t => (helmholtzFourierMode_hasDerivAt hf m t).continuousAt
  have hvc : Continuous (helmholtzFourierModeSlope f m) :=
    continuous_iff_continuousAt.mpr fun t => (helmholtzFourierModeSlope_hasDerivAt hf m t).continuousAt
  have hdv (t : ℝ) (ht : t ∈ Ioo δ r) :
      HasDerivAt (helmholtzFourierModeSlope f m)
        (helmholtzModeCoefficientA lam m t * helmholtzFourierMode f m t +
          helmholtzModeCoefficientB t * helmholtzFourierModeSlope f m t) t := by
    apply (helmholtzFourierModeSlope_hasDerivAt hf m t).congr_deriv
    exact helmholtzFourierMode_radial_ode hf lam hΔ m (hδ.trans ht.1) (ht.2.trans hrR)
  have hprop := helmholtzModeODE_zero_of_initial_zero
    (helmholtzFourierMode f m) (helmholtzFourierModeSlope f m) lam m hδ hδr
    huc.continuousOn hvc.continuousOn (fun t _ => helmholtzFourierMode_hasDerivAt hf m t) hdv
    (helmholtzFourierMode_eq_zero_on_smaller_ball hzero m hδ.le hδa)
    (helmholtzFourierModeSlope_eq_zero_on_smaller_ball hf hzero m hδ hδa)
  exact (hprop r ⟨hδr, le_rfl⟩).1

/-- Fourier completeness for the actual angular integral convention. The proof
lifts the continuous periodic function to the additive circle and applies the
pointwise Fourier-series theorem to its identically zero coefficient sequence. -/
theorem continuous_periodic_eq_zero_of_helmholtz_modes
    (G : ℝ → ℂ) (hG : Continuous G) (hp : Function.Periodic G (2 * Real.pi))
    (hmode : ∀ m : ℤ, (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * G θ) = 0) : ∀ θ : ℝ, G θ = 0 := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) := ⟨hp.lift, continuous_coinduced_dom.mpr hG⟩
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hchar (m : ℤ) (θ : ℝ) : fourier (-m) (θ : AddCircle (2 * Real.pi)) =
      helmholtzAngularWeight m θ := by
    rw [fourier_coe_apply]
    unfold helmholtzAngularWeight
    congr 1
    push_cast
    field_simp [hπ] <;> ring
  have hcoeff (m : ℤ) : fourierCoeff F m = 0 := by
    rw [fourierCoeff_eq_intervalIntegral F m 0, zero_add]
    change ((1 / (2 * Real.pi) : ℝ) •
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        fourier (-m) (θ : AddCircle (2 * Real.pi)) * G θ)) = 0
    simp_rw [hchar]
    rw [hmode m, smul_zero]
  have hcoefffun : fourierCoeff F = fun _ : ℤ => (0 : ℂ) := funext hcoeff
  have hsummable : Summable (fourierCoeff F) := by
    rw [hcoefffun]
    exact summable_zero
  intro θ
  have hs := has_pointwise_sum_fourier_series_of_summable
    (f := F) hsummable (θ : AddCircle (2 * Real.pi))
  simp only [hcoeff, zero_smul] at hs
  have hz : F (θ : AddCircle (2 * Real.pi)) = 0 := hs.unique hasSum_zero
  simpa only [F, ContinuousMap.coe_mk, Function.Periodic.lift_coe] using hz

/-- Actual unique continuation from a concentric open subball for a smooth
Helmholtz solution, established through the angular Fourier modes and the
positive-interval energy estimate, rather than an analytic regularity theorem. -/
theorem helmholtz_eq_zero_on_ball_of_eq_zero_on_smaller_ball
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (lam : ℂ) {a R : ℝ}
    (ha : 0 < a) (haR : a < R)
    (hΔ : ∀ y ∈ planeBall R, laplacian f y = -(lam ^ 2) * f y)
    (hzero : ∀ y ∈ planeBall a, f y = 0) : ∀ y ∈ planeBall R, f y = 0 := by
  intro y hy
  let r : ℝ := ‖y‖
  have hr : 0 ≤ r := norm_nonneg y
  have hrR : r < R := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hy
  let G : ℝ → ℂ := fun θ => f (r • circleDirection θ)
  have hGc : Continuous G := hf.continuous.comp (continuous_circleDirection.const_smul r)
  have hGp : Function.Periodic G (2 * Real.pi) := by
    intro θ
    change f (r • circleDirection (θ + 2 * Real.pi)) = f (r • circleDirection θ)
    have hdir : circleDirection (θ + 2 * Real.pi) = circleDirection θ := by
      ext i
      fin_cases i <;> simp [circleDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]
    rw [hdir]
  have hGmode (m : ℤ) : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * G θ) = 0 := by
    simpa only [helmholtzFourierMode, circleValueIntegrand, zero_add, G] using
      helmholtzFourierMode_eq_zero_on_ball hf lam ha haR hΔ hzero m hr hrR
  have hGzero := continuous_periodic_eq_zero_of_helmholtz_modes G hGc hGp hGmode
  have hpolar : r • circleDirection (Complex.arg (complexToPlane.symm y)) = y := by
    apply complexToPlane.symm.injective
    simp only [map_smul, complexToPlane_symm_circleDirection, Complex.real_smul]
    have h := Complex.norm_mul_exp_arg_mul_I (complexToPlane.symm y)
    simpa only [LinearIsometryEquiv.norm_map, r] using h
  have hz := hGzero (Complex.arg (complexToPlane.symm y))
  change f (r • circleDirection (Complex.arg (complexToPlane.symm y))) = 0 at hz
  rw [hpolar] at hz
  exact hz

end J0RadialUniqueness
