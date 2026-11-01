import Solutions.J0RadialUniqueness.AmplitudeAnalytic
import Solutions.J0RadialUniqueness.SectorKernelBounds
import Solutions.J0RadialUniqueness.PrincipalPowerEstimate
import Solutions.J0RadialUniqueness.AmplitudeAlgebra
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set

namespace J0RadialUniqueness

theorem kappa_eq_power_three_quarters_div_eight :
    kappa = Real.rpow 2 (3 / 4 : ℝ) / 8 := by
  unfold kappa
  simp only [Real.rpow_eq_pow]
  rw [show (-9 / 4 : ℝ) = 3 / 4 - 3 by norm_num, Real.rpow_sub (by norm_num)]
  norm_num

theorem plusKernel_sub_one_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖plusKernel z t - 1‖ ≤ (Real.rpow 2 (3 / 4 : ℝ) / (4 * ‖z‖)) * t := by
  have he (s : ℝ) : 1 + (s : ℂ) * (Complex.I * (t : ℂ) / (2 * z)) =
      1 + Complex.I * ((s * t : ℝ) : ℂ) / (2 * z) := by push_cast; ring
  have h := inverse_sqrt_sub_one_bound (Complex.I * (t : ℂ) / (2 * z))
    (Real.rpow 2 (3 / 4 : ℝ)) (fun s hs => by
      rw [he]
      exact (amplitude_bases_mem_slitPlane hz.2.2 (mul_nonneg hs.1 ht)).1)
    (fun s hs => by rw [he]; exact plus_three_halves_bound hz (mul_nonneg hs.1 ht))
  change ‖plusKernel z t - 1‖ ≤ _ at h
  calc
    _ ≤ (‖Complex.I * (t : ℂ) / (2 * z)‖ / 2) * Real.rpow 2 (3 / 4 : ℝ) := h
    _ = _ := by simp [norm_div, norm_mul, abs_of_nonneg ht]; ring

theorem minusKernel_sub_one_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖minusKernel z t - 1‖ ≤ (Real.rpow 2 (3 / 4 : ℝ) / (4 * ‖z‖)) * t := by
  have he (s : ℝ) : 1 + (s : ℂ) * (-Complex.I * (t : ℂ) / (2 * z)) =
      1 - Complex.I * ((s * t : ℝ) : ℂ) / (2 * z) := by push_cast; ring
  have h := inverse_sqrt_sub_one_bound (-Complex.I * (t : ℂ) / (2 * z))
    (Real.rpow 2 (3 / 4 : ℝ)) (fun s hs => by
      rw [he]
      exact (amplitude_bases_mem_slitPlane hz.2.2 (mul_nonneg hs.1 ht)).2)
    (fun s _ => by rw [he]; exact minus_three_halves_bound hz (s * t))
  rw [show 1 + -Complex.I * (t : ℂ) / (2 * z) =
      1 - Complex.I * (t : ℂ) / (2 * z) by ring] at h
  change ‖minusKernel z t - 1‖ ≤ _ at h
  calc
    _ ≤ (‖-Complex.I * (t : ℂ) / (2 * z)‖ / 2) * Real.rpow 2 (3 / 4 : ℝ) := h
    _ = _ := by simp [norm_div, norm_mul, abs_of_nonneg ht]; ring

theorem weightedIntegral_norm_le_half {g : ℝ → ℂ} {D : ℝ}
    (hb : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ D * t) : ‖weightedIntegral g‖ ≤ D / 2 := by
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖(muDensity t : ℂ) * g t‖ ≤ D * (t * muDensity t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (muDensity_nonneg t ht.le)]
    calc
      _ ≤ muDensity t * (D * t) := mul_le_mul_of_nonneg_left (hb t ht) (muDensity_nonneg t ht.le)
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le (firstMoment_integrableOn.const_mul D) hbound
  change ‖weightedIntegral g‖ ≤ _ at hh
  rw [integral_const_mul, firstMoment_integral] at hh
  convert hh using 1 <;> ring

theorem weightedIntegral_sub_one_eq {g : ℝ → ℂ}
    (hg : IntegrableOn (fun t => (muDensity t : ℂ) * g t) (Ioi (0 : ℝ))) :
    weightedIntegral g - 1 = weightedIntegral (fun t => g t - 1) := by
  have hμ : IntegrableOn (fun t : ℝ => (muDensity t : ℂ)) (Ioi (0 : ℝ)) :=
    muDensity_integrableOn.ofReal
  have hmass : (∫ t in Ioi (0 : ℝ), (muDensity t : ℂ)) = 1 := by
    rw [integral_complex_ofReal, muDensity_integral]
    rfl
  unfold weightedIntegral
  have he : (fun t : ℝ => (muDensity t : ℂ) * (g t - 1)) =
      (fun t => (muDensity t : ℂ) * g t) - (fun t => (muDensity t : ℂ)) := by
    funext t
    simp only [Pi.sub_apply]
    ring
  rw [he]
  change _ = ∫ t in Ioi (0 : ℝ), (muDensity t : ℂ) * g t - (muDensity t : ℂ)
  rw [integral_sub hg hμ, hmass]

/-- Proposition 4.1's four actual integral estimates, with no assumed amplitude estimates. -/
theorem amplitude_uniform_estimates : AmplitudeUniformEstimatesStatement := by
  intro z hz
  let C : ℝ := Real.rpow 2 (3 / 4 : ℝ)
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (rightHalfPlane_ne_zero hz.2.2)
  have hk : kappa = C / 8 := kappa_eq_power_three_quarters_div_eight
  have hint := amplitude_integrability z hz.2.2
  have hp : ‖APlus z - 1‖ ≤ kappa / ‖z‖ := by
    rw [APlus, weightedIntegral_sub_one_eq hint.1]
    have hh := weightedIntegral_norm_le_half (fun t ht => plusKernel_sub_one_bound hz ht.le)
    calc
      _ ≤ (C / (4 * ‖z‖)) / 2 := hh
      _ = _ := by rw [hk]; ring
  have hm : ‖AMinus z - 1‖ ≤ kappa / ‖z‖ := by
    rw [AMinus, weightedIntegral_sub_one_eq hint.2.1]
    have hh := weightedIntegral_norm_le_half (fun t ht => minusKernel_sub_one_bound hz ht.le)
    calc
      _ ≤ (C / (4 * ‖z‖)) / 2 := hh
      _ = _ := by rw [hk]; ring
  have hpm : ‖weightedIntegral (plusMomentKernel z)‖ ≤ C / 2 := by
    apply weightedIntegral_norm_le_half
    intro t ht
    unfold plusMomentKernel
    rw [norm_mul, Complex.norm_of_nonneg ht.le]
    calc
      _ ≤ t * C := mul_le_mul_of_nonneg_left (plus_three_halves_bound hz ht.le) ht.le
      _ = C * t := mul_comm _ _
  have hmm : ‖weightedIntegral (minusMomentKernel z)‖ ≤ C / 2 := by
    apply weightedIntegral_norm_le_half
    intro t ht
    unfold minusMomentKernel
    rw [norm_mul, Complex.norm_of_nonneg ht.le]
    calc
      _ ≤ t * C := mul_le_mul_of_nonneg_left (minus_three_halves_bound hz t) ht.le
      _ = C * t := mul_comm _ _
  have hp' : ‖deriv APlus z‖ ≤ kappa / ‖z‖ ^ 2 := by
    rw [(APlus_hasDerivAt hz.2.2).deriv, norm_mul]
    have hn : ‖Complex.I / (4 * z ^ 2)‖ = 1 / (4 * ‖z‖ ^ 2) := by simp
    rw [hn]
    calc
      _ ≤ (1 / (4 * ‖z‖ ^ 2)) * (C / 2) := mul_le_mul_of_nonneg_left hpm (by positivity)
      _ = _ := by rw [hk]; ring
  have hm' : ‖deriv AMinus z‖ ≤ kappa / ‖z‖ ^ 2 := by
    rw [(AMinus_hasDerivAt hz.2.2).deriv, norm_mul]
    have hn : ‖-Complex.I / (4 * z ^ 2)‖ = 1 / (4 * ‖z‖ ^ 2) := by simp
    rw [hn]
    calc
      _ ≤ (1 / (4 * ‖z‖ ^ 2)) * (C / 2) := mul_le_mul_of_nonneg_left hmm (by positivity)
      _ = _ := by rw [hk]; ring
  exact ⟨hp, hm, hp', hm'⟩

theorem amplitude_modulus_bounds : AmplitudeModulusBoundsStatement :=
  amplitudeModulusBounds_of_uniform amplitude_uniform_estimates

theorem paper_4_1 : AmplitudeUniformEstimatesStatement ∧ AmplitudeModulusBoundsStatement :=
  ⟨amplitude_uniform_estimates, amplitude_modulus_bounds⟩

end J0RadialUniqueness
