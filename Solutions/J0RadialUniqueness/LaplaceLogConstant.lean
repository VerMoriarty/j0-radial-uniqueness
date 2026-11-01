import Solutions.J0RadialUniqueness.LaplaceRealIntegral
import Solutions.J0RadialUniqueness.ExponentialIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The logarithmic constant of the actual positive-real Laplace integral.

The difference from E1 is dominated by an explicitly integrable positive kernel.
Its integral is computed from a primitive, including both endpoint limits.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace J0RadialUniqueness

def laplaceKReal (x : ℝ) : ℝ := ∫ v : ℝ in Ioi 1, positiveSpectralKernel x v

def spectralDifference (v : ℝ) : ℝ := (Real.sqrt (v ^ 2 - 1))⁻¹ - v⁻¹

def spectralDifferencePrimitive (v : ℝ) : ℝ :=
  Real.log (v + Real.sqrt (v ^ 2 - 1)) - Real.log v

def E1SpectralKernel (x v : ℝ) : ℝ := Real.exp (-x * v) / v

theorem spectralDifference_nonneg {v : ℝ} (hv : 1 < v) : 0 ≤ spectralDifference v := by
  have hvpos : 0 < v := lt_trans zero_lt_one hv
  have hsq : 0 < v ^ 2 - 1 := by nlinarith [sq_nonneg (v - 1)]
  have hspos : 0 < Real.sqrt (v ^ 2 - 1) := Real.sqrt_pos.mpr hsq
  have hslt : Real.sqrt (v ^ 2 - 1) < v :=
    (Real.sqrt_lt hsq.le hvpos.le).mpr (by linarith)
  unfold spectralDifference
  exact sub_nonneg.mpr ((inv_le_inv₀ hvpos hspos).mpr hslt.le)

theorem spectralDifferencePrimitive_hasDerivAt {v : ℝ} (hv : 1 < v) :
    HasDerivAt spectralDifferencePrimitive (spectralDifference v) v := by
  have hvpos : 0 < v := lt_trans zero_lt_one hv
  have hsq : 0 < v ^ 2 - 1 := by nlinarith [sq_nonneg (v - 1)]
  have hspos : 0 < Real.sqrt (v ^ 2 - 1) := Real.sqrt_pos.mpr hsq
  have harg : 0 < v + Real.sqrt (v ^ 2 - 1) := add_pos hvpos hspos
  have hroot : HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - 1))
      (2 * v / (2 * Real.sqrt (v ^ 2 - 1))) v := by
    convert! (((hasDerivAt_id v).pow 2).sub_const 1).sqrt hsq.ne' using 1 <;> simp <;> ring
  have h := (((hasDerivAt_id v).add hroot).log harg.ne').sub
    (Real.hasDerivAt_log hvpos.ne')
  change HasDerivAt spectralDifferencePrimitive
    ((1 + 2 * v / (2 * Real.sqrt (v ^ 2 - 1))) /
      (v + Real.sqrt (v ^ 2 - 1)) - v⁻¹) v at h
  apply h.congr_deriv
  unfold spectralDifference
  field_simp [hvpos.ne', hspos.ne', harg.ne'] <;> ring

@[simp] theorem spectralDifferencePrimitive_one : spectralDifferencePrimitive 1 = 0 := by
  norm_num [spectralDifferencePrimitive]

theorem spectralDifferencePrimitive_continuousAt_one :
    ContinuousAt spectralDifferencePrimitive 1 := by
  have hsum : ContinuousAt (fun v : ℝ => v + Real.sqrt (v ^ 2 - 1)) 1 := by fun_prop
  have harg : (1 : ℝ) + Real.sqrt ((1 : ℝ) ^ 2 - 1) ≠ 0 := by norm_num
  exact (hsum.log harg).sub (Real.continuousAt_log (by norm_num))

theorem spectralDifferencePrimitive_eq_normalized {v : ℝ} (hv : 1 < v) :
    spectralDifferencePrimitive v = Real.log (1 + Real.sqrt (1 - (v⁻¹) ^ 2)) := by
  have hvpos : 0 < v := lt_trans zero_lt_one hv
  have hsq : 0 ≤ v ^ 2 - 1 := by nlinarith [sq_nonneg (v - 1)]
  have harg : v + Real.sqrt (v ^ 2 - 1) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hvpos (Real.sqrt_nonneg _)).ne'
  have hroot : Real.sqrt (v ^ 2 - 1) / v = Real.sqrt (1 - (v⁻¹) ^ 2) := by
    calc
      Real.sqrt (v ^ 2 - 1) / v = Real.sqrt (v ^ 2 - 1) / Real.sqrt (v ^ 2) := by
        rw [Real.sqrt_sq hvpos.le]
      _ = Real.sqrt ((v ^ 2 - 1) / v ^ 2) := (Real.sqrt_div hsq (v ^ 2)).symm
      _ = Real.sqrt (1 - (v⁻¹) ^ 2) := by
        congr 1
        field_simp [hvpos.ne'] <;> ring
  unfold spectralDifferencePrimitive
  rw [← Real.log_div harg hvpos.ne']
  congr 1
  rw [add_div, div_self hvpos.ne', hroot]

theorem spectralDifferencePrimitive_tendsto_log_two :
    Tendsto spectralDifferencePrimitive atTop (𝓝 (Real.log 2)) := by
  have hi : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hinside : Tendsto (fun v : ℝ => 1 - (v⁻¹) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using hone.sub (hi.pow 2)
  have hroot : Tendsto (fun v : ℝ => Real.sqrt (1 - (v⁻¹) ^ 2)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.sqrt_one] using hinside.sqrt
  have hsum : Tendsto (fun v : ℝ => 1 + Real.sqrt (1 - (v⁻¹) ^ 2))
      atTop (𝓝 (2 : ℝ)) := by simpa only [one_add_one_eq_two] using hone.add hroot
  apply (hsum.log (by norm_num)).congr'
  filter_upwards [Ioi_mem_atTop (1 : ℝ)] with v hv
  exact (spectralDifferencePrimitive_eq_normalized hv).symm

theorem spectralDifference_integrable : IntegrableOn spectralDifference (Ioi (1 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg
    spectralDifferencePrimitive_continuousAt_one.continuousWithinAt
    (fun _ hv => spectralDifferencePrimitive_hasDerivAt hv)
    (fun _ hv => spectralDifference_nonneg hv)
    spectralDifferencePrimitive_tendsto_log_two

theorem spectralDifference_integral :
    (∫ v : ℝ in Ioi 1, spectralDifference v) = Real.log 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    spectralDifferencePrimitive_continuousAt_one.continuousWithinAt
    (fun _ hv => spectralDifferencePrimitive_hasDerivAt hv)
    (fun _ hv => spectralDifference_nonneg hv)
    spectralDifferencePrimitive_tendsto_log_two
  simpa only [spectralDifferencePrimitive_one, sub_zero] using h

/-- The E1 change of variables is proved for the actual integral, not presumed. -/
theorem E1SpectralKernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (E1SpectralKernel x) (Ioi (1 : ℝ)) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => Real.exp (-t) / t) (1 : ℝ) hx).mpr
      (by simpa only [mul_one] using E1_integrableOn hx)
  apply (h.const_mul x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change x * (Real.exp (-(x * v)) / (x * v)) = E1SpectralKernel x v
  unfold E1SpectralKernel
  have hvpos : 0 < v := lt_trans zero_lt_one hv
  rw [neg_mul]
  field_simp [hx.ne', hvpos.ne'] <;> ring

theorem E1_eq_spectral_integral {x : ℝ} (hx : 0 < x) :
    E1 x = ∫ v : ℝ in Ioi 1, E1SpectralKernel x v := by
  have h := integral_comp_mul_left_Ioi'
    (fun t : ℝ => Real.exp (-t) / t) (1 : ℝ) hx
  simp only [mul_one, smul_eq_mul] at h
  change x * (∫ v : ℝ in Ioi 1, Real.exp (-(x * v)) / (x * v)) = E1 x at h
  rw [← integral_const_mul] at h
  calc
    E1 x = ∫ v : ℝ in Ioi 1, x * (Real.exp (-(x * v)) / (x * v)) := h.symm
    _ = ∫ v : ℝ in Ioi 1, E1SpectralKernel x v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      change x * (Real.exp (-(x * v)) / (x * v)) = Real.exp (-x * v) / v
      have hvpos : 0 < v := lt_trans zero_lt_one hv
      rw [neg_mul]
      field_simp [hx.ne', hvpos.ne'] <;> ring

theorem laplaceKReal_sub_E1_identity {x : ℝ} (hx : 0 < x) :
    laplaceKReal x - E1 x =
      ∫ v : ℝ in Ioi 1, Real.exp (-x * v) * spectralDifference v := by
  unfold laplaceKReal
  rw [E1_eq_spectral_integral hx,
    ← integral_sub (positiveSpectralKernel_integrable hx) (E1SpectralKernel_integrable hx)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  change positiveSpectralKernel x v - E1SpectralKernel x v =
    Real.exp (-x * v) * spectralDifference v
  unfold positiveSpectralKernel E1SpectralKernel spectralDifference
  ring

theorem spectralDifference_damped_integral_tendsto :
    Tendsto (fun x : ℝ => ∫ v : ℝ in Ioi 1, Real.exp (-x * v) * spectralDifference v)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  have hmeas : ∀ᶠ x : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun v : ℝ => Real.exp (-x * v) * spectralDifference v)
        (volume.restrict (Ioi 1)) := by
    exact Eventually.of_forall (fun x =>
      (show Continuous (fun v : ℝ => Real.exp (-x * v)) by fun_prop).aestronglyMeasurable.mul
        spectralDifference_integrable.aestronglyMeasurable)
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] 0,
      ∀ᵐ v ∂volume.restrict (Ioi 1),
        ‖Real.exp (-x * v) * spectralDifference v‖ ≤ spectralDifference v := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hxpos : 0 < x := hx
    have hvpos : 0 < v := lt_trans zero_lt_one hv
    have hd := spectralDifference_nonneg hv
    have he : Real.exp (-x * v) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hxpos hvpos])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hd)]
    exact mul_le_of_le_one_left hd he
  have hlim : ∀ᵐ v ∂volume.restrict (Ioi 1),
      Tendsto (fun x : ℝ => Real.exp (-x * v) * spectralDifference v)
        (𝓝[>] 0) (𝓝 (spectralDifference v)) := by
    apply Eventually.of_forall
    intro v
    have h : Tendsto (fun x : ℝ => Real.exp (-x * v)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
      have hc : Continuous (fun x : ℝ => Real.exp (-x * v)) := by fun_prop
      simpa only [neg_zero, zero_mul, Real.exp_zero] using
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [one_mul] using h.mul_const (spectralDifference v)
  have h := tendsto_integral_filter_of_dominated_convergence spectralDifference
    hmeas hbound spectralDifference_integrable hlim
  simpa only [spectralDifference_integral] using h

theorem laplaceKReal_sub_E1_tendsto_log_two :
    Tendsto (fun x : ℝ => laplaceKReal x - E1 x)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  apply spectralDifference_damped_integral_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (laplaceKReal_sub_E1_identity hx).symm

/-- The actual positive-real Laplace integral has the required logarithmic constant. -/
theorem laplaceKReal_add_log_half_tendsto_neg_eulerMascheroni :
    Tendsto (fun x : ℝ => laplaceKReal x + Real.log (x / 2))
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have h := (laplaceKReal_sub_E1_tendsto_log_two.add
    E1_add_log_tendsto_neg_eulerMascheroni).sub_const (Real.log 2)
  have heq : (fun x : ℝ => (laplaceKReal x - E1 x + (E1 x + Real.log x)) - Real.log 2)
      =ᶠ[𝓝[>] 0] (fun x : ℝ => laplaceKReal x + Real.log (x / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.log_div (ne_of_gt (show 0 < x from hx)) (by norm_num)]
    ring
  have hconstant : Real.log 2 + -Real.eulerMascheroniConstant - Real.log 2 =
      -Real.eulerMascheroniConstant := by ring
  rw [hconstant] at h
  exact h.congr' heq

theorem laplaceK_ofReal_eq_laplaceKReal {x : ℝ} (hx : 0 < x) :
    laplaceK (x : ℂ) = (laplaceKReal x : ℂ) :=
  laplaceK_ofReal_spectral_integral hx

/-- Complex-valued version, for subsequent comparison with the independent K0 series. -/
theorem laplaceK_add_log_half_tendsto_neg_eulerMascheroni :
    Tendsto (fun x : ℝ => laplaceK (x : ℂ) + (Real.log (x / 2) : ℂ))
      (𝓝[>] 0) (𝓝 (-((Real.eulerMascheroniConstant : ℝ) : ℂ))) := by
  have h := (Complex.continuous_ofReal.tendsto (-Real.eulerMascheroniConstant)).comp
    laplaceKReal_add_log_half_tendsto_neg_eulerMascheroni
  have heq : (fun x : ℝ => ((laplaceKReal x + Real.log (x / 2) : ℝ) : ℂ))
      =ᶠ[𝓝[>] 0] (fun x : ℝ => laplaceK (x : ℂ) + (Real.log (x / 2) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [laplaceK_ofReal_eq_laplaceKReal hx, Complex.ofReal_add]
  simpa only [Complex.ofReal_neg] using h.congr' heq

end J0RadialUniqueness
