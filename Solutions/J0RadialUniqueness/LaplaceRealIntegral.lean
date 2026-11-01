import Solutions.J0RadialUniqueness.LaplaceAnalytic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! The positive-real integral representation of the actual Laplace-defined K.

The principal complex powers are first converted to positive real powers. An
affine change of variables then gives the integral over (1,infinity). No standard
K0 representation or identification with the independent K0 series is assumed.
-/

noncomputable section

open MeasureTheory Set

namespace J0RadialUniqueness

def realLaplaceAmplitude (x t : ℝ) : ℝ := Real.rpow (1 + t / (2 * x)) (-1 / 2 : ℝ)

def realLaplacePrefactor (x : ℝ) : ℝ :=
  Real.sqrt (Real.pi / (2 * x)) * Real.exp (-x)

def positiveLaplaceWeight (x t : ℝ) : ℝ :=
  realLaplacePrefactor x * (muDensity t * realLaplaceAmplitude x t)

def realLaplaceKernel (x t : ℝ) : ℝ :=
  Real.exp (-x - t) / Real.sqrt (t * (2 * x + t))

def positiveSpectralKernel (x v : ℝ) : ℝ :=
  Real.exp (-x * v) / Real.sqrt (v ^ 2 - 1)

theorem real_rpow_neg_half_eq_inv_sqrt {a : ℝ} (ha : 0 ≤ a) :
    Real.rpow a (-1 / 2 : ℝ) = (Real.sqrt a)⁻¹ := by
  simp only [Real.rpow_eq_pow]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg ha,
    ← Real.sqrt_eq_rpow]

theorem laplaceKernel_ofReal {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    laplaceKernel (x : ℂ) t = (realLaplaceAmplitude x t : ℂ) := by
  have hb : 0 ≤ 1 + t / (2 * x) := by positivity
  have h := Complex.ofReal_cpow hb (-1 / 2 : ℝ)
  simpa only [laplaceKernel, realLaplaceAmplitude, Complex.cpow_eq_pow, Real.rpow_eq_pow, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_neg] using h.symm

theorem laplaceK_prefactor_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.cpow ((Real.pi : ℂ) / (2 * (x : ℂ))) (1 / 2 : ℂ) *
      Complex.exp (-(x : ℂ)) = (realLaplacePrefactor x : ℂ) := by
  have hp : Complex.cpow ((Real.pi : ℂ) / (2 * (x : ℂ))) (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / (2 * x)) : ℂ) := by
    have h := Complex.ofReal_cpow
      (div_nonneg Real.pi_pos.le (by positivity : (0 : ℝ) ≤ 2 * x)) (1 / 2 : ℝ)
    rw [← Real.sqrt_eq_rpow] at h
    simpa only [Complex.cpow_eq_pow, Real.rpow_eq_pow, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_ofNat] using h.symm
  rw [hp]
  simp only [realLaplacePrefactor, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg]

/-- The real kernel is obtained by cancellation of the exact square-root factors. -/
theorem positiveLaplaceWeight_eq_realLaplaceKernel {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) :
    positiveLaplaceWeight x t = realLaplaceKernel x t := by
  have hb : 0 < 1 + t / (2 * x) := by positivity
  have hbase : 1 + t / (2 * x) = (2 * x + t) / (2 * x) := by
    field_simp [hx.ne'] <;> ring
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hxroot : Real.sqrt (2 * x) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have htroot : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsumroot : Real.sqrt (2 * x + t) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold positiveLaplaceWeight realLaplacePrefactor realLaplaceAmplitude
    muDensity realLaplaceKernel
  rw [real_rpow_neg_half_eq_inv_sqrt ht.le, real_rpow_neg_half_eq_inv_sqrt hb.le,
    Real.sqrt_div Real.pi_pos.le (2 * x), hbase,
    Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * x + t) (2 * x),
    Real.sqrt_mul ht.le (2 * x + t)]
  rw [show -x - t = -x + -t by ring, Real.exp_add]
  field_simp [hp, hxroot, htroot, hsumroot] <;> ring

/-- Positivity puts the real argument in the actual slit-plane integrability theorem. -/
theorem realLaplaceAmplitude_weighted_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => muDensity t * realLaplaceAmplitude x t) (Ioi 0) := by
  have hslit : (x : ℂ) ∈ Complex.slitPlane := Or.inl hx
  have h := (laplace_weighted_kernel_integrable hslit).re
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ((muDensity t : ℂ) * laplaceKernel (x : ℂ) t).re =
    muDensity t * realLaplaceAmplitude x t
  rw [laplaceKernel_ofReal hx ht.le]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem positiveLaplaceWeight_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (positiveLaplaceWeight x) (Ioi 0) :=
  (realLaplaceAmplitude_weighted_integrable hx).const_mul (realLaplacePrefactor x)

theorem realLaplaceKernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (realLaplaceKernel x) (Ioi 0) := by
  apply (positiveLaplaceWeight_integrable hx).congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact positiveLaplaceWeight_eq_realLaplaceKernel hx ht

/-- Direct conversion of the actual complex definition, before any variable substitution. -/
theorem laplaceK_ofReal_weight_integral {x : ℝ} (hx : 0 < x) :
    laplaceK (x : ℂ) = ((∫ t : ℝ in Ioi 0, positiveLaplaceWeight x t : ℝ) : ℂ) := by
  unfold laplaceK
  rw [laplaceK_prefactor_ofReal hx, laplaceI, weightedIntegral,
    ← integral_const_mul, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (realLaplacePrefactor x : ℂ) * ((muDensity t : ℂ) * laplaceKernel (x : ℂ) t) =
    (positiveLaplaceWeight x t : ℂ)
  rw [laplaceKernel_ofReal hx ht.le]
  simp only [positiveLaplaceWeight, Complex.ofReal_mul]

theorem laplaceK_ofReal_kernel_integral {x : ℝ} (hx : 0 < x) :
    laplaceK (x : ℂ) = ((∫ t : ℝ in Ioi 0, realLaplaceKernel x t : ℝ) : ℂ) := by
  rw [laplaceK_ofReal_weight_integral hx]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact positiveLaplaceWeight_eq_realLaplaceKernel hx ht

/-- The exact pointwise Jacobian cancellation in t=x(v-1). -/
theorem realLaplaceKernel_affine {x : ℝ} (hx : 0 < x) (v : ℝ) :
    x * realLaplaceKernel x (x * (v - 1)) = positiveSpectralKernel x v := by
  have hpoly : (x * (v - 1)) * (2 * x + x * (v - 1)) = x ^ 2 * (v ^ 2 - 1) := by ring
  have hroot : Real.sqrt ((x * (v - 1)) * (2 * x + x * (v - 1))) =
      x * Real.sqrt (v ^ 2 - 1) := by
    rw [hpoly, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
  unfold realLaplaceKernel positiveSpectralKernel
  rw [hroot, show -x - x * (v - 1) = -x * v by ring,
    ← mul_div_assoc, mul_div_mul_left _ _ hx.ne']

theorem positiveLaplace_affine_image {x : ℝ} (hx : 0 < x) :
    (fun v : ℝ => x * (v - 1)) '' Ioi (1 : ℝ) = Ioi (0 : ℝ) := by
  ext t
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mul_pos hx (sub_pos.mpr hv)
  · intro ht
    change 0 < t at ht
    refine ⟨t / x + 1, ?_, ?_⟩
    · have hpos : 0 < t / x := div_pos ht hx
      change 1 < t / x + 1
      linarith
    · field_simp [hx.ne'] <;> ring

theorem positiveLaplace_affine_hasDerivAt (x v : ℝ) :
    HasDerivAt (fun u : ℝ => x * (u - 1)) x v := by
  convert! ((hasDerivAt_id v).sub_const 1).const_mul x using 1 <;> simp <;> ring

theorem positiveLaplace_affine_injOn {x : ℝ} (hx : 0 < x) :
    InjOn (fun v : ℝ => x * (v - 1)) (Ioi (1 : ℝ)) := by
  intro u _ v _ heq
  have heq' := mul_left_cancel₀ hx.ne' heq
  linarith

/-- Absolute convergence at the square-root singular endpoint v=1. -/
theorem positiveSpectralKernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (positiveSpectralKernel x) (Ioi (1 : ℝ)) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun v _ => (positiveLaplace_affine_hasDerivAt x v).hasDerivWithinAt)
    (positiveLaplace_affine_injOn hx) (realLaplaceKernel x)
  rw [positiveLaplace_affine_image hx] at hchange
  have h := hchange.mp (realLaplaceKernel_integrable hx)
  apply h.congr_fun ?_ measurableSet_Ioi
  intro v _
  simpa only [abs_of_pos hx, smul_eq_mul] using realLaplaceKernel_affine hx v

theorem realLaplaceKernel_integral_eq_spectral {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Ioi 0, realLaplaceKernel x t) =
      ∫ v : ℝ in Ioi 1, positiveSpectralKernel x v := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun v _ => (positiveLaplace_affine_hasDerivAt x v).hasDerivWithinAt)
    (positiveLaplace_affine_injOn hx) (realLaplaceKernel x)
  rw [positiveLaplace_affine_image hx] at h
  calc
    (∫ t : ℝ in Ioi 0, realLaplaceKernel x t) =
        ∫ v : ℝ in Ioi 1, |x| • realLaplaceKernel x (x * (v - 1)) := h
    _ = ∫ v : ℝ in Ioi 1, positiveSpectralKernel x v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      simpa only [abs_of_pos hx, smul_eq_mul] using realLaplaceKernel_affine hx v

/-- The requested positive-real representation, derived from the actual Laplace definition. -/
theorem laplaceK_ofReal_spectral_integral {x : ℝ} (hx : 0 < x) :
    laplaceK (x : ℂ) =
      ((∫ v : ℝ in Ioi 1, Real.exp (-x * v) / Real.sqrt (v ^ 2 - 1) : ℝ) : ℂ) := by
  rw [laplaceK_ofReal_kernel_integral hx, realLaplaceKernel_integral_eq_spectral hx]
  rfl

theorem laplaceK_ofReal_spectral_complex_integral {x : ℝ} (hx : 0 < x) :
    laplaceK (x : ℂ) =
      ∫ v : ℝ in Ioi 1, ((Real.exp (-x * v) / Real.sqrt (v ^ 2 - 1) : ℝ) : ℂ) := by
  rw [laplaceK_ofReal_spectral_integral hx, integral_complex_ofReal]

end J0RadialUniqueness
