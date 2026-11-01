import Solutions.J0RadialUniqueness.LaplaceRealIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The actual positive-real spectral integral and its modified Bessel equation.
All moment integrals and differentiations are justified by explicit exponential
majorants derived from the nonnegative exponential series.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace J0RadialUniqueness

def spectralMomentKernel (n : ℕ) (x v : ℝ) : ℝ := v ^ n * positiveSpectralKernel x v

def spectralMoment (n : ℕ) (x : ℝ) : ℝ :=
  ∫ v : ℝ in Ioi 1, spectralMomentKernel n x v

def kSpectral (x : ℝ) : ℝ := spectralMoment 0 x

def kSpectralPrime (x : ℝ) : ℝ := -spectralMoment 1 x

def kSpectralSecond (x : ℝ) : ℝ := spectralMoment 2 x

def spectralFlux (x v : ℝ) : ℝ := Real.exp (-x * v) * Real.sqrt (v ^ 2 - 1)

theorem spectralSqrt_pos {v : ℝ} (hv : 1 < v) : 0 < Real.sqrt (v ^ 2 - 1) :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem positiveSpectralKernel_nonneg (x v : ℝ) : 0 ≤ positiveSpectralKernel x v := by
  unfold positiveSpectralKernel
  positivity

theorem spectralMomentKernel_nonneg (n : ℕ) (x : ℝ) {v : ℝ} (hv : 1 < v) :
    0 ≤ spectralMomentKernel n x v :=
  mul_nonneg (pow_nonneg (by linarith) _) (positiveSpectralKernel_nonneg x v)

theorem positiveSpectralKernel_continuousOn (x : ℝ) :
    ContinuousOn (positiveSpectralKernel x) (Ioi (1 : ℝ)) := by
  intro v hv
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  exact (spectralSqrt_pos hv).ne'

theorem spectralMomentKernel_continuousOn (n : ℕ) (x : ℝ) :
    ContinuousOn (spectralMomentKernel n x) (Ioi (1 : ℝ)) :=
  (continuous_id.pow n).continuousOn.mul (positiveSpectralKernel_continuousOn x)

/-- Explicit polynomial absorption into half of an exponential decay margin. -/
theorem polynomial_exp_decay_bound (n : ℕ) {a x v : ℝ}
    (ha : 0 < a) (hx : 2 * a ≤ x) (hv : 0 ≤ v) :
    v ^ n * Real.exp (-x * v) ≤
      ((n.factorial : ℝ) / a ^ n) * Real.exp (-a * v) := by
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have hterm := Real.pow_div_factorial_le_exp (a * v) (mul_nonneg ha.le hv) n
  have hclear : a ^ n * v ^ n ≤ Real.exp (a * v) * (n.factorial : ℝ) := by
    have h := (div_le_iff₀ hf).1 hterm
    simpa only [mul_pow] using h
  have hpow : v ^ n ≤ ((n.factorial : ℝ) / a ^ n) * Real.exp (a * v) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos ha n)).2
    nlinarith only [hclear]
  have hC : 0 ≤ (n.factorial : ℝ) / a ^ n := by positivity
  calc
    v ^ n * Real.exp (-x * v) ≤
        (((n.factorial : ℝ) / a ^ n) * Real.exp (a * v)) * Real.exp (-x * v) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = ((n.factorial : ℝ) / a ^ n) * Real.exp ((a - x) * v) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ ((n.factorial : ℝ) / a ^ n) * Real.exp (-a * v) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith : a - x ≤ -a) hv)) hC

theorem spectralMomentKernel_norm_bound (n : ℕ) {a x v : ℝ}
    (ha : 0 < a) (hx : 2 * a ≤ x) (hv : 1 < v) :
    ‖spectralMomentKernel n x v‖ ≤
      ((n.factorial : ℝ) / a ^ n) * positiveSpectralKernel a v := by
  rw [Real.norm_eq_abs, abs_of_nonneg (spectralMomentKernel_nonneg n x hv)]
  calc
    spectralMomentKernel n x v =
        (v ^ n * Real.exp (-x * v)) / Real.sqrt (v ^ 2 - 1) := by
      unfold spectralMomentKernel positiveSpectralKernel
      ring
    _ ≤ (((n.factorial : ℝ) / a ^ n) * Real.exp (-a * v)) /
        Real.sqrt (v ^ 2 - 1) :=
      div_le_div_of_nonneg_right
        (polynomial_exp_decay_bound n ha hx (by linarith)) (Real.sqrt_nonneg _)
    _ = ((n.factorial : ℝ) / a ^ n) * positiveSpectralKernel a v := by
      unfold positiveSpectralKernel
      ring

theorem spectralMomentKernel_integrable (n : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (spectralMomentKernel n x) (Ioi (1 : ℝ)) := by
  have ha : 0 < x / 2 := by positivity
  apply ((positiveSpectralKernel_integrable ha).const_mul
    ((n.factorial : ℝ) / (x / 2) ^ n)).mono'
    ((spectralMomentKernel_continuousOn n x).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact spectralMomentKernel_norm_bound n ha (by linarith) hv

theorem spectralMomentKernel_hasDerivAt (n : ℕ) (x v : ℝ) :
    HasDerivAt (fun y : ℝ => spectralMomentKernel n y v)
      (-spectralMomentKernel (n + 1) x v) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-y * v))
      (Real.exp (-x * v) * (-v)) x := by
    simpa only [id_eq, Pi.neg_apply, neg_one_mul] using
      (((hasDerivAt_id x).neg.mul_const v).exp)
  have h := (he.div_const (Real.sqrt (v ^ 2 - 1))).const_mul (v ^ n)
  apply h.congr_deriv
  dsimp only [spectralMomentKernel, positiveSpectralKernel]
  rw [pow_succ]
  ring

/-- Every real moment differentiates to minus the next moment on x>0. -/
theorem spectralMoment_hasDerivAt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (spectralMoment n) (-spectralMoment (n + 1) x) x := by
  let a : ℝ := x / 4
  let F : ℝ → ℝ → ℝ := spectralMomentKernel n
  let D : ℝ → ℝ → ℝ := fun y v => -spectralMomentKernel (n + 1) y v
  let B : ℝ → ℝ := fun v => ((n + 1).factorial : ℝ) / a ^ (n + 1) * positiveSpectralKernel a v
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : Ioi (x / 2) ∈ 𝓝 x :=
    isOpen_Ioi.mem_nhds (show x / 2 < x by linarith)
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y)
      (volume.restrict (Ioi (1 : ℝ))) :=
    Eventually.of_forall (fun y =>
      (spectralMomentKernel_continuousOn n y).aestronglyMeasurable measurableSet_Ioi)
  have hdmeas : AEStronglyMeasurable (D x) (volume.restrict (Ioi (1 : ℝ))) :=
    ((spectralMomentKernel_continuousOn (n + 1) x).aestronglyMeasurable measurableSet_Ioi).neg
  have hbound : ∀ᵐ v ∂volume.restrict (Ioi (1 : ℝ)),
      ∀ y ∈ Ioi (x / 2), ‖D y v‖ ≤ B v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro y hy
    dsimp only [D, B]
    rw [norm_neg]
    have hparam : 2 * a ≤ y := by
      change x / 2 < y at hy
      dsimp only [a]
      linarith
    exact spectralMomentKernel_norm_bound (n + 1) ha hparam hv
  have hBint : Integrable B (volume.restrict (Ioi (1 : ℝ))) :=
    (positiveSpectralKernel_integrable ha).const_mul _
  have hdiff : ∀ᵐ v ∂volume.restrict (Ioi (1 : ℝ)),
      ∀ y ∈ Ioi (x / 2), HasDerivAt (F · v) (D y v) y :=
    Eventually.of_forall (fun v y _ => spectralMomentKernel_hasDerivAt n y v)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : ℝ))) hs hmeas (spectralMomentKernel_integrable n hx)
    hdmeas hbound hBint hdiff
  have hvalue : (∫ v, D x v ∂volume.restrict (Ioi (1 : ℝ))) =
      -spectralMoment (n + 1) x := by
    dsimp only [D]
    rw [integral_neg]
    rfl
  rw [hvalue] at h
  exact h.2

theorem kSpectral_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt kSpectral (kSpectralPrime x) x := spectralMoment_hasDerivAt 0 hx

theorem kSpectralPrime_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt kSpectralPrime (kSpectralSecond x) x := by
  convert! (spectralMoment_hasDerivAt 1 hx).neg using 1 <;>
    simp only [kSpectralPrime, kSpectralSecond, neg_neg]

theorem spectralFlux_continuous (x : ℝ) : Continuous (spectralFlux x) := by
  unfold spectralFlux
  fun_prop

theorem spectralFlux_hasDerivAt (x : ℝ) {v : ℝ} (hv : 1 < v) :
    HasDerivAt (spectralFlux x)
      (spectralMomentKernel 1 x v - x *
        (spectralMomentKernel 2 x v - spectralMomentKernel 0 x v)) v := by
  have hp : 0 < v ^ 2 - 1 := by nlinarith
  have hr : Real.sqrt (v ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - 1))
      (v / Real.sqrt (v ^ 2 - 1)) v := by
    have h := (((hasDerivAt_id v).pow 2).sub_const 1).sqrt hp.ne'
    apply h.congr_deriv
    simp only [id_eq, Pi.pow_apply]
    field_simp [hr] <;> ring
  have he : HasDerivAt (fun u : ℝ => Real.exp (-x * u))
      (Real.exp (-x * v) * (-x)) v := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id v).const_mul (-x)).exp
  have h := he.mul hsqrt
  apply h.congr_deriv
  calc
    (Real.exp (-x * v) * (-x)) * Real.sqrt (v ^ 2 - 1) +
        Real.exp (-x * v) * (v / Real.sqrt (v ^ 2 - 1)) =
        Real.exp (-x * v) * ((v - x * Real.sqrt (v ^ 2 - 1) ^ 2) /
          Real.sqrt (v ^ 2 - 1)) := by field_simp [hr] <;> ring
    _ = Real.exp (-x * v) * ((v - x * (v ^ 2 - 1)) /
        Real.sqrt (v ^ 2 - 1)) := by rw [Real.sq_sqrt hp.le]
    _ = _ := by
      dsimp only [spectralMomentKernel, positiveSpectralKernel]
      ring

theorem linear_exp_decay_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun v : ℝ => v * Real.exp (-x * v)) atTop (𝓝 0) := by
  have htop : Tendsto (fun v : ℝ => x * v) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hx).2 tendsto_id
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp htop).div_const x
  change Tendsto (fun v : ℝ => ((x * v) ^ 1 * Real.exp (-(x * v))) / x)
    atTop (𝓝 (0 / x)) at h
  have hfun : (fun v : ℝ => ((x * v) ^ 1 * Real.exp (-(x * v))) / x) =
      (fun v : ℝ => v * Real.exp (-x * v)) := by
    funext v
    simp only [pow_one, neg_mul]
    field_simp [hx.ne'] <;> ring
  rw [hfun] at h
  simpa using h

theorem spectralFlux_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (spectralFlux x) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun v => by unfold spectralFlux; positivity))
    ?_ (linear_exp_decay_tendsto_zero hx)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
  have hr : Real.sqrt (v ^ 2 - 1) ≤ v := (Real.sqrt_le_left hv).mpr (by linarith)
  unfold spectralFlux
  calc
    Real.exp (-x * v) * Real.sqrt (v ^ 2 - 1) ≤ Real.exp (-x * v) * v :=
      mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
    _ = v * Real.exp (-x * v) := mul_comm _ _

theorem spectral_moment_ode {x : ℝ} (hx : 0 < x) :
    x * spectralMoment 2 x - spectralMoment 1 x - x * spectralMoment 0 x = 0 := by
  have h0 := spectralMomentKernel_integrable 0 hx
  have h1 := spectralMomentKernel_integrable 1 hx
  have h2 := spectralMomentKernel_integrable 2 hx
  have hD : IntegrableOn (fun v => spectralMomentKernel 1 x v -
      x * (spectralMomentKernel 2 x v - spectralMomentKernel 0 x v)) (Ioi (1 : ℝ)) :=
    h1.sub ((h2.sub h0).const_mul x)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (spectralFlux_continuous x).continuousAt.continuousWithinAt
    (fun v hv => spectralFlux_hasDerivAt x hv) hD (spectralFlux_tendsto_zero hx)
  have hvalue : (∫ v : ℝ in Ioi 1, spectralMomentKernel 1 x v -
      x * (spectralMomentKernel 2 x v - spectralMomentKernel 0 x v)) =
      spectralMoment 1 x - x * (spectralMoment 2 x - spectralMoment 0 x) := by
    have h20 : IntegrableOn
        (fun v : ℝ => spectralMomentKernel 2 x v - spectralMomentKernel 0 x v) (Ioi 1) :=
      h2.sub h0
    have hx20 : IntegrableOn
        (fun v : ℝ => x * (spectralMomentKernel 2 x v - spectralMomentKernel 0 x v)) (Ioi 1) :=
      h20.const_mul x
    have hsub20 : (∫ v : ℝ in Ioi 1,
        spectralMomentKernel 2 x v - spectralMomentKernel 0 x v) =
        spectralMoment 2 x - spectralMoment 0 x :=
      integral_sub (f := fun v : ℝ => spectralMomentKernel 2 x v)
        (g := fun v : ℝ => spectralMomentKernel 0 x v) h2 h0
    have hmul : (∫ v : ℝ in Ioi 1,
        x * (spectralMomentKernel 2 x v - spectralMomentKernel 0 x v)) =
        x * (spectralMoment 2 x - spectralMoment 0 x) := by
      rw [integral_const_mul, hsub20]
    calc
      _ = (∫ v : ℝ in Ioi 1, spectralMomentKernel 1 x v) -
          ∫ v : ℝ in Ioi 1, x * (spectralMomentKernel 2 x v - spectralMomentKernel 0 x v) :=
        integral_sub (f := fun v : ℝ => spectralMomentKernel 1 x v)
          (g := fun v : ℝ => x * (spectralMomentKernel 2 x v - spectralMomentKernel 0 x v)) h1 hx20
      _ = _ := by rw [hmul]; rfl
  rw [hvalue] at hftc
  simp only [spectralFlux, one_pow, sub_self, Real.sqrt_zero, mul_zero, sub_zero] at hftc
  linear_combination -hftc

theorem kSpectral_ode {x : ℝ} (hx : 0 < x) :
    x ^ 2 * kSpectralSecond x + x * kSpectralPrime x - x ^ 2 * kSpectral x = 0 := by
  dsimp only [kSpectral, kSpectralPrime, kSpectralSecond]
  linear_combination x * spectral_moment_ode hx

theorem kSpectralPrime_hasDerivAt_normalized {x : ℝ} (hx : 0 < x) :
    HasDerivAt kSpectralPrime (kSpectral x - kSpectralPrime x / x) x := by
  apply (kSpectralPrime_hasDerivAt hx).congr_deriv
  dsimp only [kSpectral, kSpectralPrime, kSpectralSecond]
  field_simp [hx.ne']
  linear_combination spectral_moment_ode hx

theorem laplaceK_ofReal_eq_kSpectral {x : ℝ} (hx : 0 < x) :
    laplaceK (x : ℂ) = (kSpectral x : ℂ) := by
  rw [laplaceK_ofReal_spectral_integral hx]
  congr 1
  simp only [kSpectral, spectralMoment, spectralMomentKernel, pow_zero, one_mul,
    positiveSpectralKernel]

end J0RadialUniqueness
