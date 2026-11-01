import Solutions.J0RadialUniqueness.CircleLaplacianODE
import Solutions.J0RadialUniqueness.FODE
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
The actual circular mean of a smooth Helmholtz solution.  Uniqueness at radius
zero is proved by a real energy estimate for arbitrary complex coefficients.
The singular damping term has the favorable sign, so no ordinary initial-value
theorem is used at zero, and no nonvanishing comparison solution is assumed.
-/

noncomputable section

open MeasureTheory Laplacian Set
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

/-- Uniqueness for the regular solution of the singular radial equation, on a
finite positive interval. Only continuity, rather than an ODE at zero, is used
at the singular endpoint. -/
theorem singularRadial_zero_of_initial_zero
    (u v : ℝ → ℂ) (κ : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hu : ContinuousOn u (Icc 0 R)) (hv : ContinuousOn v (Icc 0 R))
    (hdu : ∀ t ∈ Ioo 0 R, HasDerivAt u (v t) t)
    (hdv : ∀ t ∈ Ioo 0 R,
      HasDerivAt v (-v t / (t : ℂ) - κ * u t) t)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0) :
    ∀ t ∈ Icc 0 R, u t = 0 := by
  let C : ℝ := 1 + ‖κ‖
  let E : ℝ → ℝ := fun t => ‖u t‖ ^ 2 + ‖v t‖ ^ 2
  let D : ℝ → ℝ := fun t => 2 * inner ℝ (u t) (v t) +
    2 * inner ℝ (v t) (-v t / (t : ℂ) - κ * u t)
  let W : ℝ → ℝ := fun t => Real.exp (-C * t) * E t
  have hE (t : ℝ) (ht : t ∈ Ioo 0 R) : HasDerivAt E (D t) t :=
    (hdu t ht).norm_sq.add (hdv t ht).norm_sq
  have hD (t : ℝ) (ht : t ∈ Ioo 0 R) : D t ≤ C * E t := by
    have hdiv : v t / (t : ℂ) = t⁻¹ • v t := by
      simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    have hi : inner ℝ (v t) (-v t / (t : ℂ) - κ * u t) =
        -(t⁻¹ * ‖v t‖ ^ 2) + inner ℝ (v t) (-(κ * u t)) := by
      simp only [neg_div, inner_sub_right, inner_neg_right, hdiv,
        real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    have h₁ := real_inner_le_norm (u t) (v t)
    have h₂ : inner ℝ (v t) (-(κ * u t)) ≤ ‖v t‖ * (‖κ‖ * ‖u t‖) := by
      simpa only [norm_neg, norm_mul] using real_inner_le_norm (v t) (-(κ * u t))
    have hdamp : 0 ≤ t⁻¹ * ‖v t‖ ^ 2 :=
      mul_nonneg (inv_nonneg.mpr ht.1.le) (sq_nonneg _)
    have hcross : 2 * ‖u t‖ * ‖v t‖ ≤ ‖u t‖ ^ 2 + ‖v t‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖u t‖ - ‖v t‖)]
    have hcrossκ := mul_le_mul_of_nonneg_left hcross (norm_nonneg κ)
    dsimp only [D, C, E]
    rw [hi]
    nlinarith only [h₁, h₂, hdamp, hcross, hcrossκ]
  have hW (t : ℝ) (ht : t ∈ Ioo 0 R) :
      HasDerivAt W (Real.exp (-C * t) * (D t - C * E t)) t := by
    have he := (((hasDerivAt_id t).const_mul (-C)).exp).mul (hE t ht)
    convert! he using 1 <;> simp only [id_eq, mul_one] <;> ring
  have hWcont : ContinuousOn W (Icc 0 R) := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((hu.norm.pow 2).add (hv.norm.pow 2))
  have hanti : AntitoneOn W (Icc 0 R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R) hWcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hW t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hW t ht).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hD t ht))
  intro t ht
  have hzero : W 0 = 0 := by simp [W, E, hu0, hv0]
  have hle : W t ≤ 0 := by
    simpa only [hzero] using hanti (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl, hR⟩) ht ht.1
  have hEnonpos : E t ≤ 0 := by
    have hscaled : Real.exp (-C * t) * E t ≤ Real.exp (-C * t) * 0 := by
      simpa only [W, mul_zero] using hle
    by_contra hn
    have he : 0 < E t := lt_of_not_ge hn
    have hw : 0 < Real.exp (-C * t) * E t := mul_pos (Real.exp_pos _) he
    simp only [mul_zero] at hscaled
    linarith
  have hnorm : ‖u t‖ = 0 := by
    dsimp only [E] at hEnonpos
    nlinarith [sq_nonneg ‖v t‖, norm_nonneg (u t)]
  exact norm_eq_zero.mp hnorm

/-- The factorial-series model of the regular radial solution. -/
def quadraticFProfile (a : ℂ) (t : ℝ) : ℂ := F (a * (t : ℂ) ^ 2)

def quadraticFSlope (a : ℂ) (t : ℝ) : ℂ :=
  (2 * a * (t : ℂ)) * deriv F (a * (t : ℂ) ^ 2)

def quadraticFAccel (a : ℂ) (t : ℝ) : ℂ :=
  (2 * a * (t : ℂ)) ^ 2 * deriv (deriv F) (a * (t : ℂ) ^ 2) +
    (2 * a) * deriv F (a * (t : ℂ) ^ 2)

theorem quadraticFProfile_hasDerivAt (a : ℂ) (t : ℝ) :
    HasDerivAt (quadraticFProfile a) (quadraticFSlope a t) t := by
  have hp : HasDerivAt (fun z : ℂ => a * z ^ 2) (2 * a * (t : ℂ)) (t : ℂ) := by
    convert! ((hasDerivAt_id (t : ℂ)).pow 2).const_mul a using 1 <;>
      simp only [id_eq, mul_one] <;> ring
  have hh := ((F_differentiable (a * (t : ℂ) ^ 2)).hasDerivAt.comp (t : ℂ) hp).comp_ofReal
  convert! hh using 1 <;> simp only [quadraticFProfile, quadraticFSlope] <;> ring

theorem quadraticFSlope_hasDerivAt (a : ℂ) (t : ℝ) :
    HasDerivAt (quadraticFSlope a) (quadraticFAccel a t) t := by
  have hp : HasDerivAt (fun z : ℂ => a * z ^ 2) (2 * a * (t : ℂ)) (t : ℂ) := by
    convert! ((hasDerivAt_id (t : ℂ)).pow 2).const_mul a using 1 <;>
      simp only [id_eq, mul_one] <;> ring
  have hdf := ((F_deriv_differentiable (a * (t : ℂ) ^ 2)).hasDerivAt.comp
    (t : ℂ) hp).comp_ofReal
  have hlin := ((hasDerivAt_id (t : ℂ)).const_mul (2 * a)).comp_ofReal
  have hh := hlin.mul hdf
  convert! hh using 1 <;>
    simp only [quadraticFSlope, quadraticFAccel, id_eq, mul_one, Function.comp_def,
      Pi.mul_apply] <;> ring

@[simp] theorem quadraticFProfile_zero (a : ℂ) : quadraticFProfile a 0 = 1 := by
  simp [quadraticFProfile]

@[simp] theorem quadraticFSlope_zero (a : ℂ) : quadraticFSlope a 0 = 0 := by
  simp [quadraticFSlope]

theorem quadraticFProfile_radial_ode (a : ℂ) {t : ℝ} (ht : 0 < t) :
    quadraticFAccel a t + quadraticFSlope a t / (t : ℂ) =
      (4 * a) * quadraticFProfile a t := by
  have h := F_ode (a * (t : ℂ) ^ 2)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  dsimp only [quadraticFAccel, quadraticFSlope, quadraticFProfile]
  field_simp [htC]
  linear_combination (4 * a) * h

theorem quadraticFProfile_eq_J0 (lam : ℂ) (t : ℝ) :
    quadraticFProfile (-(lam ^ 2) / 4) t = J0 ((t : ℂ) * lam) := by
  unfold quadraticFProfile J0
  congr 1
  ring

theorem integral_circleDirection_eq_zero :
    (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circleDirection t) = 0 := by
  have heq : circleDirection = fun t : ℝ =>
      Real.cos t • circleAxis0 + Real.sin t • circleAxis1 := funext circleDirection_eq_axes
  have hcos : IntervalIntegrable (fun t : ℝ => Real.cos t • circleAxis0)
      volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.smul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hsin : IntervalIntegrable (fun t : ℝ => Real.sin t • circleAxis1)
      volume 0 (2 * Real.pi) :=
    (Real.continuous_sin.smul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  rw [heq]
  change (∫ t : ℝ in (0 : ℝ)..(2 * Real.pi),
    Real.cos t • circleAxis0 + Real.sin t • circleAxis1) = 0
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    integral_cos, integral_sin]
  simp

@[simp] theorem circleRadialSlope_zero (f : Plane → ℂ) (x : Plane) :
    circleRadialSlope f x 0 = 0 := by
  unfold circleRadialSlope circleSlopeIntegrand
  simp only [zero_smul, add_zero]
  rw [(fderiv ℝ f x).intervalIntegral_comp_comm
    (continuous_circleDirection.intervalIntegrable (μ := volume) 0 (2 * Real.pi)),
    integral_circleDirection_eq_zero, map_zero, smul_zero]

theorem circularMean_const_mul (c : ℂ) (f : Plane → ℂ) (r : ℝ) (x : Plane) :
    circularMean (fun y => c * f y) r x = c * circularMean f r x := by
  simp only [circularMean, Complex.real_smul, intervalIntegral.integral_const_mul]
  ring

theorem circularMean_helmholtz_on_closedBall {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (lam : ℂ) (x : Plane) {R : ℝ} (hR : 0 ≤ R)
    (hΔ : ∀ y ∈ Metric.closedBall x R, laplacian f y = -(lam ^ 2) * f y)
    {r : ℝ} (hr : r ∈ Icc 0 R) :
    circularMean f r x = J0 ((r : ℂ) * lam) * f x := by
  let a : ℂ := -(lam ^ 2) / 4
  let u : ℝ → ℂ := fun t => circleProfile f x t - quadraticFProfile a t * f x
  let v : ℝ → ℂ := fun t => circleRadialSlope f x t - quadraticFSlope a t * f x
  have huc : Continuous u := by
    exact (continuous_iff_continuousAt.mpr
      (fun t => (circleProfile_hasDerivAt hf x t).continuousAt)).sub
        ((continuous_iff_continuousAt.mpr
          (fun t => (quadraticFProfile_hasDerivAt a t).continuousAt)).mul continuous_const)
  have hvc : Continuous v := by
    exact (continuous_iff_continuousAt.mpr
      (fun t => (circleRadialSlope_hasDerivAt hf x t).continuousAt)).sub
        ((continuous_iff_continuousAt.mpr
          (fun t => (quadraticFSlope_hasDerivAt a t).continuousAt)).mul continuous_const)
  have hdu (t : ℝ) (_ht : t ∈ Ioo 0 R) : HasDerivAt u (v t) t :=
    (circleProfile_hasDerivAt hf x t).sub ((quadraticFProfile_hasDerivAt a t).mul_const (f x))
  have hmeanΔ (t : ℝ) (ht : t ∈ Ioo 0 R) :
      circularMean (laplacian f) t x = -(lam ^ 2) * circleProfile f x t := by
    calc
      circularMean (laplacian f) t x = circularMean (fun y => -(lam ^ 2) * f y) t x := by
        unfold circularMean
        congr 1
        apply intervalIntegral.integral_congr
        intro θ _
        apply hΔ
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, norm_circleDirection, mul_one, abs_of_pos ht.1]
        exact ht.2.le
      _ = _ := circularMean_const_mul _ _ _ _
  have hrad (t : ℝ) (ht : t ∈ Ioo 0 R) :
      circleRadialAccel f x t + circleRadialSlope f x t / (t : ℂ) =
        -(lam ^ 2) * circleProfile f x t := by
    have hh := circleProfile_radial_ode hf x ht.1
    rw [circleProfile_second_deriv hf x t, circleProfile_deriv hf x t,
      hmeanΔ t ht] at hh
    exact hh
  have hdv (t : ℝ) (ht : t ∈ Ioo 0 R) :
      HasDerivAt v (-v t / (t : ℂ) - lam ^ 2 * u t) t := by
    have hh := (circleRadialSlope_hasDerivAt hf x t).sub
      ((quadraticFSlope_hasDerivAt a t).mul_const (f x))
    apply hh.congr_deriv
    have hm := quadraticFProfile_radial_ode a ht.1
    have ha : 4 * a = -(lam ^ 2) := by dsimp [a]; ring
    rw [ha] at hm
    dsimp only [u, v]
    linear_combination hrad t ht - (f x) * hm
  have hu0 : u 0 = 0 := by simp [u]
  have hv0 : v 0 = 0 := by simp [v]
  have hz := singularRadial_zero_of_initial_zero u v (lam ^ 2) hR
    huc.continuousOn hvc.continuousOn hdu hdv hu0 hv0 r hr
  change circleProfile f x r - quadraticFProfile a r * f x = 0 at hz
  rw [sub_eq_zero] at hz
  rw [show a = -(lam ^ 2) / 4 from rfl, quadraticFProfile_eq_J0] at hz
  exact hz

/-- The global Helmholtz mean formula, for every nonnegative radius and every
complex spectral parameter, including zero. -/
theorem circularMean_helmholtz {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (lam : ℂ) (hΔ : ∀ y, laplacian f y = -(lam ^ 2) * f y)
    {r : ℝ} (hr : 0 ≤ r) (x : Plane) :
    circularMean f r x = J0 ((r : ℂ) * lam) * f x := by
  exact circularMean_helmholtz_on_closedBall hf lam x hr (fun y _ => hΔ y) ⟨hr, le_rfl⟩

end J0RadialUniqueness
