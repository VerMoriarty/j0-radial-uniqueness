import Solutions.J0RadialUniqueness.CompactHelmholtzResolvent
import Solutions.J0RadialUniqueness.CircleGreenIdentity
import Mathlib.Tactic

/-!
The actual radial weak identity of the entire-parameter Helmholtz resolvent.
Weighted B and B' are extended continuously by their explicit formulas. The
Wronskian primitive is assigned its actual limiting value at zero; neither the
ODE nor differentiation of a logarithm is used at the singular endpoint.
-/

noncomputable section

open Filter MeasureTheory Laplacian
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

@[simp] theorem helmholtzP_zero (lam : ℂ) : helmholtzP lam 0 = 1 := by
  simp [helmholtzP, modifiedI0]

@[simp] theorem helmholtzH_zero (lam : ℂ) : helmholtzH lam 0 = 0 := by
  simp [helmholtzH, K0Correction]

theorem continuous_helmholtzP (lam : ℂ) : Continuous (helmholtzP lam) :=
  continuous_iff_continuousAt.mpr (fun s => (helmholtzP_hasDerivAt lam s).continuousAt)

theorem continuous_helmholtzH (lam : ℂ) : Continuous (helmholtzH lam) :=
  continuous_iff_continuousAt.mpr (fun s => (helmholtzH_hasDerivAt lam s).continuousAt)

theorem continuous_helmholtzPSlope (lam : ℂ) : Continuous (helmholtzPSlope lam) :=
  continuous_iff_continuousAt.mpr (fun s => (helmholtzPSlope_hasDerivAt lam s).continuousAt)

theorem continuous_helmholtzHSlope (lam : ℂ) : Continuous (helmholtzHSlope lam) :=
  continuous_iff_continuousAt.mpr (fun s => (helmholtzHSlope_hasDerivAt lam s).continuousAt)

def helmholtzResolventWeightedB (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  ((greenRadialWeight r s : ℂ) * helmholtzP lam r * helmholtzP lam s +
    (s : ℂ) * (helmholtzP lam r * helmholtzH lam s - helmholtzH lam r * helmholtzP lam s)) /
      (2 * (Real.pi : ℂ))

def helmholtzResolventWeightedBSlope (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  (-helmholtzP lam r * helmholtzP lam s +
    (greenRadialWeight r s : ℂ) * helmholtzP lam r * helmholtzPSlope lam s +
    (s : ℂ) * (helmholtzP lam r * helmholtzHSlope lam s - helmholtzH lam r * helmholtzPSlope lam s)) /
      (2 * (Real.pi : ℂ))

theorem continuous_helmholtzResolventWeightedB {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Continuous (helmholtzResolventWeightedB r lam) := by
  unfold helmholtzResolventWeightedB
  exact ((((Complex.continuous_ofReal.comp (continuous_greenRadialWeight hr)).mul
    continuous_const).mul (continuous_helmholtzP lam)).add
      (Complex.continuous_ofReal.mul
        ((continuous_const.mul (continuous_helmholtzH lam)).sub
          (continuous_const.mul (continuous_helmholtzP lam))))).div_const _

theorem continuous_helmholtzResolventWeightedBSlope {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Continuous (helmholtzResolventWeightedBSlope r lam) := by
  unfold helmholtzResolventWeightedBSlope
  exact (((continuous_const.mul (continuous_helmholtzP lam)).add
    (((Complex.continuous_ofReal.comp (continuous_greenRadialWeight hr)).mul continuous_const).mul
      (continuous_helmholtzPSlope lam))).add
        (Complex.continuous_ofReal.mul
          ((continuous_const.mul (continuous_helmholtzHSlope lam)).sub
            (continuous_const.mul (continuous_helmholtzPSlope lam))))).div_const _

@[simp] theorem helmholtzResolventWeightedB_zero (r : ℝ) (lam : ℂ) :
    helmholtzResolventWeightedB r lam 0 = 0 := by
  simp [helmholtzResolventWeightedB, greenRadialWeight]

@[simp] theorem helmholtzResolventWeightedBSlope_zero (r : ℝ) (lam : ℂ) :
    helmholtzResolventWeightedBSlope r lam 0 = -helmholtzP lam r / (2 * (Real.pi : ℂ)) := by
  simp [helmholtzResolventWeightedBSlope, greenRadialWeight]

theorem helmholtzLogRatio_inverse_all (r s : ℝ) :
    helmholtzLogRatio r s = -(Real.log (r / s) : ℂ) := by
  have he : s / r = (r / s)⁻¹ := by rw [inv_div]
  rw [helmholtzLogRatio, he, Real.log_inv, Complex.ofReal_neg]

theorem helmholtzResolventWeightedB_eq (r : ℝ) (lam : ℂ) (s : ℝ) :
    helmholtzResolventWeightedB r lam s = (s : ℂ) * helmholtzResolventB r lam s := by
  unfold helmholtzResolventWeightedB helmholtzResolventB
  rw [helmholtzLogRatio_inverse_all]
  simp only [greenRadialWeight, Complex.ofReal_mul]
  ring

theorem helmholtzResolventWeightedBSlope_eq {r s : ℝ} (hr : 0 < r)
    (hs : s ≠ 0) (lam : ℂ) :
    helmholtzResolventWeightedBSlope r lam s = (s : ℂ) * helmholtzResolventBSlope r lam s := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hpi : 2 * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  unfold helmholtzResolventWeightedBSlope helmholtzResolventBSlope helmholtzBSlope helmholtzB
  rw [helmholtzLogRatio_inverse_all r s]
  simp only [helmholtzLogRatio, div_self hr.ne', Real.log_one, Complex.ofReal_zero,
    neg_zero, zero_mul, zero_add, greenRadialWeight, Complex.ofReal_mul]
  field_simp [hsC, hpi]
  ring

/-- The genuine right endpoint limit of sB, proved by its continuous extension. -/
theorem helmholtzResolventB_weighted_tendsto_zero {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Tendsto (fun s : ℝ => (s : ℂ) * helmholtzResolventB r lam s)
      (𝓝[>] 0) (𝓝 0) := by
  have hh : Tendsto (helmholtzResolventWeightedB r lam) (𝓝[>] 0) (𝓝 0) := by
    simpa only [helmholtzResolventWeightedB_zero] using
      (continuous_helmholtzResolventWeightedB hr lam).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he : helmholtzResolventWeightedB r lam =
      (fun s : ℝ => (s : ℂ) * helmholtzResolventB r lam s) :=
    funext (helmholtzResolventWeightedB_eq r lam)
  rw [he] at hh
  exact hh

/-- The slope extension has a nonzero zero-radius limit, despite the totalized
formula for B' itself having a different value at zero. -/
theorem helmholtzResolventBSlope_weighted_tendsto_zero {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Tendsto (fun s : ℝ => (s : ℂ) * helmholtzResolventBSlope r lam s)
      (𝓝[>] 0) (𝓝 (-helmholtzP lam r / (2 * (Real.pi : ℂ)))) := by
  have hh : Tendsto (helmholtzResolventWeightedBSlope r lam) (𝓝[>] 0)
      (𝓝 (-helmholtzP lam r / (2 * (Real.pi : ℂ)))) := by
    simpa only [helmholtzResolventWeightedBSlope_zero] using
      (continuous_helmholtzResolventWeightedBSlope hr lam).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact helmholtzResolventWeightedBSlope_eq hr hs.ne' lam

theorem helmholtzResolventB_deriv_weighted_tendsto_zero {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Tendsto (fun s : ℝ => (s : ℂ) * deriv (helmholtzResolventB r lam) s)
      (𝓝[>] 0) (𝓝 (-helmholtzP lam r / (2 * (Real.pi : ℂ)))) := by
  apply (helmholtzResolventBSlope_weighted_tendsto_zero hr lam).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [(helmholtzResolventB_hasDerivAt hr hs lam).deriv]

def helmholtzResolventPrimitive (f : Plane → ℂ) (x : Plane) (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  if s = 0 then helmholtzP lam r * f x else
    (2 * (Real.pi : ℂ)) * (s : ℂ) *
      (helmholtzResolventB r lam s * circleRadialSlope f x s -
        helmholtzResolventBSlope r lam s * circleProfile f x s)

theorem helmholtzResolventPrimitive_eq_extension (f : Plane → ℂ) (x : Plane)
    {r : ℝ} (hr : 0 < r) (lam : ℂ) (s : ℝ) :
    helmholtzResolventPrimitive f x r lam s = (2 * (Real.pi : ℂ)) *
      (helmholtzResolventWeightedB r lam s * circleRadialSlope f x s -
        helmholtzResolventWeightedBSlope r lam s * circleProfile f x s) := by
  by_cases hs : s = 0
  · subst s
    simp only [helmholtzResolventPrimitive, if_pos rfl, ite_true,
      helmholtzResolventWeightedB_zero, helmholtzResolventWeightedBSlope_zero,
      circleProfile_zero, zero_mul, zero_sub]
    have hpi : 2 * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    field_simp [hpi]
  · rw [helmholtzResolventPrimitive, if_neg hs, helmholtzResolventWeightedB_eq,
      helmholtzResolventWeightedBSlope_eq hr hs]
    ring

theorem continuous_helmholtzResolventPrimitive {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Continuous (helmholtzResolventPrimitive f x r lam) := by
  have he : helmholtzResolventPrimitive f x r lam = fun s => (2 * (Real.pi : ℂ)) *
      (helmholtzResolventWeightedB r lam s * circleRadialSlope f x s -
        helmholtzResolventWeightedBSlope r lam s * circleProfile f x s) :=
    funext (helmholtzResolventPrimitive_eq_extension f x hr lam)
  rw [he]
  exact continuous_const.mul
    (((continuous_helmholtzResolventWeightedB hr lam).mul
      (circleRadialSlope_differentiable hf x).continuous).sub
        ((continuous_helmholtzResolventWeightedBSlope hr lam).mul
          (circleProfile_differentiable hf x).continuous))

def helmholtzResolventRadialIntegrand (f : Plane → ℂ) (x : Plane) (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s *
    (circleProfile (laplacian f) x s + lam ^ 2 * circleProfile f x s)

theorem continuous_helmholtzResolventRadialIntegrand {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Continuous (helmholtzResolventRadialIntegrand f x r lam) :=
  (continuous_const.mul (continuous_helmholtzResolventWeightedB hr lam)).mul
    (((circleProfile_differentiable (laplacian_contDiff_infty hf) x).continuous).add
      (continuous_const.mul (circleProfile_differentiable hf x).continuous))

theorem helmholtzResolventPrimitive_hasDerivAt {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    HasDerivAt (helmholtzResolventPrimitive f x r lam)
      (helmholtzResolventRadialIntegrand f x r lam s) s := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hdId : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) s := by
    convert! (hasDerivAt_id (s : ℂ)).comp_ofReal using 1 <;> rfl
  have hh := (hdId.mul
    (((helmholtzResolventB_hasDerivAt hr hs lam).mul (circleRadialSlope_hasDerivAt hf x s)).sub
      ((helmholtzResolventBSlope_hasDerivAt hr hs lam).mul (circleProfile_hasDerivAt hf x s)))).const_mul
        (2 * (Real.pi : ℂ))
  have he : helmholtzResolventPrimitive f x r lam =ᶠ[𝓝 s] fun t : ℝ =>
      (2 * (Real.pi : ℂ)) * ((t : ℂ) *
        (helmholtzResolventB r lam t * circleRadialSlope f x t -
          helmholtzResolventBSlope r lam t * circleProfile f x t)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    have htpos : 0 < t := ht
    simp only [helmholtzResolventPrimitive, if_neg htpos.ne']
    ring
  have hh' := hh.congr_of_eventuallyEq he
  apply hh'.congr_deriv
  have hm := circleProfile_radial_ode hf x hs
  rw [circleProfile_second_deriv hf x s, circleProfile_deriv hf x s] at hm
  have hb := helmholtzResolventB_ode hr hs lam
  field_simp [hsC] at hm hb
  simp only [id_eq, Pi.mul_apply, Pi.sub_apply, one_mul,
    helmholtzResolventRadialIntegrand, helmholtzResolventWeightedB_eq, circleProfile]
  linear_combination (2 * (Real.pi : ℂ) * helmholtzResolventB r lam s) * hm -
    (2 * (Real.pi : ℂ) * circularMean f s x) * hb

@[simp] theorem helmholtzResolventPrimitive_zero (f : Plane → ℂ) (x : Plane) (r : ℝ) (lam : ℂ) :
    helmholtzResolventPrimitive f x r lam 0 = helmholtzP lam r * f x := by
  simp only [helmholtzResolventPrimitive, if_pos rfl, ite_true]

@[simp] theorem helmholtzResolventPrimitive_radius (f : Plane → ℂ) (x : Plane)
    {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    helmholtzResolventPrimitive f x r lam r = circularMean f r x := by
  rw [helmholtzResolventPrimitive, if_neg hr.ne', helmholtzResolventB_radius hr,
    helmholtzResolventBSlope_radius hr]
  simp only [zero_mul, zero_sub, circleProfile]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpi : 2 * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  field_simp [hrC, hpi]

/-- The radial weak B identity for the actual circular means of an arbitrary
smooth function. Its boundary factor is P(r), with no spectral root hypothesis. -/
theorem integral_helmholtzResolventB_circle_laplacian {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    (∫ s : ℝ in (0 : ℝ)..r, (2 * (Real.pi : ℂ) * (s : ℂ) * helmholtzResolventB r lam s) *
      (circularMean (laplacian f) s x + lam ^ 2 * circularMean f s x)) =
        circularMean f r x - helmholtzP lam r * f x := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.le
    (continuous_helmholtzResolventPrimitive hf x hr lam).continuousOn
    (fun s hs => helmholtzResolventPrimitive_hasDerivAt hf x hr hs.1 lam)
    ((continuous_helmholtzResolventRadialIntegrand hf x hr lam).intervalIntegrable
      (μ := volume) 0 r)
  simpa only [helmholtzResolventRadialIntegrand, helmholtzResolventWeightedB_eq,
    circleProfile, helmholtzResolventPrimitive_zero, helmholtzResolventPrimitive_radius f x hr,
    mul_assoc] using hh

end J0RadialUniqueness
