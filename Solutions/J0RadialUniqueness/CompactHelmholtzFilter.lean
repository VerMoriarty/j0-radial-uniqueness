import Solutions.J0RadialUniqueness.K0ModifiedODE
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The actual one-dimensional Helmholtz Green companion.

All logarithms here are real `log (s/r)`. The analytic harmonic-number correction
is the independently defined factorial series. Its entire Wronskian identity is
proved from the F/H ODEs, with its constant evaluated at zero; no Paley-Wiener
theorem, compact filter existence or planar PDE is an input.
-/

noncomputable section

open Filter
open scoped Topology

namespace J0RadialUniqueness

def helmholtzP (lam : ℂ) (s : ℝ) : ℂ := modifiedI0 (Complex.I * lam * (s : ℂ))
def helmholtzH (lam : ℂ) (s : ℝ) : ℂ := K0Correction (Complex.I * lam * (s : ℂ))

def helmholtzPSlope (lam : ℂ) (s : ℝ) : ℂ :=
  Complex.I * lam * deriv modifiedI0 (Complex.I * lam * (s : ℂ))
def helmholtzHSlope (lam : ℂ) (s : ℝ) : ℂ :=
  Complex.I * lam * deriv K0Correction (Complex.I * lam * (s : ℂ))

def helmholtzPAccel (lam : ℂ) (s : ℝ) : ℂ :=
  (Complex.I * lam) ^ 2 * deriv (deriv modifiedI0) (Complex.I * lam * (s : ℂ))
def helmholtzHAccel (lam : ℂ) (s : ℝ) : ℂ :=
  (Complex.I * lam) ^ 2 * deriv (deriv K0Correction) (Complex.I * lam * (s : ℂ))

theorem helmholtzP_eq_J0 (lam : ℂ) (s : ℝ) :
    helmholtzP lam s = J0 ((s : ℂ) * lam) := by
  unfold helmholtzP modifiedI0 J0
  congr 1
  rw [mul_pow, mul_pow, Complex.I_sq]
  ring

theorem helmholtzH_eq_harmonicF (lam : ℂ) (s : ℝ) :
    helmholtzH lam s = harmonicF (-lam ^ 2 * (s : ℂ) ^ 2 / 4) := by
  unfold helmholtzH K0Correction
  congr 1
  rw [mul_pow, mul_pow, Complex.I_sq]
  ring

theorem helmholtzP_hasDerivAt (lam : ℂ) (s : ℝ) :
    HasDerivAt (helmholtzP lam) (helmholtzPSlope lam s) s := by
  have h := (modifiedI0_hasDerivAt (Complex.I * lam * (s : ℂ))).comp (s : ℂ)
    ((hasDerivAt_id (s : ℂ)).const_mul (Complex.I * lam))
  have hh := h.comp_ofReal
  convert! hh using 1 <;> simp only [helmholtzP, helmholtzPSlope, modifiedI0_deriv,
    Function.comp_def, id_eq] <;> ring

theorem helmholtzH_hasDerivAt (lam : ℂ) (s : ℝ) :
    HasDerivAt (helmholtzH lam) (helmholtzHSlope lam s) s := by
  have h := (K0Correction_hasDerivAt (Complex.I * lam * (s : ℂ))).comp (s : ℂ)
    ((hasDerivAt_id (s : ℂ)).const_mul (Complex.I * lam))
  have hh := h.comp_ofReal
  convert! hh using 1 <;> simp only [helmholtzH, helmholtzHSlope, K0Correction_deriv,
    Function.comp_def, id_eq] <;> ring

theorem helmholtzPSlope_hasDerivAt (lam : ℂ) (s : ℝ) :
    HasDerivAt (helmholtzPSlope lam) (helmholtzPAccel lam s) s := by
  have h := ((modifiedI0_deriv_hasDerivAt (Complex.I * lam * (s : ℂ))).comp (s : ℂ)
    ((hasDerivAt_id (s : ℂ)).const_mul (Complex.I * lam))).const_mul (Complex.I * lam)
  convert! h.comp_ofReal using 1 <;>
    simp only [helmholtzPSlope, helmholtzPAccel, modifiedI0_secondDerivative,
      Function.comp_def, id_eq] <;> ring

theorem helmholtzHSlope_hasDerivAt (lam : ℂ) (s : ℝ) :
    HasDerivAt (helmholtzHSlope lam) (helmholtzHAccel lam s) s := by
  have h := ((K0Correction_deriv_hasDerivAt (Complex.I * lam * (s : ℂ))).comp (s : ℂ)
    ((hasDerivAt_id (s : ℂ)).const_mul (Complex.I * lam))).const_mul (Complex.I * lam)
  convert! h.comp_ofReal using 1 <;>
    simp only [helmholtzHSlope, helmholtzHAccel, K0Correction_secondDerivative,
      Function.comp_def, id_eq] <;> ring

theorem helmholtzP_scaled_ode (lam : ℂ) (s : ℝ) :
    (s : ℂ) ^ 2 * helmholtzPAccel lam s + (s : ℂ) * helmholtzPSlope lam s +
      lam ^ 2 * (s : ℂ) ^ 2 * helmholtzP lam s = 0 := by
  have h := modifiedI0_ode (Complex.I * lam * (s : ℂ))
  unfold modifiedBesselOperator at h
  simp only [mul_pow, Complex.I_sq] at h
  unfold helmholtzP helmholtzPSlope helmholtzPAccel
  have hI : (Complex.I * lam) ^ 2 = -lam ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  rw [hI]
  linear_combination h

theorem helmholtzH_scaled_ode (lam : ℂ) (s : ℝ) :
    (s : ℂ) ^ 2 * helmholtzHAccel lam s + (s : ℂ) * helmholtzHSlope lam s +
      lam ^ 2 * (s : ℂ) ^ 2 * helmholtzH lam s = 2 * (s : ℂ) * helmholtzPSlope lam s := by
  have h := K0Correction_ode (Complex.I * lam * (s : ℂ))
  unfold modifiedBesselOperator at h
  simp only [mul_pow, Complex.I_sq] at h
  unfold helmholtzH helmholtzHSlope helmholtzHAccel helmholtzPSlope
  have hI : (Complex.I * lam) ^ 2 = -lam ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  rw [hI]
  linear_combination h

theorem helmholtzP_ode (lam : ℂ) {s : ℝ} (hs : 0 < s) :
    helmholtzPAccel lam s + helmholtzPSlope lam s / (s : ℂ) + lam ^ 2 * helmholtzP lam s = 0 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h := congrArg (fun z : ℂ => z / (s : ℂ) ^ 2) (helmholtzP_scaled_ode lam s)
  convert! h using 1 <;> field_simp [hsC] <;> ring

theorem helmholtzH_ode (lam : ℂ) {s : ℝ} (hs : 0 < s) :
    helmholtzHAccel lam s + helmholtzHSlope lam s / (s : ℂ) + lam ^ 2 * helmholtzH lam s =
      2 * helmholtzPSlope lam s / (s : ℂ) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h := congrArg (fun z : ℂ => z / (s : ℂ) ^ 2) (helmholtzH_scaled_ode lam s)
  convert! h using 1 <;> field_simp [hsC] <;> ring

def harmonicSeriesWronskian (w : ℂ) : ℂ :=
  2 * w * (F w * deriv harmonicF w - deriv F w * harmonicF w) - (F w) ^ 2

theorem harmonicSeriesWronskian_hasDerivAt (w : ℂ) :
    HasDerivAt harmonicSeriesWronskian 0 w := by
  have hF := (F_differentiable w).hasDerivAt
  have hF' := (F_deriv_differentiable w).hasDerivAt
  have hH := (harmonicF_differentiable w).hasDerivAt
  have hH' := (harmonicF_deriv_differentiable w).hasDerivAt
  have h := (((hasDerivAt_id w).const_mul (2 : ℂ)).mul
    ((hF.mul hH').sub (hF'.mul hH))).sub (hF.pow 2)
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, one_mul]
  linear_combination (2 * F w) * (harmonicF_ode w) - (2 * harmonicF w) * (F_ode w)

/-- The Wronskian constant is fixed by the actual entire series values at zero. -/
theorem harmonicSeriesWronskian_eq_neg_one (w : ℂ) : harmonicSeriesWronskian w = -1 := by
  have h := is_const_of_deriv_eq_zero
    (fun z => (harmonicSeriesWronskian_hasDerivAt z).differentiableAt)
    (fun z => (harmonicSeriesWronskian_hasDerivAt z).deriv) w 0
  simpa [harmonicSeriesWronskian] using h

theorem helmholtz_pair_wronskian (lam : ℂ) (s : ℝ) :
    (s : ℂ) * (helmholtzP lam s * helmholtzHSlope lam s -
      helmholtzPSlope lam s * helmholtzH lam s) - (helmholtzP lam s) ^ 2 = -1 := by
  have h := harmonicSeriesWronskian_eq_neg_one ((Complex.I * lam * (s : ℂ)) ^ 2 / 4)
  unfold harmonicSeriesWronskian at h
  unfold helmholtzP helmholtzH helmholtzPSlope helmholtzHSlope
  rw [modifiedI0_deriv, K0Correction_deriv]
  unfold quadraticSlope modifiedI0 K0Correction
  linear_combination h

def helmholtzLogRatio (r s : ℝ) : ℂ := (Real.log (s / r) : ℂ)

theorem helmholtzLogRatio_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    HasDerivAt (helmholtzLogRatio r) (s : ℂ)⁻¹ s := by
  have hd : HasDerivAt (fun t : ℝ => Real.log (t / r)) s⁻¹ s := by
    have h := ((hasDerivAt_id s).div_const r).log (div_ne_zero hs.ne' hr.ne')
    apply h.congr_deriv
    simp only [id_eq]
    field_simp [hr.ne', hs.ne']
  have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hd
  convert! h using 1 <;> simp [helmholtzLogRatio, Function.comp_apply, Complex.ofReal_inv]

def helmholtzB (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  (-helmholtzLogRatio r s * helmholtzP lam s + helmholtzH lam s -
    helmholtzH lam r * helmholtzP lam s) / (2 * (Real.pi : ℂ))

def helmholtzBSlope (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  (-(s : ℂ)⁻¹ * helmholtzP lam s - helmholtzLogRatio r s * helmholtzPSlope lam s +
    helmholtzHSlope lam s - helmholtzH lam r * helmholtzPSlope lam s) / (2 * (Real.pi : ℂ))

def helmholtzBAccel (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  (((s : ℂ) ^ 2)⁻¹ * helmholtzP lam s - (2 / (s : ℂ)) * helmholtzPSlope lam s -
    helmholtzLogRatio r s * helmholtzPAccel lam s + helmholtzHAccel lam s -
    helmholtzH lam r * helmholtzPAccel lam s) / (2 * (Real.pi : ℂ))

theorem helmholtzB_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    HasDerivAt (helmholtzB r lam) (helmholtzBSlope r lam s) s := by
  have h := ((((helmholtzLogRatio_hasDerivAt hr hs).neg.mul (helmholtzP_hasDerivAt lam s)).add
    (helmholtzH_hasDerivAt lam s)).sub
      ((helmholtzP_hasDerivAt lam s).const_mul (helmholtzH lam r))).div_const (2 * (Real.pi : ℂ))
  convert! h using 1 <;> simp only [helmholtzB, helmholtzBSlope, Pi.neg_apply] <;> ring

theorem helmholtzBSlope_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    HasDerivAt (helmholtzBSlope r lam) (helmholtzBAccel r lam s) s := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hπ : 2 * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hi := (hasDerivAt_inv hsC).comp_ofReal
  have h := (((((hi.neg.mul (helmholtzP_hasDerivAt lam s)).sub
    ((helmholtzLogRatio_hasDerivAt hr hs).mul (helmholtzPSlope_hasDerivAt lam s))).add
      (helmholtzHSlope_hasDerivAt lam s)).sub
        ((helmholtzPSlope_hasDerivAt lam s).const_mul (helmholtzH lam r))).div_const (2 * (Real.pi : ℂ)))
  convert! h using 1 <;> simp only [helmholtzBSlope, helmholtzBAccel,
    Function.comp_def, Pi.neg_apply, neg_neg] <;> field_simp [hsC, hπ] <;> ring

theorem helmholtzB_ode {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    helmholtzBAccel r lam s + helmholtzBSlope r lam s / (s : ℂ) + lam ^ 2 * helmholtzB r lam s = 0 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hπ : 2 * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have heq : (2 * (Real.pi : ℂ)) *
      (helmholtzBAccel r lam s + helmholtzBSlope r lam s / (s : ℂ) + lam ^ 2 * helmholtzB r lam s) =
      -(helmholtzLogRatio r s + helmholtzH lam r) *
        (helmholtzPAccel lam s + helmholtzPSlope lam s / (s : ℂ) + lam ^ 2 * helmholtzP lam s) +
      (helmholtzHAccel lam s + helmholtzHSlope lam s / (s : ℂ) + lam ^ 2 * helmholtzH lam s) -
      2 * helmholtzPSlope lam s / (s : ℂ) := by
    unfold helmholtzBAccel helmholtzBSlope helmholtzB
    field_simp [hsC, hπ]
    <;> ring
  rw [helmholtzP_ode lam hs, helmholtzH_ode lam hs] at heq
  have hz : (2 * (Real.pi : ℂ)) *
      (helmholtzBAccel r lam s + helmholtzBSlope r lam s / (s : ℂ) + lam ^ 2 * helmholtzB r lam s) = 0 := by
    linear_combination heq
  exact (mul_eq_zero.mp hz).resolve_left hπ

theorem helmholtzB_wronskian {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    (s : ℂ) * (helmholtzP lam s * helmholtzBSlope r lam s -
      helmholtzPSlope lam s * helmholtzB r lam s) = -1 / (2 * (Real.pi : ℂ)) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hπ : 2 * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have heq : (2 * (Real.pi : ℂ)) * ((s : ℂ) *
      (helmholtzP lam s * helmholtzBSlope r lam s - helmholtzPSlope lam s * helmholtzB r lam s)) =
      (s : ℂ) * (helmholtzP lam s * helmholtzHSlope lam s -
        helmholtzPSlope lam s * helmholtzH lam s) - (helmholtzP lam s) ^ 2 := by
    unfold helmholtzBSlope helmholtzB
    field_simp [hsC, hπ]
    <;> ring
  rw [helmholtz_pair_wronskian] at heq
  apply (eq_div_iff hπ).mpr
  simpa only [mul_comm] using heq

theorem helmholtzB_wronskian_tendsto_zero {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Tendsto (fun s : ℝ => (s : ℂ) *
      (helmholtzP lam s * helmholtzBSlope r lam s - helmholtzPSlope lam s * helmholtzB r lam s))
      (𝓝[>] 0) (𝓝 (-1 / (2 * (Real.pi : ℂ)))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (helmholtzB_wronskian hr hs lam).symm

theorem helmholtzB_radius {r : ℝ} (hr : 0 < r) (lam : ℂ)
    (hJ : J0 ((r : ℂ) * lam) = 1) : helmholtzB r lam r = 0 := by
  have hp : helmholtzP lam r = 1 := (helmholtzP_eq_J0 lam r).trans hJ
  simp [helmholtzB, helmholtzLogRatio, hr.ne', hp]

theorem helmholtzBSlope_radius {r : ℝ} (hr : 0 < r) (lam : ℂ)
    (hJ : J0 ((r : ℂ) * lam) = 1) :
    helmholtzBSlope r lam r = -1 / (2 * (Real.pi : ℂ) * (r : ℂ)) := by
  have hp : helmholtzP lam r = 1 := (helmholtzP_eq_J0 lam r).trans hJ
  have hw := helmholtzB_wronskian hr hr lam
  rw [hp, helmholtzB_radius hr lam hJ] at hw
  simp only [one_mul, mul_zero, sub_zero] at hw
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    helmholtzBSlope r lam r = ((r : ℂ) * helmholtzBSlope r lam r) / (r : ℂ) := by
      field_simp [hrC]
    _ = (-1 / (2 * (Real.pi : ℂ))) / (r : ℂ) := by rw [hw]
    _ = _ := by rw [div_div]

theorem helmholtzB_deriv_radius {r : ℝ} (hr : 0 < r) (lam : ℂ)
    (hJ : J0 ((r : ℂ) * lam) = 1) :
    deriv (helmholtzB r lam) r = -1 / (2 * (Real.pi : ℂ) * (r : ℂ)) := by
  rw [(helmholtzB_hasDerivAt hr hr lam).deriv]
  exact helmholtzBSlope_radius hr lam hJ

theorem helmholtzB_deriv_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    HasDerivAt (deriv (helmholtzB r lam)) (helmholtzBAccel r lam s) s := by
  have hnear : deriv (helmholtzB r lam) =ᶠ[𝓝 s] helmholtzBSlope r lam := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (helmholtzB_hasDerivAt hr ht lam).deriv
  exact (helmholtzBSlope_hasDerivAt hr hs lam).congr_of_eventuallyEq hnear

/-- The stated ODE uses the actual first and second real derivatives of B. -/
theorem helmholtzB_radial_ode {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    deriv (deriv (helmholtzB r lam)) s + deriv (helmholtzB r lam) s / (s : ℂ) +
      lam ^ 2 * helmholtzB r lam s = 0 := by
  rw [(helmholtzB_deriv_hasDerivAt hr hs lam).deriv, (helmholtzB_hasDerivAt hr hs lam).deriv]
  exact helmholtzB_ode hr hs lam

end J0RadialUniqueness
