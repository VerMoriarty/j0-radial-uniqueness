import Solutions.J0RadialUniqueness.CompactHelmholtzFilter
import Solutions.J0RadialUniqueness.QAnalytic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic

/-! The entire-parameter radial Helmholtz resolvent, including parameter zero.

The B companion is conditioned at the boundary for every complex parameter.
The T formula uses Q and the entire divided difference of harmonicF, so its
definition never divides by the parameter. Only one-dimensional identities are
proved here; no distributional resolvent identity or Paley-Wiener estimate is
postulated or counted as completed.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace J0RadialUniqueness

def harmonicDividedDifference (w : ℂ) : ℂ := dslope harmonicF 0 w

theorem harmonicF_factor_dividedDifference (w : ℂ) :
    harmonicF w = w * harmonicDividedDifference w := by
  have h := sub_smul_dslope harmonicF 0 w
  simpa only [sub_zero, harmonicF_zero, smul_eq_mul, harmonicDividedDifference] using h.symm

@[simp] theorem harmonicDividedDifference_zero : harmonicDividedDifference 0 = 1 := by
  simp only [harmonicDividedDifference, dslope_same]
  have h := harmonicF_firstDerivative_hasSum 0
  rw [← h.tsum_eq, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem harmonicDividedDifference_differentiable : Differentiable ℂ harmonicDividedDifference := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope
    (show (Set.univ : Set ℂ) ∈ 𝓝 (0 : ℂ) from Filter.univ_mem)).mpr
      harmonicF_differentiable.differentiableOn

theorem harmonicDividedDifference_analyticAt (w : ℂ) :
    AnalyticAt ℂ harmonicDividedDifference w :=
  (harmonicDividedDifference_differentiable.differentiableOn.analyticOnNhd isOpen_univ)
    w (Set.mem_univ w)

def helmholtzResolventArg (lam : ℂ) (s : ℝ) : ℂ := -lam ^ 2 * (s : ℂ) ^ 2 / 4

theorem helmholtzP_eq_F_arg (lam : ℂ) (s : ℝ) :
    helmholtzP lam s = F (helmholtzResolventArg lam s) := by
  rw [helmholtzP_eq_J0, J0]
  congr 1
  unfold helmholtzResolventArg
  ring

theorem helmholtzP_sub_one (lam : ℂ) (s : ℝ) :
    helmholtzP lam s - 1 = helmholtzResolventArg lam s * Q (helmholtzResolventArg lam s) := by
  rw [helmholtzP_eq_F_arg]
  exact F_sub_one _

theorem helmholtzH_factor_dividedDifference (lam : ℂ) (s : ℝ) :
    helmholtzH lam s = helmholtzResolventArg lam s * harmonicDividedDifference (helmholtzResolventArg lam s) := by
  rw [helmholtzH_eq_harmonicF]
  exact harmonicF_factor_dividedDifference _

def helmholtzResolventB (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  (-helmholtzLogRatio r s * helmholtzP lam r * helmholtzP lam s +
    helmholtzP lam r * helmholtzH lam s - helmholtzH lam r * helmholtzP lam s) /
      (2 * (Real.pi : ℂ))

def helmholtzResolventBSlope (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  helmholtzP lam r * helmholtzBSlope r lam s - helmholtzB r lam r * helmholtzPSlope lam s

def helmholtzResolventBAccel (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  helmholtzP lam r * helmholtzBAccel r lam s - helmholtzB r lam r * helmholtzPAccel lam s

theorem helmholtzResolventB_eq_determinant {r : ℝ} (hr : 0 < r) (lam : ℂ) (s : ℝ) :
    helmholtzResolventB r lam s =
      helmholtzP lam r * helmholtzB r lam s - helmholtzB r lam r * helmholtzP lam s := by
  unfold helmholtzResolventB helmholtzB
  simp only [helmholtzLogRatio, div_self hr.ne', Real.log_one, Complex.ofReal_zero,
    neg_zero, zero_mul, zero_add]
  ring

theorem helmholtzResolventB_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    HasDerivAt (helmholtzResolventB r lam) (helmholtzResolventBSlope r lam s) s := by
  have heq : helmholtzResolventB r lam = fun t : ℝ =>
      helmholtzP lam r * helmholtzB r lam t - helmholtzB r lam r * helmholtzP lam t :=
    funext (helmholtzResolventB_eq_determinant hr lam)
  rw [heq]
  convert! ((helmholtzB_hasDerivAt hr hs lam).const_mul (helmholtzP lam r)).sub
    ((helmholtzP_hasDerivAt lam s).const_mul (helmholtzB r lam r)) using 1 <;> rfl

theorem helmholtzResolventBSlope_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    HasDerivAt (helmholtzResolventBSlope r lam) (helmholtzResolventBAccel r lam s) s := by
  convert! ((helmholtzBSlope_hasDerivAt hr hs lam).const_mul (helmholtzP lam r)).sub
    ((helmholtzPSlope_hasDerivAt lam s).const_mul (helmholtzB r lam r)) using 1 <;> rfl

theorem helmholtzResolventB_ode {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    helmholtzResolventBAccel r lam s + helmholtzResolventBSlope r lam s / (s : ℂ) +
      lam ^ 2 * helmholtzResolventB r lam s = 0 := by
  rw [helmholtzResolventB_eq_determinant hr]
  unfold helmholtzResolventBAccel helmholtzResolventBSlope
  linear_combination (helmholtzP lam r) * (helmholtzB_ode hr hs lam) -
    (helmholtzB r lam r) * (helmholtzP_ode lam hs)

theorem helmholtzResolventB_deriv_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    HasDerivAt (deriv (helmholtzResolventB r lam)) (helmholtzResolventBAccel r lam s) s := by
  have hnear : deriv (helmholtzResolventB r lam) =ᶠ[𝓝 s] helmholtzResolventBSlope r lam := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (helmholtzResolventB_hasDerivAt hr ht lam).deriv
  exact (helmholtzResolventBSlope_hasDerivAt hr hs lam).congr_of_eventuallyEq hnear

theorem helmholtzResolventB_radial_ode {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    deriv (deriv (helmholtzResolventB r lam)) s + deriv (helmholtzResolventB r lam) s / (s : ℂ) +
      lam ^ 2 * helmholtzResolventB r lam s = 0 := by
  rw [(helmholtzResolventB_deriv_hasDerivAt hr hs lam).deriv,
    (helmholtzResolventB_hasDerivAt hr hs lam).deriv]
  exact helmholtzResolventB_ode hr hs lam

theorem helmholtzResolventB_radius {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    helmholtzResolventB r lam r = 0 := by
  rw [helmholtzResolventB_eq_determinant hr]
  ring

theorem helmholtzResolventBSlope_radius {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    helmholtzResolventBSlope r lam r = -1 / (2 * (Real.pi : ℂ) * (r : ℂ)) := by
  have hw := helmholtzB_wronskian hr hr lam
  have hw' : (r : ℂ) * helmholtzResolventBSlope r lam r = -1 / (2 * (Real.pi : ℂ)) := by
    convert! hw using 1 <;> unfold helmholtzResolventBSlope <;> ring
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    helmholtzResolventBSlope r lam r = ((r : ℂ) * helmholtzResolventBSlope r lam r) / (r : ℂ) := by
      field_simp [hrC]
    _ = (-1 / (2 * (Real.pi : ℂ))) / (r : ℂ) := by rw [hw']
    _ = _ := by rw [div_div]

theorem helmholtzResolventB_deriv_radius {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    deriv (helmholtzResolventB r lam) r = -1 / (2 * (Real.pi : ℂ) * (r : ℂ)) := by
  rw [(helmholtzResolventB_hasDerivAt hr hr lam).deriv]
  exact helmholtzResolventBSlope_radius hr lam

def helmholtzResolventG (r s : ℝ) : ℂ := (Real.log (r / s) : ℂ) / (2 * (Real.pi : ℂ))

/-- The explicit resolvent family; there is no division by lam in this definition. -/
def helmholtzResolventT (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  ((Real.log (r / s) : ℂ) *
      (((r : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam r) * helmholtzP lam s +
        ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)) +
    ((s : ℂ) ^ 2 / 4) * helmholtzP lam r * harmonicDividedDifference (helmholtzResolventArg lam s) -
    ((r : ℂ) ^ 2 / 4) * harmonicDividedDifference (helmholtzResolventArg lam r) * helmholtzP lam s) /
      (2 * (Real.pi : ℂ))

theorem helmholtzLogRatio_inverse {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    helmholtzLogRatio r s = -(Real.log (r / s) : ℂ) := by
  unfold helmholtzLogRatio
  rw [Real.log_div hs.ne' hr.ne', Real.log_div hr.ne' hs.ne']
  push_cast
  ring

/-- Exact cancellation of the apparent parameter pole, including lam = 0. -/
theorem helmholtzResolventT_mul_parameter_sq {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (lam : ℂ) :
    lam ^ 2 * helmholtzResolventT r lam s = helmholtzResolventG r s - helmholtzResolventB r lam s := by
  have hpR : helmholtzP lam r = 1 + helmholtzResolventArg lam r * Q (helmholtzResolventArg lam r) := by
    linear_combination helmholtzP_sub_one lam r
  have hpS : helmholtzP lam s = 1 + helmholtzResolventArg lam s * Q (helmholtzResolventArg lam s) := by
    linear_combination helmholtzP_sub_one lam s
  unfold helmholtzResolventT helmholtzResolventG helmholtzResolventB
  rw [helmholtzLogRatio_inverse hr hs,
    helmholtzH_factor_dividedDifference lam r, helmholtzH_factor_dividedDifference lam s, hpR, hpS]
  unfold helmholtzResolventArg
  ring

@[simp] theorem helmholtzResolventT_zero_parameter (r s : ℝ) :
    helmholtzResolventT r 0 s =
      ((((r : ℂ) ^ 2 + (s : ℂ) ^ 2) / 4) * (Real.log (r / s) : ℂ) +
        ((s : ℂ) ^ 2 - (r : ℂ) ^ 2) / 4) / (2 * (Real.pi : ℂ)) := by
  simp only [helmholtzResolventT, helmholtzResolventArg, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    neg_zero, zero_mul, zero_div, Q_zero, harmonicDividedDifference_zero,
    helmholtzP, modifiedI0, mul_zero, zero_mul, F_zero, mul_one]
  ring

theorem helmholtzResolventT_radius {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    helmholtzResolventT r lam r = 0 := by
  simp only [helmholtzResolventT, div_self hr.ne', Real.log_one, Complex.ofReal_zero, zero_mul, zero_add]
  ring

theorem helmholtzP_parameter_analyticAt (s : ℝ) (lam : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => helmholtzP z s) lam := by
  have harg : AnalyticAt ℂ (fun z : ℂ => helmholtzResolventArg z s) lam := by
    unfold helmholtzResolventArg
    fun_prop
  have heq : (fun z : ℂ => helmholtzP z s) =
      (fun z : ℂ => F (helmholtzResolventArg z s)) := funext (fun z => helmholtzP_eq_F_arg z s)
  rw [heq]
  exact (F_analyticAt (helmholtzResolventArg lam s)).comp (f := fun z : ℂ => helmholtzResolventArg z s) harg

theorem helmholtzH_parameter_analyticAt (s : ℝ) (lam : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => helmholtzH z s) lam := by
  have harg : AnalyticAt ℂ (fun z : ℂ => helmholtzResolventArg z s) lam := by
    unfold helmholtzResolventArg
    fun_prop
  have heq : (fun z : ℂ => helmholtzH z s) =
      (fun z : ℂ => harmonicF (helmholtzResolventArg z s)) :=
    funext (fun z => helmholtzH_eq_harmonicF z s)
  rw [heq]
  exact (harmonicF_analyticAt (helmholtzResolventArg lam s)).comp (f := fun z : ℂ => helmholtzResolventArg z s) harg

theorem helmholtzResolventB_parameter_analyticAt (r s : ℝ) (lam : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => helmholtzResolventB r z s) lam := by
  have hpr := helmholtzP_parameter_analyticAt r lam
  have hps := helmholtzP_parameter_analyticAt s lam
  have hhr := helmholtzH_parameter_analyticAt r lam
  have hhs := helmholtzH_parameter_analyticAt s lam
  unfold helmholtzResolventB
  exact ((((analyticAt_const.mul hpr).mul hps).add (hpr.mul hhs)).sub (hhr.mul hps)).div_const

/-- The entire dependence at the apparent pole is proved using the actual dslope
removable-singularity theorem, rather than defining T by division by lam². -/
theorem helmholtzResolventT_parameter_analyticAt (r s : ℝ) (lam : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => helmholtzResolventT r z s) lam := by
  have har : AnalyticAt ℂ (fun z : ℂ => helmholtzResolventArg z r) lam := by
    unfold helmholtzResolventArg
    fun_prop
  have has : AnalyticAt ℂ (fun z : ℂ => helmholtzResolventArg z s) lam := by
    unfold helmholtzResolventArg
    fun_prop
  have hqr := (Q_analyticAt (helmholtzResolventArg lam r)).comp (f := fun z : ℂ => helmholtzResolventArg z r) har
  have hqs := (Q_analyticAt (helmholtzResolventArg lam s)).comp (f := fun z : ℂ => helmholtzResolventArg z s) has
  have hdr := (harmonicDividedDifference_analyticAt (helmholtzResolventArg lam r)).comp (f := fun z : ℂ => helmholtzResolventArg z r) har
  have hds := (harmonicDividedDifference_analyticAt (helmholtzResolventArg lam s)).comp (f := fun z : ℂ => helmholtzResolventArg z s) has
  have hpr := helmholtzP_parameter_analyticAt r lam
  have hps := helmholtzP_parameter_analyticAt s lam
  unfold helmholtzResolventT
  apply AnalyticAt.div_const
  apply AnalyticAt.sub
  · apply AnalyticAt.add
    · exact analyticAt_const.mul (((analyticAt_const.mul hqr).mul hps).add (analyticAt_const.mul hqs))
    · exact (analyticAt_const.mul hpr).mul hds
  · exact (analyticAt_const.mul hdr).mul hps

def helmholtzResolventMass (r : ℝ) (lam : ℂ) : ℂ :=
  ((r : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam r)

theorem helmholtzResolventMass_mul_parameter_sq (r : ℝ) (lam : ℂ) :
    lam ^ 2 * helmholtzResolventMass r lam = 1 - J0 ((r : ℂ) * lam) := by
  rw [← helmholtzP_eq_J0]
  have h := helmholtzP_sub_one lam r
  unfold helmholtzResolventMass helmholtzResolventArg at *
  linear_combination h

@[simp] theorem helmholtzResolventMass_zero_parameter (r : ℝ) :
    helmholtzResolventMass r 0 = (r : ℂ) ^ 2 / 4 := by
  simp [helmholtzResolventMass, helmholtzResolventArg]

theorem helmholtzResolventMass_parameter_analyticAt (r : ℝ) (lam : ℂ) :
    AnalyticAt ℂ (helmholtzResolventMass r) lam := by
  have harg : AnalyticAt ℂ (fun z : ℂ => helmholtzResolventArg z r) lam := by
    unfold helmholtzResolventArg
    fun_prop
  exact analyticAt_const.mul ((Q_analyticAt (helmholtzResolventArg lam r)).comp (f := fun z : ℂ => helmholtzResolventArg z r) harg)

end J0RadialUniqueness
