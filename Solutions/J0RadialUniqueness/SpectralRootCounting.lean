import Solutions.J0RadialUniqueness.EntireSeriesGrowth
import Solutions.J0RadialUniqueness.SpectralNoCommonZeros
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Data.Set.Card

/-! Actual zero counting for the normalized mean-defect spectrum. Removing the
double zero at the origin gives a function with value one there. Its proven
order-one bound and Jensen's inequality give a linear bound for the number of
nonzero Bessel one-points. These results do not assume a zero enumeration or a
root asymptotic formula. -/

noncomputable section
open Set Filter Metric MeromorphicOn
open scoped Topology Classical

namespace J0RadialUniqueness

def normalizedResolventMass (r : ℝ) (z : ℂ) : ℂ :=
  Q (helmholtzResolventArg z r)

@[simp] theorem normalizedResolventMass_zero (r : ℝ) :
    normalizedResolventMass r 0 = 1 := by
  simp [normalizedResolventMass, helmholtzResolventArg]

theorem normalizedResolventMass_analyticAt (r : ℝ) (z : ℂ) :
    AnalyticAt ℂ (normalizedResolventMass r) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => helmholtzResolventArg w r) z := by
    unfold helmholtzResolventArg
    fun_prop
  exact (Q_analyticAt _).comp ha

theorem normalizedResolventMass_norm_le {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖normalizedResolventMass r z‖ ≤ Real.exp (r * ‖z‖) :=
  norm_Q_helmholtzResolventArg_le hr z

theorem helmholtzResolventMass_eq_const_mul_normalized (r : ℝ) (z : ℂ) :
    helmholtzResolventMass r z = ((r : ℂ) ^ 2 / 4) * normalizedResolventMass r z := rfl

theorem normalizedResolventMass_deriv_ne_zero_at_root {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : normalizedResolventMass r z = 0) :
    deriv (normalizedResolventMass r) z ≠ 0 := by
  have hmass : helmholtzResolventMass r z = 0 := by
    rw [helmholtzResolventMass_eq_const_mul_normalized, hz, mul_zero]
  have hd : HasDerivAt (helmholtzResolventMass r)
      (((r : ℂ) ^ 2 / 4) * deriv (normalizedResolventMass r) z) z :=
    (normalizedResolventMass_analyticAt r z).differentiableAt.hasDerivAt.const_mul _
  intro hzero
  apply helmholtzResolventMass_deriv_ne_zero_at_root hr hmass
  rw [hd.deriv, hzero, mul_zero]

theorem normalizedResolventMass_order_at_root {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : normalizedResolventMass r z = 0) :
    analyticOrderAt (normalizedResolventMass r) z = 1 :=
  (normalizedResolventMass_analyticAt r z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    hz (normalizedResolventMass_deriv_ne_zero_at_root hr hz)

def spectralRootsInClosedBall (r R : ℝ) : Set ℂ :=
  {z | z ∈ closedBall (0 : ℂ) R ∧ normalizedResolventMass r z = 0}

theorem normalizedResolventMass_divisor_apply {r : ℝ} (hr : 0 < r)
    (R : ℝ) (z : ℂ) :
    divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R) z =
      if z ∈ spectralRootsInClosedBall r R then (1 : ℤ) else 0 := by
  classical
  have ha : AnalyticOnNhd ℂ (normalizedResolventMass r) (closedBall (0 : ℂ) R) :=
    fun w _ => normalizedResolventMass_analyticAt r w
  by_cases hb : z ∈ closedBall (0 : ℂ) R
  · rw [ha.divisor_apply hb]
    by_cases hz : normalizedResolventMass r z = 0
    · have hm : z ∈ spectralRootsInClosedBall r R := ⟨hb, hz⟩
      rw [if_pos hm, normalizedResolventMass_order_at_root hr hz]
      rfl
    · have ho := (normalizedResolventMass_analyticAt r z).analyticOrderAt_eq_zero.mpr hz
      have hm : z ∉ spectralRootsInClosedBall r R := fun h => hz h.2
      rw [if_neg hm, ho]
      rfl
  · have hd : divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R) z = 0 :=
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb
    have hm : z ∉ spectralRootsInClosedBall r R := fun h => hb h.1
    rw [hd, if_neg hm]

theorem spectralRootsInClosedBall_finite {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (spectralRootsInClosedBall r R).Finite := by
  classical
  have he : spectralRootsInClosedBall r R =
      (divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R)).support := by
    ext z
    simp only [Function.mem_support, normalizedResolventMass_divisor_apply hr]
    by_cases hz : z ∈ spectralRootsInClosedBall r R <;> simp [hz]
  rw [he]
  exact (divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R)).finiteSupport
    (isCompact_closedBall (0 : ℂ) R)

theorem spectralRootsInClosedBall_ncard_eq_divisor_sum {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∑ᶠ z : ℂ, divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R) z) =
      ((spectralRootsInClosedBall r R).ncard : ℤ) := by
  classical
  have hf := spectralRootsInClosedBall_finite hr R
  have hs : Function.support
      (fun z : ℂ => divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R) z) ⊆
      hf.toFinset := by
    intro z hz
    apply hf.mem_toFinset.mpr
    by_contra hn
    exact hz (by simp only [normalizedResolventMass_divisor_apply hr, if_neg hn])
  calc
    _ = ∑ z ∈ hf.toFinset, (1 : ℤ) := by
      rw [finsum_eq_sum_of_support_subset _ hs]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [normalizedResolventMass_divisor_apply hr, if_pos (hf.mem_toFinset.mp hz)]
    _ = _ := by simp [Set.ncard_eq_toFinset_card _ hf]

/-- Jensen's inequality applied at radii R and 2R to the actual normalized
spectrum, using its already proved exp(r‖z‖) bound and value one at zero. -/
theorem normalizedResolventMass_divisor_sum_le {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ((∑ᶠ z : ℂ, divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R) z : ℤ) : ℝ) ≤
      (2 * r * R) / Real.log 2 := by
  have ha : AnalyticOnNhd ℂ (normalizedResolventMass r)
      (closedBall (0 : ℂ) |2 * R|) := fun z _ => normalizedResolventMass_analyticAt r z
  have hb : ∀ z ∈ sphere (0 : ℂ) |2 * R|,
      ‖normalizedResolventMass r z‖ ≤ Real.exp (2 * r * R) := by
    intro z hz
    have hn : ‖z‖ = 2 * R := by
      simpa only [mem_sphere, dist_zero_right, abs_of_pos (by positivity : 0 < 2 * R)] using hz
    have hh := normalizedResolventMass_norm_le hr.le z
    rw [hn] at hh
    convert! hh using 1 <;> ring
  have hj := AnalyticOnNhd.sum_divisor_le
    (f := normalizedResolventMass r) (c := (0 : ℂ)) (r := R) (R := 2 * R)
    (M := Real.exp (2 * r * R))
    (by simpa only [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR, abs_of_pos (by positivity : 0 < 2 * R)]; linarith)
    (by rw [Real.one_le_exp_iff]; positivity) ha (by simp) hb
  have hquot : (2 * R) / R = 2 := by field_simp [hR.ne']
  have hD :
      (fun z : ℂ => divisor (normalizedResolventMass r) (closedBall (0 : ℂ) |R|) z) =
      (fun z : ℂ => divisor (normalizedResolventMass r) (closedBall (0 : ℂ) R) z) :=
    congrArg (fun T : Set ℂ => fun z : ℂ => divisor (normalizedResolventMass r) T z)
      (congrArg (fun a : ℝ => closedBall (0 : ℂ) a) (abs_of_pos hR))
  rw [hD] at hj
  simpa only [normalizedResolventMass_zero, norm_one,
    div_one, Real.log_exp, hquot] using hj

theorem spectralRootsInClosedBall_ncard_le {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ((spectralRootsInClosedBall r R).ncard : ℝ) ≤ (2 * r / Real.log 2) * R := by
  have hj := normalizedResolventMass_divisor_sum_le hr hR
  rw [spectralRootsInClosedBall_ncard_eq_divisor_sum hr] at hj
  calc
    ((spectralRootsInClosedBall r R).ncard : ℝ) ≤ (2 * r * R) / Real.log 2 := by
      exact_mod_cast hj
    _ = _ := by ring

theorem normalizedResolventMass_one_root_iff (z : ℂ) :
    normalizedResolventMass 1 z = 0 ↔ z ∈ onePoints := by
  have he : helmholtzResolventMass 1 z = (1 / 4 : ℂ) * normalizedResolventMass 1 z := by
    simpa only [Complex.ofReal_one, one_pow] using
      helmholtzResolventMass_eq_const_mul_normalized 1 z
  constructor
  · intro hz
    have hzn : z ≠ 0 := by
      intro hzero
      subst z
      simpa only [normalizedResolventMass_zero, one_ne_zero] using hz
    refine ⟨hzn, ?_⟩
    have hm : helmholtzResolventMass 1 z = 0 := by rw [he, hz, mul_zero]
    have hid := helmholtzResolventMass_mul_parameter_sq 1 z
    rw [hm, mul_zero, Complex.ofReal_one, one_mul] at hid
    exact (sub_eq_zero.mp hid.symm).symm
  · rintro ⟨hzn, hJ⟩
    have hid := helmholtzResolventMass_mul_parameter_sq 1 z
    rw [Complex.ofReal_one, one_mul, hJ, sub_self, he] at hid
    have hm : (1 / 4 : ℂ) * normalizedResolventMass 1 z = 0 :=
      (mul_eq_zero.mp hid).resolve_left (pow_ne_zero _ hzn)
    exact (mul_eq_zero.mp hm).resolve_left (by norm_num)

theorem onePoints_inter_closedBall_finite (R : ℝ) :
    (onePoints ∩ closedBall (0 : ℂ) R).Finite := by
  have he : onePoints ∩ closedBall (0 : ℂ) R = spectralRootsInClosedBall 1 R := by
    ext z
    simp only [mem_inter_iff, spectralRootsInClosedBall, mem_setOf_eq,
      normalizedResolventMass_one_root_iff, and_comm]
  rw [he]
  exact spectralRootsInClosedBall_finite (by norm_num) R

theorem onePoints_inter_closedBall_ncard_le {R : ℝ} (hR : 0 < R) :
    ((onePoints ∩ closedBall (0 : ℂ) R).ncard : ℝ) ≤ (2 / Real.log 2) * R := by
  have he : onePoints ∩ closedBall (0 : ℂ) R = spectralRootsInClosedBall 1 R := by
    ext z
    simp only [mem_inter_iff, spectralRootsInClosedBall, mem_setOf_eq,
      normalizedResolventMass_one_root_iff, and_comm]
  rw [he]
  simpa only [mul_one] using spectralRootsInClosedBall_ncard_le (by norm_num : 0 < (1 : ℝ)) hR

end J0RadialUniqueness
