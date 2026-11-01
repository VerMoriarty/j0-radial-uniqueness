import Solutions.J0RadialUniqueness.CircleLaplacian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Actual angularly averaged Abel kernels. This module proves regularity,
the parameter derivative, diagonal values and compact uniform bounds. No
second-Abel/Fubini identity or Volterra inversion is assumed or asserted. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

def abelAnglePoint (t s θ : ℝ) : ℝ × ℝ :=
  (s + (t - s) * Real.sin θ ^ 2, s)

def abelParameterAxis : ℝ × ℝ := (1, 0)

def abelAveragedKernel (K : ℝ × ℝ → ℂ) (t s : ℝ) : ℂ :=
  (2 : ℂ) * ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), K (abelAnglePoint t s θ)

def abelAveragedKernelSlopeIntegrand (K : ℝ × ℝ → ℂ) (t s θ : ℝ) : ℂ :=
  ((Real.sin θ ^ 2 : ℝ) : ℂ) * fderiv ℝ K (abelAnglePoint t s θ) abelParameterAxis

def abelAveragedKernelSlope (K : ℝ × ℝ → ℂ) (t s : ℝ) : ℂ :=
  (2 : ℂ) * ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), abelAveragedKernelSlopeIntegrand K t s θ

theorem continuous_abelAnglePoint_joint :
    Continuous (fun q : (ℝ × ℝ) × ℝ => abelAnglePoint q.1.1 q.1.2 q.2) := by
  unfold abelAnglePoint
  fun_prop

theorem continuous_abelAveragedKernel {K : ℝ × ℝ → ℂ} (hK : Continuous K) :
    Continuous (fun p : ℝ × ℝ => abelAveragedKernel K p.1 p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ =>
      ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), K (abelAnglePoint p.1 p.2 θ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (p : ℝ × ℝ) (θ : ℝ) => K (abelAnglePoint p.1 p.2 θ)) ?_ 0 (Real.pi / 2)
    convert! hK.comp continuous_abelAnglePoint_joint using 1 <;> rfl
  exact continuous_const.mul hi

theorem continuous_abelAveragedKernelSlopeIntegrand_joint {K : ℝ × ℝ → ℂ}
    (hK : ContDiff ℝ ∞ K) :
    Continuous (fun q : (ℝ × ℝ) × ℝ => abelAveragedKernelSlopeIntegrand K q.1.1 q.1.2 q.2) := by
  unfold abelAveragedKernelSlopeIntegrand
  have hdfSmooth : ContDiff ℝ ∞ (fderiv ℝ K) := hK.fderiv_right (by simp)
  have hdf : Continuous (fderiv ℝ K) := hdfSmooth.continuous
  have ha : Continuous (fun q : (ℝ × ℝ) × ℝ => ((Real.sin q.2 ^ 2 : ℝ) : ℂ)) := by fun_prop
  exact ha.mul ((hdf.comp continuous_abelAnglePoint_joint).clm_apply continuous_const)

theorem continuous_abelAveragedKernelSlope {K : ℝ × ℝ → ℂ} (hK : ContDiff ℝ ∞ K) :
    Continuous (fun p : ℝ × ℝ => abelAveragedKernelSlope K p.1 p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ => ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
      abelAveragedKernelSlopeIntegrand K p.1 p.2 θ) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (p : ℝ × ℝ) (θ : ℝ) =>
        abelAveragedKernelSlopeIntegrand K p.1 p.2 θ) ?_ 0 (Real.pi / 2)
    convert! continuous_abelAveragedKernelSlopeIntegrand_joint hK using 1 <;> rfl
  exact continuous_const.mul hi

theorem abelAnglePoint_hasDerivAt (t s θ : ℝ) :
    HasDerivAt (fun u : ℝ => abelAnglePoint u s θ) (Real.sin θ ^ 2, (0 : ℝ)) t := by
  have h₁ : HasDerivAt (fun u : ℝ => s + (u - s) * Real.sin θ ^ 2) (Real.sin θ ^ 2) t := by
    convert! (((hasDerivAt_id t).sub_const s).mul_const (Real.sin θ ^ 2)).const_add s using 1 <;> simp
  exact h₁.prodMk (hasDerivAt_const t s)

theorem abelAveragedKernel_integrand_hasDerivAt {K : ℝ × ℝ → ℂ}
    (hK : ContDiff ℝ ∞ K) (t s θ : ℝ) :
    HasDerivAt (fun u : ℝ => K (abelAnglePoint u s θ))
      (abelAveragedKernelSlopeIntegrand K t s θ) t := by
  unfold abelAveragedKernelSlopeIntegrand
  have hh := ((hK.differentiable (by simp)).differentiableAt
    (x := abelAnglePoint t s θ)).hasFDerivAt.comp_hasDerivAt t (abelAnglePoint_hasDerivAt t s θ)
  apply hh.congr_deriv
  have hv : (Real.sin θ ^ 2, (0 : ℝ)) = Real.sin θ ^ 2 • abelParameterAxis := by
    apply Prod.ext <;> simp [abelParameterAxis]
  rw [hv, map_smul, Complex.real_smul]

set_option maxHeartbeats 1000000 in
/-- The actual first-real-parameter derivative is obtained by a dominated
parameter integral on a compact angle interval. -/
theorem abelAveragedKernel_hasDerivAt {K : ℝ × ℝ → ℂ}
    (hK : ContDiff ℝ ∞ K) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => abelAveragedKernel K u s) (abelAveragedKernelSlope K t s) t := by
  have hp : Continuous (fun q : ℝ × ℝ => abelAnglePoint q.1 s q.2) := by
    unfold abelAnglePoint
    fun_prop
  have hG : Continuous (Function.uncurry (fun u θ : ℝ => K (abelAnglePoint u s θ))) :=
    hK.continuous.comp hp
  have hH : Continuous (Function.uncurry (fun u θ : ℝ => abelAveragedKernelSlopeIntegrand K u s θ)) := by
    have hdfSmooth : ContDiff ℝ ∞ (fderiv ℝ K) := hK.fderiv_right (by simp)
    have ha : Continuous (fun q : ℝ × ℝ => ((Real.sin q.2 ^ 2 : ℝ) : ℂ)) := by fun_prop
    unfold Function.uncurry abelAveragedKernelSlopeIntegrand
    exact ha.mul ((hdfSmooth.continuous.comp hp).clm_apply continuous_const)
  have hh := hasDerivAt_intervalIntegral_of_joint_continuous hG hH
    (fun u θ => abelAveragedKernel_integrand_hasDerivAt hK u s θ) 0 (Real.pi / 2) t
  exact hh.const_mul (2 : ℂ)

theorem abelAveragedKernel_deriv {K : ℝ × ℝ → ℂ} (hK : ContDiff ℝ ∞ K) (t s : ℝ) :
    deriv (fun u : ℝ => abelAveragedKernel K u s) t = abelAveragedKernelSlope K t s :=
  (abelAveragedKernel_hasDerivAt hK t s).deriv

theorem abelAveragedKernel_diag (K : ℝ × ℝ → ℂ) (t : ℝ) :
    abelAveragedKernel K t t = (Real.pi : ℂ) * K (t, t) := by
  simp only [abelAveragedKernel, abelAnglePoint, sub_self, zero_mul, add_zero]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

def abelClosedTriangle (a b : ℝ) : Set (ℝ × ℝ) := {p | a ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ b}

theorem isCompact_abelClosedTriangle (a b : ℝ) : IsCompact (abelClosedTriangle a b) := by
  have hc : IsClosed (abelClosedTriangle a b) :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter (isClosed_le continuous_fst continuous_const))
  apply (isCompact_Icc.prod (isCompact_Icc : IsCompact (Icc a b))).of_isClosed_subset hc
  rintro ⟨t, s⟩ ⟨has, hst, htb⟩
  exact ⟨⟨has.trans hst, htb⟩, ⟨has, hst.trans htb⟩⟩

theorem abelAveragedKernelSlope_uniform_bound {K : ℝ × ℝ → ℂ}
    (hK : ContDiff ℝ ∞ K) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, a ≤ s → s ≤ t → t ≤ b →
      ‖abelAveragedKernelSlope K t s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_abelClosedTriangle a b).exists_bound_of_continuousOn
    (continuous_abelAveragedKernelSlope hK).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t s has hst htb
  exact (hC (t, s) ⟨has, hst, htb⟩).trans (le_max_left _ _)

theorem abelAveragedKernel_diag_uniform_lower_bound {K : ℝ × ℝ → ℂ}
    (hK : Continuous K) (a b : ℝ) (hne : ∀ t ∈ Icc a b, K (t, t) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc a b, c ≤ ‖abelAveragedKernel K t t‖ := by
  have hc : Continuous (fun t : ℝ => ‖abelAveragedKernel K t t‖) :=
    ((continuous_abelAveragedKernel hK).comp (continuous_id.prodMk continuous_id)).norm
  apply isCompact_Icc.exists_forall_le' hc.continuousOn
  intro t ht
  apply norm_pos_iff.mpr
  rw [abelAveragedKernel_diag]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (hne t ht)

end J0RadialUniqueness
