import Solutions.J0RadialUniqueness.AbelAveragedKernel
import Solutions.J0RadialUniqueness.AnnularVolterraKernel
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-! Local regularity of the actual Abel average. Smoothness is required only
on an open square containing the relevant angle images; no global smooth
extension of the annular kernel is assumed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

def abelOpenSquare (A B : ℝ) : Set (ℝ × ℝ) := Ioo A B ×ˢ Ioo A B

theorem abelAnglePoint_mem_openSquare {A B t s : ℝ}
    (ht : t ∈ Ioo A B) (hs : s ∈ Ioo A B) (θ : ℝ) :
    abelAnglePoint t s θ ∈ abelOpenSquare A B := by
  have hsin : Real.sin θ ^ 2 ∈ Icc (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  have hh := (convex_Ioo A B).add_smul_sub_mem hs ht hsin
  refine ⟨?_, hs⟩
  simpa only [abelAnglePoint, smul_eq_mul, mul_comm] using hh

theorem abelKernel_continuousOn_openSquare {K : ℝ × ℝ → ℂ} {A B : ℝ}
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p) :
    ContinuousOn K (abelOpenSquare A B) := fun p hp => (hK p hp).continuousAt.continuousWithinAt

theorem abelKernel_fderiv_continuousOn_openSquare {K : ℝ × ℝ → ℂ} {A B : ℝ}
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p) :
    ContinuousOn (fderiv ℝ K) (abelOpenSquare A B) := by
  intro p hp
  have hh : ContDiffAt ℝ ∞ (fderiv ℝ K) p := (hK p hp).fderiv_right (by simp)
  exact hh.continuousAt.continuousWithinAt

theorem abelAveragedKernel_continuousOn_openSquare {K : ℝ × ℝ → ℂ} {A B : ℝ}
    (hK : ContinuousOn K (abelOpenSquare A B)) :
    ContinuousOn (fun p : ℝ × ℝ => abelAveragedKernel K p.1 p.2) (abelOpenSquare A B) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hp : Continuous (fun q : (abelOpenSquare A B) × ℝ =>
      abelAnglePoint q.1.1.1 q.1.1.2 q.2) := by unfold abelAnglePoint; fun_prop
  have hG : Continuous (fun q : (abelOpenSquare A B) × ℝ =>
      K (abelAnglePoint q.1.1.1 q.1.1.2 q.2)) :=
    hK.comp_continuous hp (fun q => abelAnglePoint_mem_openSquare q.1.2.1 q.1.2.2 q.2)
  have hi : Continuous (fun p : abelOpenSquare A B =>
      ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), K (abelAnglePoint p.1.1 p.1.2 θ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (p : abelOpenSquare A B) (θ : ℝ) =>
        K (abelAnglePoint p.1.1 p.1.2 θ)) ?_ 0 (Real.pi / 2)
    convert! hG using 1 <;> rfl
  exact continuous_const.mul hi

theorem abelAveragedKernelSlope_continuousOn_openSquare {K : ℝ × ℝ → ℂ} {A B : ℝ}
    (hdf : ContinuousOn (fderiv ℝ K) (abelOpenSquare A B)) :
    ContinuousOn (fun p : ℝ × ℝ => abelAveragedKernelSlope K p.1 p.2) (abelOpenSquare A B) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hp : Continuous (fun q : (abelOpenSquare A B) × ℝ =>
      abelAnglePoint q.1.1.1 q.1.1.2 q.2) := by unfold abelAnglePoint; fun_prop
  have hd : Continuous (fun q : (abelOpenSquare A B) × ℝ =>
      fderiv ℝ K (abelAnglePoint q.1.1.1 q.1.1.2 q.2)) :=
    hdf.comp_continuous hp (fun q => abelAnglePoint_mem_openSquare q.1.2.1 q.1.2.2 q.2)
  have hH : Continuous (fun q : (abelOpenSquare A B) × ℝ =>
      abelAveragedKernelSlopeIntegrand K q.1.1.1 q.1.1.2 q.2) := by
    unfold abelAveragedKernelSlopeIntegrand
    have ha : Continuous (fun q : (abelOpenSquare A B) × ℝ => ((Real.sin q.2 ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact ha.mul (hd.clm_apply continuous_const)
  have hi : Continuous (fun p : abelOpenSquare A B => ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
      abelAveragedKernelSlopeIntegrand K p.1.1 p.1.2 θ) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (p : abelOpenSquare A B) (θ : ℝ) =>
        abelAveragedKernelSlopeIntegrand K p.1.1 p.1.2 θ) ?_ 0 (Real.pi / 2)
    convert! hH using 1 <;> rfl
  exact continuous_const.mul hi

theorem abelAveragedKernel_integrand_hasDerivAt_of_contDiffAt
    {K : ℝ × ℝ → ℂ} (t s θ : ℝ) (hK : ContDiffAt ℝ ∞ K (abelAnglePoint t s θ)) :
    HasDerivAt (fun u : ℝ => K (abelAnglePoint u s θ))
      (abelAveragedKernelSlopeIntegrand K t s θ) t := by
  have hh := (hK.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (abelAnglePoint_hasDerivAt t s θ)
  apply hh.congr_deriv
  have hv : (Real.sin θ ^ 2, (0 : ℝ)) = Real.sin θ ^ 2 • abelParameterAxis := by
    apply Prod.ext <;> simp [abelParameterAxis]
  simp only [abelAveragedKernelSlopeIntegrand]
  rw [hv, map_smul, Complex.real_smul]

set_option maxHeartbeats 1000000 in
/-- Differentiation under the finite angle integral with only local smoothness
on the open square. Compactness supplies the actual derivative majorant. -/
theorem abelAveragedKernel_hasDerivAt_local {K : ℝ × ℝ → ℂ} {A B t s : ℝ}
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p)
    (ht : t ∈ Ioo A B) (hs : s ∈ Ioo A B) :
    HasDerivAt (fun u : ℝ => abelAveragedKernel K u s) (abelAveragedKernelSlope K t s) t := by
  let J : Set ℝ := Icc ((A + t) / 2) ((t + B) / 2)
  have hJ : J ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  have hJsub (u : ℝ) (hu : u ∈ J) : u ∈ Ioo A B := by
    change (A + t) / 2 ≤ u ∧ u ≤ (t + B) / 2 at hu
    constructor <;> linarith [hu.1, hu.2, ht.1, ht.2]
  have hKc := abelKernel_continuousOn_openSquare hK
  have hdf := abelKernel_fderiv_continuousOn_openSquare hK
  have hp : Continuous (fun q : ℝ × ℝ => abelAnglePoint q.1 s q.2) := by
    unfold abelAnglePoint; fun_prop
  have hGc (u : ℝ) (hu : u ∈ Ioo A B) : Continuous (fun θ : ℝ => K (abelAnglePoint u s θ)) :=
    hKc.comp_continuous (by unfold abelAnglePoint; fun_prop)
      (fun θ => abelAnglePoint_mem_openSquare hu hs θ)
  have hHc (u : ℝ) (hu : u ∈ Ioo A B) :
      Continuous (fun θ : ℝ => abelAveragedKernelSlopeIntegrand K u s θ) := by
    unfold abelAveragedKernelSlopeIntegrand
    have hd : Continuous (fun θ : ℝ => fderiv ℝ K (abelAnglePoint u s θ)) :=
      hdf.comp_continuous (by unfold abelAnglePoint; fun_prop)
        (fun θ => abelAnglePoint_mem_openSquare hu hs θ)
    have ha : Continuous (fun θ : ℝ => ((Real.sin θ ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact ha.mul (hd.clm_apply continuous_const)
  have hHd : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ K (abelAnglePoint q.1 s q.2))
      (J ×ˢ uIcc (0 : ℝ) (Real.pi / 2)) :=
    hdf.comp hp.continuousOn (fun q hq => abelAnglePoint_mem_openSquare (hJsub q.1 hq.1) hs q.2)
  have hHjoint : ContinuousOn (fun q : ℝ × ℝ => abelAveragedKernelSlopeIntegrand K q.1 s q.2)
      (J ×ˢ uIcc (0 : ℝ) (Real.pi / 2)) := by
    unfold abelAveragedKernelSlopeIntegrand
    have ha : Continuous (fun q : ℝ × ℝ => ((Real.sin q.2 ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact ha.continuousOn.mul (hHd.clm_apply continuous_const.continuousOn)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hHjoint
  have hh := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u θ : ℝ => K (abelAnglePoint u s θ))
    (F' := fun u θ : ℝ => abelAveragedKernelSlopeIntegrand K u s θ)
    (μ := volume) (bound := fun _ : ℝ => C) (s := J) hJ
    (by filter_upwards [hJ] with u hu; exact (hGc u (hJsub u hu)).aestronglyMeasurable)
    ((hGc t ht).intervalIntegrable 0 (Real.pi / 2)) (hHc t ht).aestronglyMeasurable
    (Eventually.of_forall (fun θ hθ u hu => hC (u, θ) ⟨hu, uIoc_subset_uIcc hθ⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun θ _ u hu =>
      abelAveragedKernel_integrand_hasDerivAt_of_contDiffAt u s θ
        (hK _ (abelAnglePoint_mem_openSquare (hJsub u hu) hs θ))))
  exact hh.2.const_mul (2 : ℂ)

theorem abelAveragedKernelSlope_uniform_bound_local {K : ℝ × ℝ → ℂ} {A B a b : ℝ}
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p) (hAa : A < a) (hbB : b < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, a ≤ s → s ≤ t → t ≤ b →
      ‖abelAveragedKernelSlope K t s‖ ≤ C := by
  have hsub : abelClosedTriangle a b ⊆ abelOpenSquare A B := by
    rintro ⟨t, s⟩ ⟨has, hst, htb⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hc := (abelAveragedKernelSlope_continuousOn_openSquare
    (abelKernel_fderiv_continuousOn_openSquare hK)).mono hsub
  obtain ⟨C, hC⟩ := (isCompact_abelClosedTriangle a b).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t s has hst htb
  exact (hC (t, s) ⟨has, hst, htb⟩).trans (le_max_left _ _)

theorem abelAveragedKernel_diag_uniform_lower_bound_local {K : ℝ × ℝ → ℂ} {A B a b : ℝ}
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p) (hAa : A < a) (hbB : b < B)
    (hne : ∀ t ∈ Icc a b, K (t, t) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc a b, c ≤ ‖abelAveragedKernel K t t‖ := by
  have hd : ContinuousOn (fun t : ℝ => ‖abelAveragedKernel K t t‖) (Icc a b) :=
    ((abelAveragedKernel_continuousOn_openSquare (abelKernel_continuousOn_openSquare hK)).comp
      (continuous_id.prodMk continuous_id).continuousOn (fun t ht =>
        ⟨⟨hAa.trans_le ht.1, ht.2.trans_lt hbB⟩, ⟨hAa.trans_le ht.1, ht.2.trans_lt hbB⟩⟩)).norm
  apply isCompact_Icc.exists_forall_le' hd
  intro t ht
  rw [abelAveragedKernel_diag]
  exact norm_pos_iff.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (hne t ht))

/-- The source's actual annular kernel satisfies the local hypothesis on every
admissible open square. This uses its proved local smoothness, not global C∞. -/
theorem annularVolterraKernel_complex_contDiffAt_on_openSquare (m : ℕ) {r A B : ℝ}
    (hr : 0 < r) (hrA : r < A) (hB : B < A + r) :
    ∀ p ∈ abelOpenSquare A B,
      ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (annularVolterraKernel m r q : ℂ)) p := by
  intro p hp
  have hpd : p ∈ annularKernelDomain r := square_subset_annularKernelDomain hr hrA hB
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  convert! Complex.ofRealCLM.contDiff.contDiffAt.comp p
    (annularVolterraKernel_contDiffAt m hr hpd) using 1 <;> rfl

theorem annularAbelAveragedKernel_hasDerivAt (m : ℕ) {r A B a b t s : ℝ}
    (hr : 0 < r) (hrA : r < A) (hB : B < A + r) (hAa : A < a) (hbB : b < B)
    (ht : t ∈ Icc a b) (hs : s ∈ Icc a b) :
    HasDerivAt (fun u : ℝ => abelAveragedKernel (fun q => (annularVolterraKernel m r q : ℂ)) u s)
      (abelAveragedKernelSlope (fun q => (annularVolterraKernel m r q : ℂ)) t s) t :=
  abelAveragedKernel_hasDerivAt_local
    (annularVolterraKernel_complex_contDiffAt_on_openSquare m hr hrA hB)
    ⟨hAa.trans_le ht.1, ht.2.trans_lt hbB⟩ ⟨hAa.trans_le hs.1, hs.2.trans_lt hbB⟩

theorem annularAbelAveragedKernelSlope_uniform_bound (m : ℕ) {r A B a b : ℝ}
    (hr : 0 < r) (hrA : r < A) (hB : B < A + r) (hAa : A < a) (hbB : b < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, a ≤ s → s ≤ t → t ≤ b →
      ‖abelAveragedKernelSlope (fun q => (annularVolterraKernel m r q : ℂ)) t s‖ ≤ C :=
  abelAveragedKernelSlope_uniform_bound_local
    (annularVolterraKernel_complex_contDiffAt_on_openSquare m hr hrA hB) hAa hbB

theorem annularAbelAveragedKernel_diag_uniform_lower_bound (m : ℕ) {r A B a b : ℝ}
    (hr : 0 < r) (hrA : r < A) (hB : B < A + r) (hAa : A < a) (hbB : b < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc a b,
      c ≤ ‖abelAveragedKernel (fun q => (annularVolterraKernel m r q : ℂ)) t t‖ := by
  apply abelAveragedKernel_diag_uniform_lower_bound_local
    (annularVolterraKernel_complex_contDiffAt_on_openSquare m hr hrA hB) hAa hbB
  intro t ht
  exact Complex.ofReal_ne_zero.mpr
    (annularVolterraKernel_diagonal_pos m hr (hrA.trans (hAa.trans_le ht.1))).ne'

end J0RadialUniqueness
