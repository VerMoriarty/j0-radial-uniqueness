import Solutions.J0RadialUniqueness.AbelSecondTransform
import Solutions.J0RadialUniqueness.AbelAveragedKernelLocal
import Solutions.J0RadialUniqueness.VolterraNormUniqueness
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

/-! Injectivity of the actual first Abel transform with a smooth, nonvanishing
diagonal kernel. The singular second transform is the proved Fubini identity;
the resulting regular Volterra equation is differentiated and estimated.

The interval must have positive length. For a = b every integral is zero even
for K = 1 and v = 1, so an injectivity assertion on the singleton would be false.
Local smoothness of K is sufficient: an actual smooth cutoff, supported strictly
inside the open square, supplies the global kernel used in the proof. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

set_option maxHeartbeats 1000000 in
/-- The usual moving-endpoint rule follows from the two actual partial
derivatives. No differentiability of the second variable of G is required. -/
theorem hasDerivAt_volterraIntegral_of_joint_continuous
    {G H : ℝ → ℝ → ℂ}
    (hG : Continuous (Function.uncurry G)) (hH : Continuous (Function.uncurry H))
    (hd : ∀ t s : ℝ, HasDerivAt (fun u : ℝ => G u s) (H t s) t)
    (a t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s : ℝ in a..u, G u s)
      ((∫ s : ℝ in a..t, H t s) + G t t) t := by
  let F : ℝ → ℝ → ℂ := fun u z => ∫ s : ℝ in a..z, G u s
  let D₁ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun u z =>
    ContinuousLinearMap.toSpanSingleton ℝ (∫ s : ℝ in a..z, H u s)
  let D₂ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun u z =>
    ContinuousLinearMap.toSpanSingleton ℝ (G u z)
  have h₁ (u z : ℝ) : HasFDerivAt (fun q : ℝ => F q z) (D₁ u z) u :=
    (hasDerivAt_intervalIntegral_of_joint_continuous hG hH hd a z u).hasFDerivAt
  have h₂ (u z : ℝ) : HasFDerivAt (F u) (D₂ u z) z := by
    have hc : Continuous (G u) := hG.comp (continuous_const.prodMk continuous_id)
    exact (hc.integral_hasStrictDerivAt a z).hasDerivAt.hasFDerivAt
  have hc₁ : Continuous (Function.uncurry D₁) := by
    have hi : Continuous (fun p : ℝ × ℝ => ∫ s : ℝ in a..p.2, H p.1 s) :=
      intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume) hH
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp hi
  have hc₂ : Continuous (Function.uncurry D₂) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp hG
  have hh := hasStrictFDerivAt_uncurry_coprod
    (f := F) (f₁ := D₁) (f₂ := D₂) (u := (t, t))
    (Eventually.of_forall (fun p => h₁ p.1 p.2))
    (Eventually.of_forall (fun p => h₂ p.1 p.2)) hc₁.continuousAt hc₂.continuousAt
  have hdiag : HasDerivAt (fun u : ℝ => (u, u)) (1, 1) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_id t)
  have hres := HasFDerivAt.comp_hasDerivAt
    (f := fun u : ℝ => (u, u)) (l := Function.uncurry F) t hh.hasFDerivAt hdiag
  convert! hres using 1 <;>
    simp only [F, D₁, D₂, Function.uncurry, Function.comp_def,
      ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change _ = (ContinuousLinearMap.toSpanSingleton ℝ (∫ s in a..t, H t s)) 1 +
    (ContinuousLinearMap.toSpanSingleton ℝ (G t t)) 1
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- The second Abel transform of a zero first transform is the genuine zero
regular Volterra transform, including the initial endpoint. -/
theorem abelAveragedKernel_volterraIntegral_eq_zero {K : ℝ × ℝ → ℂ}
    (hK : Continuous K) {v : ℝ → ℂ} (hv : Continuous v) {a b : ℝ}
    (hzero : ∀ t ∈ Icc a b,
      (∫ s : ℝ in a..t, (Real.sqrt (t - s))⁻¹ • (K (t, s) * v s)) = 0) :
    ∀ t ∈ Icc a b, (∫ s : ℝ in a..t, abelAveragedKernel K t s * v s) = 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hta | hat
  · subst t
    exact intervalIntegral.integral_same
  · rw [← abelSecondTransform_intervalIntegral hK hv hat]
    calc
      _ = ∫ p : ℝ in a..t, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro p hp
        rw [uIcc_of_le hat.le] at hp
        dsimp only
        rw [hzero p ⟨hp.1, hp.2.trans ht.2⟩, smul_zero]
      _ = 0 := by simp

set_option maxHeartbeats 1000000 in
/-- The regular Volterra step, stated for abstract actual kernels so the
estimates do not repeatedly unfold the angular integrals. -/
theorem volterraIntegral_injective_of_joint_continuous {G H : ℝ → ℝ → ℂ}
    (hGc : Continuous (Function.uncurry G)) (hHc : Continuous (Function.uncurry H))
    (hder : ∀ t s : ℝ, HasDerivAt (fun u : ℝ => G u s) (H t s) t)
    {v : ℝ → ℂ} (hv : Continuous v) {a b : ℝ} (hab : a < b)
    {M c : ℝ} (hM0 : 0 ≤ M) (hc : 0 < c)
    (hM : ∀ t s : ℝ, a ≤ s → s ≤ t → t ≤ b → ‖H t s‖ ≤ M)
    (hcdiag : ∀ t ∈ Icc a b, c ≤ ‖G t t‖)
    (hVzero : ∀ t ∈ Icc a b, (∫ s : ℝ in a..t, G t s * v s) = 0) :
    ∀ t ∈ Icc a b, v t = 0 := by
  have hG : Continuous (Function.uncurry (fun t s : ℝ => G t s * v s)) :=
    hGc.mul (hv.comp continuous_snd)
  have hH : Continuous (Function.uncurry (fun t s : ℝ => H t s * v s)) :=
    hHc.mul (hv.comp continuous_snd)
  have hd (t s : ℝ) : HasDerivAt (fun u : ℝ => G u s * v s) (H t s * v s) t :=
    (hder t s).mul_const (v s)
  have heq (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ s : ℝ in a..t, H t s * v s) + G t t * v t = 0 := by
    have hfull : HasDerivAt (fun u : ℝ => ∫ s : ℝ in a..u, G u s * v s)
        ((∫ s : ℝ in a..t, H t s * v s) + G t t * v t) t :=
      hasDerivAt_volterraIntegral_of_joint_continuous
        (G := fun u s : ℝ => G u s * v s) (H := fun u s : ℝ => H u s * v s) hG hH hd a t
    have hh := hfull.hasDerivWithinAt (s := Icc a b)
    have hz : HasDerivWithinAt (fun u : ℝ => ∫ s : ℝ in a..u, G u s * v s)
        (0 : ℂ) (Icc a b) t :=
      (hasDerivWithinAt_const t (Icc a b) (0 : ℂ)).congr_of_mem hVzero ht
    exact UniqueDiffWithinAt.eq_deriv (Icc a b) (uniqueDiffOn_Icc hab t ht) hh hz
  apply continuous_zero_of_norm_le_volterra_integral (C := M / c) hv (div_nonneg hM0 hc.le)
  intro t ht
  have hHct : Continuous (fun s : ℝ => H t s * v s) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hbnd : ‖∫ s : ℝ in a..t, H t s * v s‖ ≤
      M * ∫ s : ℝ in a..t, ‖v s‖ := by
    calc
      _ ≤ ∫ s : ℝ in a..t, ‖H t s * v s‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s : ℝ in a..t, M * ‖v s‖ := by
        apply intervalIntegral.integral_mono_on ht.1
          (hHct.norm.intervalIntegrable a t) ((hv.norm.const_mul M).intervalIntegrable a t)
        intro s hs
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM t s hs.1 hs.2 ht.2) (norm_nonneg _)
      _ = _ := intervalIntegral.integral_const_mul M _
  have hprod : c * ‖v t‖ ≤ M * ∫ s : ℝ in a..t, ‖v s‖ := by
    calc
      _ ≤ ‖G t t‖ * ‖v t‖ :=
        mul_le_mul_of_nonneg_right (hcdiag t ht) (norm_nonneg _)
      _ = ‖G t t * v t‖ := (norm_mul _ _).symm
      _ = ‖-(∫ s : ℝ in a..t, H t s * v s)‖ := by
        congr 1
        exact eq_neg_of_add_eq_zero_right (heq t ht)
      _ = ‖∫ s : ℝ in a..t, H t s * v s‖ := norm_neg _
      _ ≤ _ := hbnd
  calc
    ‖v t‖ ≤ (M * ∫ s : ℝ in a..t, ‖v s‖) / c :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hprod)
    _ = (M / c) * ∫ s : ℝ in a..t, ‖v s‖ := by ring

/-- Smooth-kernel injectivity on a positive-length compact interval. -/
theorem abelVolterraInjectivity_global {K : ℝ × ℝ → ℂ}
    (hK : ContDiff ℝ ∞ K) {v : ℝ → ℂ} (hv : Continuous v) {a b : ℝ}
    (hab : a < b) (hne : ∀ t ∈ Icc a b, K (t, t) ≠ 0)
    (hzero : ∀ t ∈ Icc a b,
      (∫ s : ℝ in a..t, (Real.sqrt (t - s))⁻¹ • (K (t, s) * v s)) = 0) :
    ∀ t ∈ Icc a b, v t = 0 := by
  obtain ⟨M, hM0, hM⟩ := abelAveragedKernelSlope_uniform_bound hK a b
  obtain ⟨c, hc, hcdiag⟩ := abelAveragedKernel_diag_uniform_lower_bound hK.continuous a b hne
  exact volterraIntegral_injective_of_joint_continuous
    (G := abelAveragedKernel K) (H := abelAveragedKernelSlope K)
    (continuous_abelAveragedKernel hK.continuous) (continuous_abelAveragedKernelSlope hK)
    (abelAveragedKernel_hasDerivAt hK) hv hab hM0 hc hM hcdiag
    (abelAveragedKernel_volterraIntegral_eq_zero hK.continuous hv hzero)

set_option maxHeartbeats 1000000 in
/-- A genuine smooth extension on the compact square. Multiplication by two
one-dimensional smooth cutoffs makes the function identically zero on a
neighborhood of every point outside the open square. -/
theorem exists_abelKernel_global_smooth_extension {K : ℝ × ℝ → ℂ} {A B a b : ℝ}
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p)
    (hAa : A < a) (hab : a ≤ b) (hbB : b < B) :
    ∃ L : ℝ × ℝ → ℂ, ContDiff ℝ ∞ L ∧ EqOn L K (Icc a b ×ˢ Icc a b) := by
  let c : ℝ := (a + b) / 2
  let d : ℝ := min (a - A) (B - b)
  let h : ℝ := (b - a) / 2
  have hd : 0 < d := lt_min (sub_pos.mpr hAa) (sub_pos.mpr hbB)
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hdA : d ≤ a - A := min_le_left _ _
  have hdB : d ≤ B - b := min_le_right _ _
  let χ : ContDiffBump c :=
    { rIn := h + d / 3, rOut := h + 2 * d / 3,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hleft : A < c - χ.rOut := by dsimp [c, χ, h]; linarith
  have hright : c + χ.rOut < B := by dsimp [c, χ, h]; linarith
  have hχpos : 0 < χ.rOut := χ.rOut_pos
  have hcA : A < c := by linarith
  have hcB : c < B := by linarith
  have hone (x : ℝ) (hx : x ∈ Icc a b) : χ x = 1 := by
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> dsimp [χ, c, h] <;> linarith [hx.1, hx.2]
  have hzero (x : ℝ) (hx : x ∉ Ioo A B) : χ =ᶠ[𝓝 x] (fun _ => 0) := by
    have hxouter : χ.rOut < dist x c := by
      rw [Real.dist_eq]
      by_cases hAx : A < x
      · have hBx : B ≤ x := le_of_not_gt (fun h => hx ⟨hAx, h⟩)
        rw [abs_of_nonneg (by linarith [hcB] : 0 ≤ x - c)]
        linarith
      · have hxA : x ≤ A := le_of_not_gt hAx
        rw [abs_of_nonpos (by linarith [hcA] : x - c ≤ 0)]
        linarith
    have hn : {y : ℝ | χ.rOut < dist y c} ∈ 𝓝 x :=
      (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hxouter
    filter_upwards [hn] with y hy
    exact χ.zero_of_le_dist hy.le
  let L : ℝ × ℝ → ℂ := fun p => (χ p.1 * χ p.2) • K p
  have hLs : ContDiff ℝ ∞ L := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ abelOpenSquare A B
    · exact (((χ.contDiff.comp contDiff_fst).mul
        (χ.contDiff.comp contDiff_snd)).contDiffAt).smul (hK p hp)
    · have hLzero : L =ᶠ[𝓝 p] (fun _ => 0) := by
        by_cases hp₁ : p.1 ∈ Ioo A B
        · have hp₂ : p.2 ∉ Ioo A B := fun h => hp ⟨hp₁, h⟩
          filter_upwards [(continuous_snd.tendsto p).eventually (hzero p.2 hp₂)] with q hq
          simp only [L, hq, mul_zero, zero_smul]
        · filter_upwards [(continuous_fst.tendsto p).eventually (hzero p.1 hp₁)] with q hq
          simp only [L, hq, zero_mul, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hLzero
  refine ⟨L, hLs, ?_⟩
  intro p hp
  dsimp only [L]
  rw [hone p.1 hp.1, hone p.2 hp.2, one_mul, one_smul]

/-- Injectivity for the actual kernel with only local C∞ regularity. The
extension is proved above and agrees on every point used by the Abel integrals. -/
theorem abelVolterraInjectivity_local {K : ℝ × ℝ → ℂ} {v : ℝ → ℂ} (hv : Continuous v)
    {A B a b : ℝ} (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p)
    (hne : ∀ t ∈ Icc a b, K (t, t) ≠ 0)
    (hzero : ∀ t ∈ Icc a b,
      (∫ s : ℝ in a..t, (Real.sqrt (t - s))⁻¹ • (K (t, s) * v s)) = 0) :
    ∀ t ∈ Icc a b, v t = 0 := by
  obtain ⟨L, hL, hLK⟩ := exists_abelKernel_global_smooth_extension hK hAa hab.le hbB
  apply abelVolterraInjectivity_global hL hv hab
  · intro t ht
    rw [hLK ⟨ht, ht⟩]
    exact hne t ht
  · intro t ht
    calc
      _ = ∫ s : ℝ in a..t, (Real.sqrt (t - s))⁻¹ • (K (t, s) * v s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht.1] at hs
        dsimp only
        rw [hLK ⟨ht, ⟨hs.1, hs.2.trans ht.2⟩⟩]
      _ = 0 := hzero t ht

theorem abelVolterraInjectivity_local_div {K : ℝ × ℝ → ℂ} {v : ℝ → ℂ} (hv : Continuous v)
    {A B a b : ℝ} (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hK : ∀ p ∈ abelOpenSquare A B, ContDiffAt ℝ ∞ K p)
    (hne : ∀ t ∈ Icc a b, K (t, t) ≠ 0)
    (hzero : ∀ t ∈ Icc a b,
      (∫ s : ℝ in a..t, K (t, s) * v s / (Real.sqrt (t - s) : ℂ)) = 0) :
    ∀ t ∈ Icc a b, v t = 0 := by
  apply abelVolterraInjectivity_local hv hAa hab hbB hK hne
  intro t ht
  convert! hzero t ht using 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

end J0RadialUniqueness
