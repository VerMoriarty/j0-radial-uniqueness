import Solutions.J0RadialUniqueness.MollifiedWeakHarmonic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

/-!
Smoothness and Laplacian commutation for an actual compact L1 complex kernel.
The kernel is never assumed smooth. Near each center only the smooth right
factor is cut off, so the compact-smooth convolution theorem applies locally.
-/

noncomputable section

open MeasureTheory Laplacian Filter Set
open scoped Topology ContDiff Convolution

namespace J0RadialUniqueness

def complexMulPair : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

def complexConvolution (k u : Plane → ℂ) : Plane → ℂ := k ⋆[complexMulPair, volume] u

theorem complexConvolution_eq_integral (k u : Plane → ℂ) (x : Plane) :
    complexConvolution k u x = ∫ y : Plane, k y * u (x - y) := rfl

theorem complexConvolution_integrable {k u : Plane → ℂ}
    (hk : Integrable k) (hc : HasCompactSupport k) (hu : Continuous u) (x : Plane) :
    Integrable (fun y : Plane => k y * u (x - y)) :=
  hc.convolutionExists_left_of_continuous_right complexMulPair hk.locallyIntegrable hu x

theorem complexConvolution_contDiff_of_compact_right {k u : Plane → ℂ}
    (hk : LocallyIntegrable k) (hc : HasCompactSupport u) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (complexConvolution k u) :=
  hc.contDiff_convolution_right complexMulPair hk hu

theorem directionalKernel_complexConvolution_of_compact_right {k u : Plane → ℂ}
    (hk : LocallyIntegrable k) (hc : HasCompactSupport u) (hu : ContDiff ℝ ∞ u)
    (v x : Plane) :
    directionalKernel (complexConvolution k u) v x = complexConvolution k (directionalKernel u v) x := by
  have hu₁ : ContDiff ℝ 1 u := hu.of_le (by simp)
  have hh := hc.hasFDerivAt_convolution_right complexMulPair hk hu₁ x
  change fderiv ℝ (k ⋆[complexMulPair, volume] u) x v = _
  rw [hh.fderiv]
  exact convolution_precompR_apply complexMulPair hk (hc.fderiv ℝ)
    (hu₁.continuous_fderiv one_ne_zero) x v

theorem directionalSecond_complexConvolution_of_compact_right {k u : Plane → ℂ}
    (hk : LocallyIntegrable k) (hc : HasCompactSupport u) (hu : ContDiff ℝ ∞ u)
    (v w x : Plane) :
    directionalSecond (complexConvolution k u) v w x = complexConvolution k (directionalSecond u v w) x := by
  have he : directionalKernel (complexConvolution k u) v =
      complexConvolution k (directionalKernel u v) := by
    funext y
    exact directionalKernel_complexConvolution_of_compact_right hk hc hu v y
  unfold directionalSecond
  rw [he]
  exact directionalKernel_complexConvolution_of_compact_right hk
    (directionalKernel_hasCompactSupport hc v) (directionalKernel_contDiff hu v) w x

theorem complexConvolution_sum_of_compact_right {ι : Type*} [Fintype ι] {k : Plane → ℂ}
    (hk : LocallyIntegrable k) (g : ι → Plane → ℂ)
    (hc : ∀ i, HasCompactSupport (g i)) (hg : ∀ i, Continuous (g i)) (x : Plane) :
    complexConvolution k (fun y => ∑ i, g i y) x = ∑ i, complexConvolution k (g i) x := by
  simp only [complexConvolution_eq_integral, Finset.mul_sum]
  convert! integral_finsetSum Finset.univ
    (fun i _ => (hc i).convolutionExists_right complexMulPair hk (hg i) x) using 1 <;> rfl

theorem laplacian_complexConvolution_of_compact_right {k u : Plane → ℂ}
    (hk : LocallyIntegrable k) (hc : HasCompactSupport u) (hu : ContDiff ℝ ∞ u) (x : Plane) :
    laplacian (complexConvolution k u) x = complexConvolution k (laplacian u) x := by
  let e := stdOrthonormalBasis ℝ Plane
  let g : Fin (Module.finrank ℝ Plane) → Plane → ℂ :=
    fun i => directionalSecond u (e i) (e i)
  have hgc : ∀ i, HasCompactSupport (g i) := fun i =>
    directionalSecond_hasCompactSupport hc (e i) (e i)
  have hgs : ∀ i, ContDiff ℝ ∞ (g i) := fun i => directionalSecond_contDiff hu (e i) (e i)
  have hsum : (fun y => ∑ i, g i y) = laplacian u := by
    funext y
    exact (laplacian_eq_sum_directionalSecond hu y).symm
  calc
    _ = ∑ i, directionalSecond (complexConvolution k u) (e i) (e i) x :=
      laplacian_eq_sum_directionalSecond (complexConvolution_contDiff_of_compact_right hk hc hu) x
    _ = ∑ i, complexConvolution k (g i) x := by
      apply Finset.sum_congr rfl
      intro i _
      exact directionalSecond_complexConvolution_of_compact_right hk hc hu (e i) (e i) x
    _ = complexConvolution k (fun y => ∑ i, g i y) x :=
      (complexConvolution_sum_of_compact_right hk g hgc (fun i => (hgs i).continuous) x).symm
    _ = _ := by rw [hsum]

/-- A local compact cutoff of the smooth right factor. The convolution agrees
on a neighborhood of x, and the cutoff agrees as a germ at every relevant x−y.
No regularity assumption on the compact left kernel enters this construction. -/
theorem exists_complexConvolution_local_cutoff {k u : Plane → ℂ}
    (hc : HasCompactSupport k) (hu : ContDiff ℝ ∞ u) (x₀ : Plane) :
    ∃ v : Plane → ℂ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      complexConvolution k u =ᶠ[𝓝 x₀] complexConvolution k v ∧
      ∀ y : Plane, k y ≠ 0 → v =ᶠ[𝓝 (x₀ - y)] u := by
  obtain ⟨S, hSpos, hS⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
  have hknorm (y : Plane) (hy : k y ≠ 0) : ‖y‖ < S := by
    simpa only [Metric.mem_ball, dist_zero_right] using hS (subset_closure hy)
  let R : ℝ := ‖x₀‖ + S + 2
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0 : Plane) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let v : Plane → ℂ := fun z => χ z • u z
  have hvs : ContDiff ℝ ∞ v := χ.contDiff.smul hu
  have hvc : HasCompactSupport v := χ.hasCompactSupport.smul_right
  have heq (z : Plane) (hz : z ∈ Metric.ball (0 : Plane) R) : v z = u z := by
    change χ z • u z = u z
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul]
  refine ⟨v, hvs, hvc, ?_, ?_⟩
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    simp only [complexConvolution_eq_integral]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      by_cases hy : k y = 0
      · simp only [hy, zero_mul]
      · have hxy : x - y ∈ Metric.ball (0 : Plane) R := by
          have hxnorm : ‖x - x₀‖ < 1 := by
            simpa only [Metric.mem_ball, dist_eq_norm] using hx
          have hynorm := hknorm y hy
          rw [Metric.mem_ball, dist_zero_right]
          calc
            ‖x - y‖ = ‖(x - x₀) + (x₀ - y)‖ := by congr 1; abel
            _ ≤ ‖x - x₀‖ + ‖x₀ - y‖ := norm_add_le _ _
            _ ≤ ‖x - x₀‖ + (‖x₀‖ + ‖y‖) := add_le_add (le_refl _) (norm_sub_le _ _)
            _ < R := by dsimp [R]; linarith
        dsimp only
        rw [heq (x - y) hxy])
  · intro y hy
    have hyball : x₀ - y ∈ Metric.ball (0 : Plane) R := by
      have hynorm := hknorm y hy
      rw [Metric.mem_ball, dist_zero_right]
      calc
        ‖x₀ - y‖ ≤ ‖x₀‖ + ‖y‖ := norm_sub_le _ _
        _ < R := by dsimp [R]; linarith
    filter_upwards [Metric.isOpen_ball.mem_nhds hyball] with z hz
    exact heq z hz

/-- A compact L1 kernel smooths every globally smooth complex function. The
proof localizes only the right factor, which need not have compact support. -/
theorem complexConvolution_contDiff {k u : Plane → ℂ}
    (hk : Integrable k) (hc : HasCompactSupport k) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (complexConvolution k u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨v, hvs, hvc, heq, _⟩ := exists_complexConvolution_local_cutoff hc hu x
  exact (complexConvolution_contDiff_of_compact_right hk.locallyIntegrable hvc hvs).contDiffAt.congr_of_eventuallyEq heq

/-- The actual plane Laplacian passes through a compact L1 complex convolution,
with no smoothness hypothesis on the kernel. -/
theorem laplacian_complexConvolution {k u : Plane → ℂ}
    (hk : Integrable k) (hc : HasCompactSupport k) (hu : ContDiff ℝ ∞ u) (x : Plane) :
    laplacian (complexConvolution k u) x = complexConvolution k (laplacian u) x := by
  obtain ⟨v, hvs, hvc, heq, hshift⟩ := exists_complexConvolution_local_cutoff hc hu x
  calc
    _ = laplacian (complexConvolution k v) x := (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
    _ = complexConvolution k (laplacian v) x :=
      laplacian_complexConvolution_of_compact_right hk.locallyIntegrable hvc hvs x
    _ = _ := by
      simp only [complexConvolution_eq_integral]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        by_cases hy : k y = 0
        · simp only [hy, zero_mul]
        · dsimp only
          rw [(InnerProductSpace.laplacian_congr_nhds (hshift y hy)).eq_of_nhds])

end J0RadialUniqueness
