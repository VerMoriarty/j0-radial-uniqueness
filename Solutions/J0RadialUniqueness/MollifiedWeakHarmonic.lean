import Definitions.J0RadialUniqueness.TwoRadius
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Convolution of a globally locally integrable weakly harmonic function with a
smooth compactly supported real kernel.  The convolution and its derivatives are
the actual Bochner integrals in Mathlib.  No regularity theorem for weakly
harmonic functions is assumed here. -/

noncomputable section

open MeasureTheory Laplacian
open scoped ContDiff Convolution

namespace J0RadialUniqueness

/-- Real scalar multiplication, with the complex variable in the first slot. -/
def realKernelPair : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

/-- The convolution with a real smoothing kernel, with respect to plane volume. -/
def mollified (f : Plane → ℂ) (φ : Plane → ℝ) : Plane → ℂ :=
  f ⋆[realKernelPair, volume] φ

theorem mollified_eq_integral (f : Plane → ℂ) (φ : Plane → ℝ) (x : Plane) :
    mollified f φ x = ∫ y : Plane, φ (x - y) • f y := by
  rfl

theorem mollified_integrable {f : Plane → ℂ} {φ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hc : HasCompactSupport φ) (hφ : Continuous φ)
    (x : Plane) : Integrable (fun y : Plane => φ (x - y) • f y) := by
  exact hc.convolutionExists_right realKernelPair hf hφ x

theorem mollified_contDiff {f : Plane → ℂ} {φ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hc : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (mollified f φ) := by
  exact hc.contDiff_convolution_right realKernelPair hf hφ

section DirectionalDerivatives

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed directional derivative, expressed using the real Fréchet derivative. -/
def directionalKernel (g : Plane → V) (v : Plane) : Plane → V :=
  fun x => fderiv ℝ g x v

/-- Two directional derivatives, in the indicated order. -/
def directionalSecond (g : Plane → V) (v w : Plane) : Plane → V :=
  directionalKernel (directionalKernel g v) w

theorem directionalKernel_contDiff {g : Plane → V} (hg : ContDiff ℝ ∞ g)
    (v : Plane) : ContDiff ℝ ∞ (directionalKernel g v) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  exact hd.clm_apply contDiff_const

theorem directionalKernel_hasCompactSupport {g : Plane → V}
    (hc : HasCompactSupport g) (v : Plane) :
    HasCompactSupport (directionalKernel g v) := by
  exact hc.fderiv_apply ℝ v

theorem directionalSecond_contDiff {g : Plane → V} (hg : ContDiff ℝ ∞ g)
    (v w : Plane) : ContDiff ℝ ∞ (directionalSecond g v w) := by
  exact directionalKernel_contDiff (directionalKernel_contDiff hg v) w

theorem directionalSecond_hasCompactSupport {g : Plane → V}
    (hc : HasCompactSupport g) (v w : Plane) :
    HasCompactSupport (directionalSecond g v w) := by
  exact directionalKernel_hasCompactSupport (directionalKernel_hasCompactSupport hc v) w

theorem directionalSecond_eq_fderiv {g : Plane → V} (hg : ContDiff ℝ ∞ g)
    (v w x : Plane) :
    directionalSecond g v w x = fderiv ℝ (fderiv ℝ g) x w v := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have h := fderiv_clm_apply ((hd.differentiable (by simp)).differentiableAt (x := x))
    (differentiableAt_const (c := v) (x := x))
  change fderiv ℝ (fun y => fderiv ℝ g y v) x w = _
  rw [h]
  simp

/-- The standard basis formula, in a form suited to differentiating convolutions. -/
theorem laplacian_eq_sum_directionalSecond {g : Plane → V}
    (hg : ContDiff ℝ ∞ g) (x : Plane) :
    laplacian g x =
      ∑ i : Fin (Module.finrank ℝ Plane),
        directionalSecond g ((stdOrthonormalBasis ℝ Plane) i)
          ((stdOrthonormalBasis ℝ Plane) i) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_two_apply, directionalSecond_eq_fderiv hg]
  simp

/-- First derivatives of a translated reflection have one minus sign. -/
theorem directionalKernel_reflect {g : Plane → V} (hg : ContDiff ℝ ∞ g)
    (a v x : Plane) :
    directionalKernel (fun y => g (a - y)) v x =
      -directionalKernel g v (a - x) := by
  have h := ((hg.differentiable (by simp)).differentiableAt (x := a - x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_sub a)
  simp only [Function.comp_def, id_eq] at h
  change fderiv ℝ (fun y => g (a - y)) x v = _
  rw [h.fderiv]
  simp [directionalKernel, ContinuousLinearMap.comp_apply]

/-- The two reflection signs cancel in the second derivative. -/
theorem directionalSecond_reflect {g : Plane → V} (hg : ContDiff ℝ ∞ g)
    (a v w x : Plane) :
    directionalSecond (fun y => g (a - y)) v w x =
      directionalSecond g v w (a - x) := by
  have hfun : directionalKernel (fun y => g (a - y)) v =
      fun y => -directionalKernel g v (a - y) := by
    funext y
    exact directionalKernel_reflect hg a v y
  unfold directionalSecond
  rw [hfun]
  change fderiv ℝ (fun y => -directionalKernel g v (a - y)) x w = _
  rw [fderiv_fun_neg]
  change -directionalKernel (fun y => directionalKernel g v (a - y)) w x = _
  rw [directionalKernel_reflect (directionalKernel_contDiff hg v)]
  simp [directionalKernel]

/-- Translation followed by reflection preserves the actual Laplacian. -/
theorem laplacian_reflect {g : Plane → V} (hg : ContDiff ℝ ∞ g) (a x : Plane) :
    laplacian (fun y => g (a - y)) x = laplacian g (a - x) := by
  have href : ContDiff ℝ ∞ (fun y : Plane => g (a - y)) :=
    hg.comp (contDiff_const.sub contDiff_id)
  rw [laplacian_eq_sum_directionalSecond href,
    laplacian_eq_sum_directionalSecond hg]
  apply Finset.sum_congr rfl
  intro i hi
  exact directionalSecond_reflect hg a _ _ x

end DirectionalDerivatives

/-- The first directional derivative passes under the actual convolution integral. -/
theorem directionalKernel_mollified {f : Plane → ℂ} {φ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hc : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (v x : Plane) :
    directionalKernel (mollified f φ) v x = mollified f (directionalKernel φ v) x := by
  have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have h := hc.hasFDerivAt_convolution_right realKernelPair hf hφ₁ x
  change fderiv ℝ (f ⋆[realKernelPair, volume] φ) x v = _
  rw [h.fderiv]
  exact convolution_precompR_apply realKernelPair hf (hc.fderiv ℝ)
    (hφ₁.continuous_fderiv one_ne_zero) x v

/-- The second directional derivative also passes under the convolution integral. -/
theorem directionalSecond_mollified {f : Plane → ℂ} {φ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hc : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (v w x : Plane) :
    directionalSecond (mollified f φ) v w x =
      mollified f (directionalSecond φ v w) x := by
  have hfun : directionalKernel (mollified f φ) v =
      mollified f (directionalKernel φ v) := by
    funext y
    exact directionalKernel_mollified hf hc hφ v y
  unfold directionalSecond
  rw [hfun]
  exact directionalKernel_mollified hf (directionalKernel_hasCompactSupport hc v)
    (directionalKernel_contDiff hφ v) w x

/-- Finite kernel sums commute with convolution; integrability is established termwise. -/
theorem mollified_sum {ι : Type*} [Fintype ι] {f : Plane → ℂ}
    (hf : LocallyIntegrable f) (g : ι → Plane → ℝ)
    (hc : ∀ i, HasCompactSupport (g i)) (hg : ∀ i, Continuous (g i)) (x : Plane) :
    mollified f (fun y => ∑ i, g i y) x = ∑ i, mollified f (g i) x := by
  simp only [mollified_eq_integral, Finset.sum_smul]
  simpa using integral_finsetSum Finset.univ
    (fun i _ => mollified_integrable hf (hc i) (hg i) x)

/-- Commutation of the plane Laplacian with the smoothing integral. -/
theorem laplacian_mollified {f : Plane → ℂ} {φ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hc : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (x : Plane) :
    laplacian (mollified f φ) x = mollified f (laplacian φ) x := by
  let e := stdOrthonormalBasis ℝ Plane
  let k : Fin (Module.finrank ℝ Plane) → Plane → ℝ :=
    fun i => directionalSecond φ (e i) (e i)
  have hkcomp : ∀ i, HasCompactSupport (k i) :=
    fun i => directionalSecond_hasCompactSupport hc (e i) (e i)
  have hksmooth : ∀ i, ContDiff ℝ ∞ (k i) :=
    fun i => directionalSecond_contDiff hφ (e i) (e i)
  have hsum : (fun y => ∑ i, k i y) = laplacian φ := by
    funext y
    exact (laplacian_eq_sum_directionalSecond hφ y).symm
  calc
    laplacian (mollified f φ) x =
        ∑ i, directionalSecond (mollified f φ) (e i) (e i) x :=
      laplacian_eq_sum_directionalSecond (mollified_contDiff hf hc hφ) x
    _ = ∑ i, mollified f (k i) x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact directionalSecond_mollified hf hc hφ (e i) (e i) x
    _ = mollified f (fun y => ∑ i, k i y) x :=
      (mollified_sum hf k hkcomp (fun i => (hksmooth i).continuous) x).symm
    _ = mollified f (laplacian φ) x := by rw [hsum]

/-- The translated reflected kernel is a legitimate compactly supported smooth test. -/
theorem reflectedKernel_test {φ : Plane → ℝ} (hc : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (x : Plane) :
    ContDiff ℝ ∞ (fun y : Plane => φ (x - y)) ∧
      HasCompactSupport (fun y : Plane => φ (x - y)) := by
  constructor
  · exact hφ.comp (contDiff_const.sub contDiff_id)
  · exact hc.comp_homeomorph (Homeomorph.subLeft x)

/-- A weakly harmonic function has a pointwise harmonic smoothing, for every smooth
compactly supported real kernel.  This proves the weak-to-smooth convolution step
without assuming Weyl's lemma. -/
theorem mollified_laplacian_eq_zero {f : Plane → ℂ} {φ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hweak : DistributionHarmonicOn f Set.univ)
    (hc : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) (x : Plane) :
    laplacian (mollified f φ) x = 0 := by
  rcases reflectedKernel_test hc hφ x with ⟨hψ, hcψ⟩
  have hw := hweak (fun y => φ (x - y)) hψ hcψ (Set.subset_univ _)
  rw [laplacian_mollified hf hc hφ, mollified_eq_integral]
  simpa only [laplacian_reflect hφ, Complex.real_smul] using hw

theorem mollified_smooth_harmonic {f : Plane → ℂ} {φ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hweak : DistributionHarmonicOn f Set.univ)
    (hc : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (mollified f φ) ∧
      InnerProductSpace.HarmonicOnNhd (mollified f φ) Set.univ := by
  have hs := mollified_contDiff hf hc hφ
  refine ⟨hs, fun x _ => ⟨((contDiff_infty.mp hs) 2).contDiffAt, ?_⟩⟩
  exact Filter.Eventually.of_forall fun y => mollified_laplacian_eq_zero hf hweak hc hφ y

/-- Associativity for two compact kernels only requires local integrability of
the original function.  Mathlib's convolution associativity theorem performs
the double-integral Fubini exchange; its norm-integrability hypotheses are
proved here from compact support of both kernels. -/
theorem mollified_mollified_assoc {f : Plane → ℂ} {φ ψ : Plane → ℝ}
    (hf : LocallyIntegrable f)
    (hcφ : HasCompactSupport φ) (hφ : Continuous φ)
    (hcψ : HasCompactSupport ψ) (hψ : Continuous ψ) (x : Plane) :
    mollified (mollified f φ) ψ x =
      mollified f (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) x := by
  have hnormf : LocallyIntegrable (fun y => ‖f y‖) := fun y => (hf y).norm
  have hnormφ : LocallyIntegrable (fun y => ‖φ y‖) := hφ.norm.locallyIntegrable
  have hcnorm : HasCompactSupport
      ((fun y => ‖φ y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun y => ‖ψ y‖)) :=
    HasCompactSupport.convolution (L := ContinuousLinearMap.mul ℝ ℝ) hcφ.norm hcψ.norm
  have hnormcontinuous : Continuous
      ((fun y => ‖φ y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun y => ‖ψ y‖)) :=
    hcψ.norm.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hnormφ hψ.norm
  have hbilinear : ∀ (z : ℂ) (a b : ℝ),
      realKernelPair (realKernelPair z a) b =
        realKernelPair z (ContinuousLinearMap.lsmul ℝ ℝ a b) := by
    intro z a b
    change b • (a • z) = (a * b) • z
    rw [smul_smul, mul_comm]
  exact convolution_assoc realKernelPair realKernelPair realKernelPair
    (ContinuousLinearMap.lsmul ℝ ℝ) hbilinear hf.aestronglyMeasurable
    hφ.aestronglyMeasurable hψ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y =>
      hcφ.convolutionExists_right realKernelPair hf hφ y)
    (Filter.Eventually.of_forall fun y =>
      hcψ.norm.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
        hnormφ hψ.norm y)
    (hcnorm.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      hnormf hnormcontinuous x)

/-- Scalar real kernels commute, without an integrability side condition. -/
theorem realKernel_convolution_comm (φ ψ : Plane → ℝ) :
    φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ =
      ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext a b
    exact mul_comm _ _
  simpa only [hflip] using
    (convolution_flip (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ))
      (μ := (volume : Measure Plane)) (f := ψ) (g := φ))

/-- Two smoothings with compact kernels can be exchanged, for an arbitrary
locally integrable original function. -/
theorem mollified_mollified_comm {f : Plane → ℂ} {φ ψ : Plane → ℝ}
    (hf : LocallyIntegrable f)
    (hcφ : HasCompactSupport φ) (hφ : Continuous φ)
    (hcψ : HasCompactSupport ψ) (hψ : Continuous ψ) (x : Plane) :
    mollified (mollified f φ) ψ x = mollified (mollified f ψ) φ x := by
  rw [mollified_mollified_assoc hf hcφ hφ hcψ hψ,
    mollified_mollified_assoc hf hcψ hψ hcφ hφ, realKernel_convolution_comm φ ψ]

end J0RadialUniqueness
