import Solutions.J0RadialUniqueness.LocalInnerKernelUniqueness
import Solutions.J0RadialUniqueness.AnnularCircleRecovery
import Solutions.J0RadialUniqueness.GreenConvolutionDifferential
import Solutions.J0RadialUniqueness.ClassicalWeakHarmonic

/-! Full-ball uniqueness for the actual smooth two-radius equations.
The smaller radius is used for annular recovery, so the strict hypothesis
R > r₁+r₂ supplies precisely the positive geometric margin required there. -/

noncomputable section
open MeasureTheory Laplacian
open scoped ContDiff

namespace J0RadialUniqueness

theorem localKernelUniqueness_of_le {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hle : r₁ ≤ r₂)
    (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0) :
    ∀ x ∈ planeBall R, u x = 0 := by
  have hinner := localInnerKernelUniqueness hu hr₁ hr₂ hR hNoCommon hG₁ hG₂
  have hmean := circularMean_eq_zero_of_green_and_value_zero hu hr₁
    Metric.isOpen_ball hG₁ hinner
  have hfull := eq_zero_on_larger_ball_of_circularMean_zero hu hr₁
    (show r₁ < R - r₁ by linarith) hinner hmean
  simpa only [sub_add_cancel] using hfull

theorem localKernelUniqueness {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0) :
    ∀ x ∈ planeBall R, u x = 0 := by
  rcases le_total r₁ r₂ with hle | hle
  · exact localKernelUniqueness_of_le hu hr₁ hr₂ hle hR hNoCommon hG₁ hG₂
  · exact localKernelUniqueness_of_le hu hr₂ hr₁ hle
      (by simpa only [add_comm] using hR) (fun lam => (hNoCommon lam).symm) hG₂ hG₁

theorem smoothLocalTwoRadius_noCommon {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hm₁ : MeanIdentityOn f r₁ (planeBall (R - r₁)))
    (hm₂ : MeanIdentityOn f r₂ (planeBall (R - r₂))) :
    DistributionHarmonicOn f (planeBall R) := by
  apply (distributionHarmonicOn_iff_laplacian_eq_zero Metric.isOpen_ball
    ((contDiff_infty.mp hf) 2).contDiffOn).mpr
  exact localKernelUniqueness (laplacian_contDiff_infty hf) hr₁ hr₂ hR hNoCommon
    (localConvolution_planarGreen_laplacian_eq_zero_of_meanIdentity hf hr₁ hm₁)
    (localConvolution_planarGreen_laplacian_eq_zero_of_meanIdentity hf hr₂ hm₂)

end J0RadialUniqueness
