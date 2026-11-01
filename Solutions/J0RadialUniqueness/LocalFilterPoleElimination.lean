import Solutions.J0RadialUniqueness.CompactComplexConvolutionCommute
import Solutions.J0RadialUniqueness.HelmholtzFilterConvolution
import Solutions.J0RadialUniqueness.GreenHelmholtzMean
import Solutions.J0RadialUniqueness.HelmholtzBallUniqueContinuation
import Solutions.J0RadialUniqueness.SpectralNoCommonZeros
import Mathlib.Tactic

/-! Actual elimination of every first-filter spectral pole on its full natural
ball. The filtered PDE, kernel exchange, local Green multiplier and unique
continuation are all proved dependencies. The strict radius margin is retained.
-/

noncomputable section
open MeasureTheory Laplacian Set
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem complexConvolution_cast_planarGreen (r : ℝ) (u : Plane → ℂ) (x : Plane) :
    complexConvolution (fun y : Plane => (planarGreenKernel r y : ℂ)) u x =
      localConvolution (planarGreenKernel r) u x := by
  simp only [complexConvolution_eq_integral, localConvolution, Complex.real_smul]

theorem planarHelmholtzResolventT_support_radius (r : ℝ) (lam : ℂ) {y : Plane}
    (hy : planarHelmholtzResolventT r lam y ≠ 0) : ‖y‖ ≤ r :=
  compactRadialComplexKernel_support_radius r _ hy

theorem localFilterPoleElimination {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    (lam : ℂ) (hroot : helmholtzResolventMass r₁ lam = 0) :
    ∀ x ∈ planeBall (R - r₁),
      complexConvolution (planarHelmholtzResolventT r₁ lam) u x = 0 := by
  let h : Plane → ℂ := complexConvolution (planarHelmholtzResolventT r₁ lam) u
  have hh : ContDiff ℝ ∞ h := planarHelmholtzResolventT_convolution_contDiff hu hr₁ lam
  have hPDE : ∀ x ∈ planeBall (R - r₁), laplacian h x = -(lam ^ 2) * h x :=
    planarHelmholtzResolventT_convolution_helmholtz_on_ball hu hr₁ lam hroot hG₁
  have hm₂ : helmholtzResolventMass r₂ lam ≠ 0 := by
    rcases hNoCommon lam with h₁ | h₂
    · exact False.elim (h₁ hroot)
    · exact h₂
  have hTI := planarHelmholtzResolventT_integrable hr₁ lam
  have hGI : Integrable (fun y : Plane => (planarGreenKernel r₂ y : ℂ)) :=
    (planarGreenKernel_integrable hr₂).ofReal
  have hTs (y : Plane) (hy : planarHelmholtzResolventT r₁ lam y ≠ 0) : ‖y‖ ≤ r₁ :=
    planarHelmholtzResolventT_support_radius r₁ lam hy
  have hGs (y : Plane) (hy : (planarGreenKernel r₂ y : ℂ) ≠ 0) : ‖y‖ ≤ r₂ := by
    apply planarGreenKernel_support_radius r₂
    intro hz
    exact hy (by rw [hz, Complex.ofReal_zero])
  have hGfun : complexConvolution (fun y : Plane => (planarGreenKernel r₂ y : ℂ)) u =
      localConvolution (planarGreenKernel r₂) u :=
    funext (complexConvolution_cast_planarGreen r₂ u)
  have hzeroSmall : ∀ x ∈ planeBall (R - r₁ - r₂), h x = 0 := by
    intro x hx
    have hTzero : complexConvolution (planarHelmholtzResolventT r₁ lam)
        (localConvolution (planarGreenKernel r₂) u) x = 0 := by
      rw [complexConvolution_eq_integral]
      have he : (fun y : Plane => planarHelmholtzResolventT r₁ lam y *
          localConvolution (planarGreenKernel r₂) u (x - y)) = 0 := by
        funext y
        change planarHelmholtzResolventT r₁ lam y *
          localConvolution (planarGreenKernel r₂) u (x - y) = 0
        by_cases hy : planarHelmholtzResolventT r₁ lam y = 0
        · simp only [hy, zero_mul, Pi.zero_apply]
        · have hx' : x ∈ planeBall ((R - r₂) - r₁) := by
            have heq : R - r₁ - r₂ = (R - r₂) - r₁ := by ring
            simpa only [heq] using hx
          have hyinside := norm_sub_lt_of_inner_ball hx' (hTs y hy)
          rw [hG₂ (x - y) hyinside, mul_zero]
      rw [he]
      exact integral_zero _ _
    have hGzero : localConvolution (planarGreenKernel r₂) h x = 0 := by
      calc
        _ = complexConvolution (fun y : Plane => (planarGreenKernel r₂ y : ℂ)) h x :=
          (complexConvolution_cast_planarGreen r₂ h x).symm
        _ = complexConvolution (planarHelmholtzResolventT r₁ lam)
            (complexConvolution (fun y : Plane => (planarGreenKernel r₂ y : ℂ)) u) x :=
          complexConvolution_iterated_comm_of_radius hGI hTI hGs hTs hu.continuous x
        _ = complexConvolution (planarHelmholtzResolventT r₁ lam)
            (localConvolution (planarGreenKernel r₂) u) x := by rw [hGfun]
        _ = 0 := hTzero
    have hmean := localConvolution_planarGreen_helmholtz_on_ball hh lam hr₂ hPDE hx
    have hprod : helmholtzResolventMass r₂ lam * h x = 0 := hmean.symm.trans hGzero
    exact (mul_eq_zero.mp hprod).resolve_left hm₂
  exact helmholtz_eq_zero_on_ball_of_eq_zero_on_smaller_ball hh lam
    (show 0 < R - r₁ - r₂ by linarith) (show R - r₁ - r₂ < R - r₁ by linarith)
    hPDE hzeroSmall

theorem localFilterPoleElimination_of_ratio_exclusion {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hratio : ((r₁ / r₂ : ℝ) : ℂ) ∉ ratioSet)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    (lam : ℂ) (hroot : helmholtzResolventMass r₁ lam = 0) :
    ∀ x ∈ planeBall (R - r₁), complexConvolution (planarHelmholtzResolventT r₁ lam) u x = 0 :=
  localFilterPoleElimination hu hr₁ hr₂ hR
    (helmholtzResolventMasses_no_common_zero_of_ratio_exclusion hr₁ hr₂ hratio) hG₁ hG₂ lam hroot

end J0RadialUniqueness
