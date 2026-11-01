import Solutions.J0RadialUniqueness.CompactComplexConvolution
import Solutions.J0RadialUniqueness.PlanarHelmholtzResolvent

/-! The actual compact resolvent applied to a smooth function. Kernel
integrability and compact support, smooth convolution and its Laplacian are
discharged here; no PDE identity for the filtered function is assumed. -/

noncomputable section

open MeasureTheory Laplacian
open scoped ContDiff

namespace J0RadialUniqueness

theorem complexConvolution_add_const_mul {k f g : Plane → ℂ}
    (hk : Integrable k) (hc : HasCompactSupport k) (hf : Continuous f) (hg : Continuous g)
    (c : ℂ) (x : Plane) :
    complexConvolution k (fun y => f y + c * g y) x =
      complexConvolution k f x + c * complexConvolution k g x := by
  simp only [complexConvolution_eq_integral]
  have hi := complexConvolution_integrable hk hc hf x
  have hj := complexConvolution_integrable hk hc hg x
  calc
    _ = ∫ y : Plane, k y * f (x - y) + c * (k y * g (x - y)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring)
    _ = _ := by rw [integral_add hi (hj.const_mul c), integral_const_mul]

theorem planarHelmholtzResolventT_convolution_contDiff {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    ContDiff ℝ ∞ (complexConvolution (planarHelmholtzResolventT r lam) u) :=
  complexConvolution_contDiff (planarHelmholtzResolventT_integrable hr lam)
    (planarHelmholtzResolventT_hasCompactSupport r lam) hu

theorem planarHelmholtzResolventT_convolution_operator {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r : ℝ} (hr : 0 < r) (lam : ℂ) (x : Plane) :
    laplacian (complexConvolution (planarHelmholtzResolventT r lam) u) x +
        lam ^ 2 * complexConvolution (planarHelmholtzResolventT r lam) u x =
      localConvolution (planarGreenKernel r) u x - helmholtzResolventMass r lam * u x := by
  have hk := planarHelmholtzResolventT_integrable hr lam
  have hc := planarHelmholtzResolventT_hasCompactSupport r lam
  rw [laplacian_complexConvolution hk hc hu x]
  rw [← complexConvolution_add_const_mul hk hc
    (laplacian_contDiff_infty hu).continuous hu.continuous (lam ^ 2) x]
  exact planarHelmholtzResolventT_weak hu x hr lam

/-- A zero of the actual first kernel spectrum produces a genuine local
Helmholtz solution on precisely the natural smaller ball. -/
theorem planarHelmholtzResolventT_convolution_helmholtz_on_ball {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {R r : ℝ} (hr : 0 < r) (lam : ℂ)
    (hroot : helmholtzResolventMass r lam = 0)
    (hzero : ∀ x ∈ planeBall (R - r), localConvolution (planarGreenKernel r) u x = 0) :
    ∀ x ∈ planeBall (R - r),
      laplacian (complexConvolution (planarHelmholtzResolventT r lam) u) x =
        -(lam ^ 2) * complexConvolution (planarHelmholtzResolventT r lam) u x := by
  intro x hx
  have hh := planarHelmholtzResolventT_convolution_operator hu hr lam x
  rw [hzero x hx, hroot, zero_mul, sub_zero] at hh
  linear_combination hh

end J0RadialUniqueness
