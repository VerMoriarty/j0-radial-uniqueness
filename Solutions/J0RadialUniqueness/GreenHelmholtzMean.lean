import Solutions.J0RadialUniqueness.PlanarHelmholtzResolvent
import Solutions.J0RadialUniqueness.HelmholtzCircularMean

/-! Actual compact Green multipliers for a Helmholtz solution on the required
closed ball only. The ambient function is smooth; its PDE is entirely local. -/

noncomputable section

open MeasureTheory Laplacian
open scoped ContDiff Interval

namespace J0RadialUniqueness

theorem localConvolution_planarGreen_helmholtz_on_closedBall {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (lam : ℂ) (x : Plane) {r : ℝ} (hr : 0 < r)
    (hΔ : ∀ y ∈ Metric.closedBall x r, laplacian f y = -(lam ^ 2) * f y) :
    localConvolution (planarGreenKernel r) f x = helmholtzResolventMass r lam * f x := by
  rw [localConvolution, planarGreen_integral_eq_radial hf.continuous x hr]
  have hmean (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
      circularMean f t x = J0 ((t : ℂ) * lam) * f x :=
    circularMean_helmholtz_on_closedBall hf lam x hr.le hΔ ht
  calc
    _ = ∫ t : ℝ in (0 : ℝ)..r,
        (greenRadialWeight r t • J0 ((t : ℂ) * lam)) * f x := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) r := by
        simpa only [Set.uIcc_of_le hr.le] using ht
      dsimp only
      rw [hmean t ht']
      simp only [Complex.real_smul, mul_assoc]
    _ = (∫ t : ℝ in (0 : ℝ)..r,
        greenRadialWeight r t • J0 ((t : ℂ) * lam)) * f x :=
      intervalIntegral.integral_mul_const _ _
    _ = helmholtzResolventMass r lam * f x := by
      rw [show (fun t : ℝ => greenRadialWeight r t • J0 ((t : ℂ) * lam)) =
          (fun t : ℝ => (t * Real.log (r / t)) • J0 ((t : ℂ) * lam)) from rfl,
        integral_greenBessel_eq_Q hr lam]
      congr 1
      unfold helmholtzResolventMass helmholtzResolventArg
      congr 2
      ring

theorem closedBall_subset_planeBall_of_center_inner {x : Plane} {R r : ℝ}
    (hx : x ∈ planeBall (R - r)) : Metric.closedBall x r ⊆ planeBall R := by
  intro y hy
  have hd : ‖x - y‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
  have hh := norm_sub_lt_of_inner_ball hx hd
  simpa only [sub_sub_cancel] using hh

theorem localConvolution_planarGreen_helmholtz_on_ball {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (lam : ℂ) {R r : ℝ} (hr : 0 < r)
    (hΔ : ∀ y ∈ planeBall R, laplacian f y = -(lam ^ 2) * f y)
    {x : Plane} (hx : x ∈ planeBall (R - r)) :
    localConvolution (planarGreenKernel r) f x = helmholtzResolventMass r lam * f x :=
  localConvolution_planarGreen_helmholtz_on_closedBall hf lam x hr
    (fun y hy => hΔ y (closedBall_subset_planeBall_of_center_inner hx hy))

end J0RadialUniqueness
