import Solutions.J0RadialUniqueness.LocalQuotientBoundaryBounds
import Solutions.J0RadialUniqueness.EntireTriangleLiouville

/-! The actual smooth local inner-ball uniqueness step. Every spectral quotient
input of PL and Liouville is discharged by the actual kernel estimates and
pole elimination. This does not yet recover the outer annulus of the paper's
full ball. -/

noncomputable section

open MeasureTheory Laplacian Filter
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem localResolventQuotient_eq_zero {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) :
    ∀ lam : ℂ, localResolventQuotient r₁ u x lam = 0 := by
  obtain ⟨C, _, N₀, hN, hdiag, hvertical, hsample⟩ :=
    localResolventQuotient_boundary_bounds hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx
  obtain ⟨A, hA, B, hB, hgrowth⟩ :=
    localResolventQuotient_outer_exp_bound hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx
  have hNpos (n : ℕ) : 0 < resolventVerticalSequence r₁ N₀ n := by
    unfold resolventVerticalSequence
    exact div_pos (add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (add_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg N₀)))
      (div_pos (mul_pos (by norm_num) Real.pi_pos) (by norm_num))) hr₁
  exact entire_even_eq_zero_of_outer_growth_and_triangle_bounds
    (localResolventQuotient_differentiable hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx)
    (localResolventQuotient_neg hr₁ hu.continuous x)
    (resolventVerticalSequence r₁ N₀) hNpos hN hA hB hgrowth hdiag hvertical hsample

/-- Two actual Green equations force u to vanish on the full natural ball of
the first kernel, under the exact no-common-zero condition. -/
theorem localInnerKernelUniqueness {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0) :
    ∀ x ∈ planeBall (R - r₁), u x = 0 := by
  let h : Plane → ℂ := complexConvolution (planarHelmholtzResolventT r₁ 0) u
  have hhzero : ∀ x ∈ planeBall (R - r₁), h x = 0 := by
    intro x hx
    have hf := localResolventQuotient_factorization hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx 0
    rw [localResolventQuotient_eq_zero hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx 0, mul_zero] at hf
    exact hf
  intro x hx
  have heq : h =ᶠ[𝓝 x] (fun _ : Plane => (0 : ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact hhzero y hy
  have hΔ : laplacian h x = 0 := by
    simpa using (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
  have hop := planarHelmholtzResolventT_convolution_operator hu hr₁ 0 x
  change laplacian h x + (0 : ℂ) ^ 2 * h x =
    localConvolution (planarGreenKernel r₁) u x - helmholtzResolventMass r₁ 0 * u x at hop
  rw [hΔ, hG₁ x hx] at hop
  have hm : helmholtzResolventMass r₁ 0 ≠ 0 := by
    rw [helmholtzResolventMass_zero_parameter]
    exact div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr₁.ne')) (by norm_num)
  have hprod : helmholtzResolventMass r₁ 0 * u x = 0 := by linear_combination hop
  exact (mul_eq_zero.mp hprod).resolve_left hm

end J0RadialUniqueness
