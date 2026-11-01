import Solutions.J0RadialUniqueness.RotatedQuadrantPL
import Solutions.J0RadialUniqueness.TriangleMaximumPrinciple
import Solutions.J0RadialUniqueness.LocalQuotientOuterGrowth
import Mathlib.Analysis.Complex.Liouville

/-! An unweighted PL--triangle--Liouville tool.

This general theorem retains its boundary and growth estimates as explicit
mathematical inputs. It does not assert those inputs for the local Bessel
quotient and does not itself prove the paper's local two-radius theorem.
-/

noncomputable section

open Set Filter Bornology
open scoped Topology ComplexConjugate

namespace J0RadialUniqueness

theorem outerQuadrantRotation_real_ray_diagonal (t : ℝ) :
    |(outerQuadrantRotation * (t : ℂ)).im| = |(outerQuadrantRotation * (t : ℂ)).re| := by
  simp [Complex.mul_re, Complex.mul_im, outerQuadrantRotation_re, outerQuadrantRotation_im]

theorem outerQuadrantRotation_imag_ray_diagonal (t : ℝ) :
    |(outerQuadrantRotation * ((t : ℂ) * Complex.I)).im| =
      |(outerQuadrantRotation * ((t : ℂ) * Complex.I)).re| := by
  simp [Complex.mul_re, Complex.mul_im, outerQuadrantRotation_re, outerQuadrantRotation_im, abs_neg]

/-- Every point of the upper outer sector has a preimage in the closed first
quadrant under the actual unit rotation exp(iπ/4). -/
theorem exists_outerQuadrantRotation_preimage {z : ℂ} (hz : |z.re| ≤ z.im) :
    ∃ w : ℂ, 0 ≤ w.re ∧ 0 ≤ w.im ∧ outerQuadrantRotation * w = z := by
  let c : ℝ := Real.sqrt 2 / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let w : ℂ := conj outerQuadrantRotation * z
  have hwr : w.re = c * (z.re + z.im) := by
    dsimp only [w]
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      outerQuadrantRotation_re, outerQuadrantRotation_im]
    dsimp [c]
    ring
  have hwi : w.im = c * (z.im - z.re) := by
    dsimp only [w]
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      outerQuadrantRotation_re, outerQuadrantRotation_im]
    dsimp [c]
    ring
  have hre : 0 ≤ w.re := by
    rw [hwr]
    exact mul_nonneg hc (by linarith [(abs_le.mp hz).1])
  have him : 0 ≤ w.im := by
    rw [hwi]
    exact mul_nonneg hc (by linarith [(abs_le.mp hz).2])
  have hunit : outerQuadrantRotation * conj outerQuadrantRotation = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_outerQuadrantRotation]
    norm_num
  refine ⟨w, hre, him, ?_⟩
  dsimp only [w]
  rw [← mul_assoc, hunit, one_mul]

/-- Entire even functions with actual order-one outer growth and uniform bounds
on the four diagonal rays and an exhausting sequence of right vertical edges
are bounded by that same constant on the whole plane. -/
theorem entire_even_norm_le_of_outer_growth_and_triangle_bounds
    {q : ℂ → ℂ} (hq : Differentiable ℂ q) (heven : ∀ z : ℂ, q (-z) = q z)
    (N : ℕ → ℝ) (_hNpos : ∀ n : ℕ, 0 < N n) (hN : Tendsto N atTop atTop)
    {C A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, |z.re| ≤ |z.im| → 1 ≤ ‖z‖ →
      ‖q z‖ ≤ A * Real.exp (B * ‖z‖))
    (hdiag : ∀ z : ℂ, |z.im| = |z.re| → ‖q z‖ ≤ C)
    (hvertical : ∀ n : ℕ, ∀ z : ℂ, z.re = N n → |z.im| ≤ N n → ‖q z‖ ≤ C) :
    ∀ z : ℂ, ‖q z‖ ≤ C := by
  have hrot : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ w.im →
      ‖q (outerQuadrantRotation * w)‖ ≤ C := by
    apply rotatedQuadrantPL_order_one q hq outerQuadrantRotation norm_outerQuadrantRotation hA hB
    · intro t _
      exact hdiag _ (outerQuadrantRotation_real_ray_diagonal t)
    · intro t _
      exact hdiag _ (outerQuadrantRotation_imag_ray_diagonal t)
    · intro w hre him hn
      have hnorm : ‖outerQuadrantRotation * w‖ = ‖w‖ := by
        rw [norm_mul, norm_outerQuadrantRotation, one_mul]
      have hh := hgrowth (outerQuadrantRotation * w)
        (outerQuadrantRotation_mem_outer_sector hre.le him.le) (by rwa [hnorm])
      simpa only [hnorm] using hh
  have hupper : ∀ z : ℂ, |z.re| ≤ z.im → ‖q z‖ ≤ C := by
    intro z hz
    obtain ⟨w, hre, him, heq⟩ := exists_outerQuadrantRotation_preimage hz
    have hh := hrot w hre him
    rwa [heq] at hh
  have houter : ∀ z : ℂ, |z.re| ≤ |z.im| → ‖q z‖ ≤ C := by
    intro z hz
    by_cases him : 0 ≤ z.im
    · exact hupper z (by simpa only [abs_of_nonneg him] using hz)
    · have himneg : z.im < 0 := lt_of_not_ge him
      have hneg : |(-z).re| ≤ (-z).im := by
        simpa only [Complex.neg_re, Complex.neg_im, abs_neg, abs_of_neg himneg] using hz
      have hh := hupper (-z) hneg
      simpa only [heven z] using hh
  have hright : ∀ z ∈ closedRightPrincipalWedge, ‖q z‖ ≤ C := by
    apply norm_le_on_rightPrincipalWedge_of_uniform_sides hq N hN
    · intro z hside hre
      exact hdiag z (by simpa only [abs_of_nonneg hre] using hside)
    · exact hvertical
  intro z
  rcases le_total |z.re| |z.im| with hzouter |hzinner
  · exact houter z hzouter
  · by_cases hre : 0 ≤ z.re
    · apply hright z
      change |z.im| ≤ z.re
      simpa only [abs_of_nonneg hre] using hzinner
    · have hreneg : z.re < 0 := lt_of_not_ge hre
      have hh : ‖q (-z)‖ ≤ C := by
        apply hright (-z)
        change |(-z).im| ≤ (-z).re
        simpa only [Complex.neg_im, abs_neg, Complex.neg_re, abs_of_neg hreneg] using hzinner
      simpa only [heven z] using hh

/-- Liouville and any sequence of samples tending to zero turn an actual global
norm bound into pointwise vanishing. No growth theorem is hidden in this step. -/
theorem entire_eq_zero_of_global_norm_bound_and_samples
    {q : ℂ → ℂ} (hq : Differentiable ℂ q) {C : ℝ} (hbound : ∀ z : ℂ, ‖q z‖ ≤ C)
    (N : ℕ → ℝ) (hsample : Tendsto (fun n : ℕ => q (N n : ℂ)) atTop (𝓝 0)) :
    ∀ z : ℂ, q z = 0 := by
  have hb : IsBounded (Set.range q) := isBounded_iff_forall_norm_le.mpr ⟨C, by
    rintro y ⟨z, rfl⟩
    exact hbound z⟩
  have hconst : ∀ z : ℂ, q z = q 0 := fun z => hq.apply_eq_apply_of_bounded hb z 0
  have he : (fun n : ℕ => q (N n : ℂ)) = fun _ : ℕ => q 0 :=
    funext (fun n => hconst (N n : ℂ))
  have hsample_const : Tendsto (fun _ : ℕ => q 0) atTop (𝓝 0) := by
    rwa [he] at hsample
  have hzero : q 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hsample_const
  intro z
  exact (hconst z).trans hzero

/-- The unweighted PL--triangle--Liouville combination. The outer growth,
diagonal and vertical bounds are explicit hypotheses of this general tool. -/
theorem entire_even_eq_zero_of_outer_growth_and_triangle_bounds
    {q : ℂ → ℂ} (hq : Differentiable ℂ q) (heven : ∀ z : ℂ, q (-z) = q z)
    (N : ℕ → ℝ) (hNpos : ∀ n : ℕ, 0 < N n) (hN : Tendsto N atTop atTop)
    {C A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, |z.re| ≤ |z.im| → 1 ≤ ‖z‖ →
      ‖q z‖ ≤ A * Real.exp (B * ‖z‖))
    (hdiag : ∀ z : ℂ, |z.im| = |z.re| → ‖q z‖ ≤ C)
    (hvertical : ∀ n : ℕ, ∀ z : ℂ, z.re = N n → |z.im| ≤ N n → ‖q z‖ ≤ C)
    (hsample : Tendsto (fun n : ℕ => q (N n : ℂ)) atTop (𝓝 0)) :
    ∀ z : ℂ, q z = 0 :=
  entire_eq_zero_of_global_norm_bound_and_samples hq
    (entire_even_norm_le_of_outer_growth_and_triangle_bounds hq heven N hNpos hN hA hB
      hgrowth hdiag hvertical) N hsample

end J0RadialUniqueness
