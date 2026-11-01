import Solutions.J0RadialUniqueness.BesselPolynomialExpansion
import Solutions.J0RadialUniqueness.SharpnessSpectral
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-! Existence of a genuine right-half-plane one-point follows from the
proved spectral polynomial expansion and its nonzero highest coefficient.
This also closes both geometric-counterexample branches for equal radii. -/

noncomputable section
open Set
open scoped ContDiff

namespace J0RadialUniqueness

theorem rightOnePoint_nonempty : Nonempty RightOnePoint := by
  by_contra h
  letI : IsEmpty RightOnePoint := not_nonempty_iff.mp h
  have hzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (besselPolePolynomial 2).eval (t : ℂ) = 0 := by
    rw [← besselRadialRootSeries_eq_polynomial 2 (by norm_num) ht]
    simp only [besselRadialRootSeries, tsum_empty]
  have hI : ((Complex.ofReal) '' Icc (0 : ℝ) 1).Infinite :=
    (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image Complex.ofReal_injective.injOn
  have hroots : {z : ℂ | (besselPolePolynomial 2).IsRoot z}.Infinite := by
    apply hI.mono
    rintro z ⟨t, ht, rfl⟩
    exact hzero t ht
  have heq := Polynomial.eq_zero_of_infinite_isRoot (besselPolePolynomial 2) hroots
  exact besselPolePolynomial_highest_coeff_ne_zero 2 (by rw [heq]; simp)

theorem exists_right_one_point : ∃ z : ℂ, z ≠ 0 ∧ J0 z = 1 ∧ 0 < z.re := by
  obtain ⟨z⟩ := rightOnePoint_nonempty
  exact ⟨z, z.val.property.1, z.val.property.2, z.property⟩

theorem exists_nonzero_spectral_frequency (r : ℝ) (hr : 0 < r) :
    ∃ lam : ℂ, lam ≠ 0 ∧ J0 (Complex.I * lam * (r : ℂ)) = 1 := by
  obtain ⟨z, hz, hJ, _⟩ := exists_right_one_point
  let lam : ℂ := -Complex.I * z / (r : ℂ)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hl : lam ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz) hrC
  refine ⟨lam, hl, ?_⟩
  have he : Complex.I * lam * (r : ℂ) = z := by
    dsimp only [lam]
    field_simp [hrC]
    rw [Complex.I_sq]
    norm_num
  rw [he]
  exact hJ

theorem boundaryFiniteSmoothCounterexample_equal_radii (r : ℝ) (hr : 0 < r) (s : ℕ) :
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ (s : WithTop ℕ∞) f (planeBall (r + r)) ∧
      MeasureTheory.LocallyIntegrableOn f (planeBall (r + r)) ∧
      MeanIdentityOn f r (planeBall ((r + r) - r)) ∧
      MeanIdentityOn f r (planeBall ((r + r) - r)) ∧
      ¬ DistributionHarmonicOn f (planeBall (r + r)) := by
  obtain ⟨lam, hl, hJ⟩ := exists_nonzero_spectral_frequency r hr
  exact boundaryFiniteSmoothCounterexample_of_common_spectral_root hr hr hl hJ hJ s

theorem subcriticalSmoothCounterexample_equal_radii (r R : ℝ) (hr : 0 < r)
    (hR : r < R) (hsub : R < r + r) :
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ ∞ f (planeBall R) ∧ MeasureTheory.LocallyIntegrableOn f (planeBall R) ∧
      MeanIdentityOn f r (planeBall (R - r)) ∧ MeanIdentityOn f r (planeBall (R - r)) ∧
      ¬ DistributionHarmonicOn f (planeBall R) := by
  obtain ⟨lam, hl, hJ⟩ := exists_nonzero_spectral_frequency r hr
  exact subcriticalSmoothCounterexample_of_common_spectral_root hr hr
    (by simpa only [max_self] using hR) hsub hl hJ hJ

end J0RadialUniqueness
