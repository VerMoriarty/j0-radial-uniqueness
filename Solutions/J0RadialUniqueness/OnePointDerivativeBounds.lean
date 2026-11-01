import Solutions.J0RadialUniqueness.SimpleOnePoints

/-! Quantitative inverse-polynomial derivative control on the actual nonzero
Bessel one-point set. The strict radial derivative estimate already proved
from the actual amplitude decomposition gives the estimate on all quadrants;
no asymptotic derivative formula is assumed. -/

noncomputable section

open Filter
open scoped Topology

namespace J0RadialUniqueness

/-- At a genuine one-point the derivative of the real logarithmic modulus is
the real part of the actual complex radial derivative. -/
theorem rayLogNorm_hasDerivAt_at_one_point {z : ℂ} (hJ : J0 z = 1) :
    HasDerivAt (rayLogNorm z) (z * deriv J0 z).re (1 : ℝ) := by
  have hj : HasDerivAt J0 (deriv J0 z) ((1 : ℂ) * z) := by
    simpa only [one_mul] using (J0_differentiable z).hasDerivAt
  have hp := (hj.comp (1 : ℂ) ((hasDerivAt_id (1 : ℂ)).mul_const z)).comp_ofReal
  have hpath : HasDerivAt (fun t : ℝ => J0 ((t : ℂ) * z)) (z * deriv J0 z) (1 : ℝ) := by
    convert! hp using 1 <;> simp only [Function.comp_def, id_eq, Complex.ofReal_one, one_mul] <;> ring
  have hn : J0 ((((1 : ℝ) : ℂ)) * z) ≠ 0 := by
    rw [Complex.ofReal_one, one_mul, hJ]
    exact one_ne_zero
  have hh := hasDerivAt_log_norm hpath hn
  have hfun : rayLogNorm z = (fun t : ℝ => Real.log ‖J0 ((t : ℂ) * z)‖) := by
    funext t
    rfl
  rw [hfun]
  simpa only [Complex.ofReal_one, one_mul, hJ, div_one] using hh

/-- A quantitative radial derivative estimate for every nonzero one-point,
with the quadrant symmetry discharged at the level of the actual log norm. -/
theorem J0_one_point_radial_derivative_gt {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    (7 / 25 : ℝ) < (z * deriv J0 z).re := by
  have hlog := rayLogNorm_hasDerivAt_at_one_point hJ
  have hl := globalLocalization z hz hJ
  have hsector := quadrantRep_in_principalSector z hl.1 hl.2.1
  have hpoint := J0_quadrantRep z hJ
  have heq : rayLogNorm (quadrantRep z) =ᶠ[𝓝 (1 : ℝ)] rayLogNorm z := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    unfold rayLogNorm
    rw [norm_J0_mul_quadrantRep t ht.le z]
  have hrep := hlog.congr_of_eventuallyEq heq
  have hb := ((paper_5_1 (quadrantRep z) hpoint hsector).1 1 le_rfl).2
  unfold rayLogDerivative at hb
  rw [hrep.deriv] at hb
  simpa only [one_mul] using hb

theorem J0_one_point_weighted_derivative_norm_gt {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    (7 / 25 : ℝ) < ‖z‖ * ‖deriv J0 z‖ := by
  have hh := (J0_one_point_radial_derivative_gt hz hJ).trans_le (Complex.re_le_norm (z * deriv J0 z))
  simpa only [norm_mul] using hh

/-- A fully explicit inverse-polynomial lower bound for the actual derivative.
It holds over the whole nonzero one-point set, without a large-root cutoff. -/
theorem J0_derivative_norm_lower_bound_at_one_point {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    (7 / 25 : ℝ) / ‖z‖ < ‖deriv J0 z‖ := by
  apply (div_lt_iff₀ (norm_pos_iff.mpr hz)).2
  have hh := J0_one_point_weighted_derivative_norm_gt hz hJ
  nlinarith

/-- Inverse derivative coefficients at the actual roots grow at most linearly. -/
theorem J0_inverse_derivative_norm_upper_bound_at_one_point {z : ℂ}
    (hz : z ≠ 0) (hJ : J0 z = 1) :
    ‖(deriv J0 z)⁻¹‖ < (25 / 7 : ℝ) * ‖z‖ := by
  have hdpos : 0 < ‖deriv J0 z‖ := norm_pos_iff.mpr (J0_deriv_ne_zero_at_one_point hz hJ)
  rw [norm_inv, ← one_div ‖deriv J0 z‖]
  apply (div_lt_iff₀ hdpos).2
  have hh := J0_one_point_weighted_derivative_norm_gt hz hJ
  nlinarith

/-- A conventional polynomial-growth packaging for spectral residue estimates. -/
theorem J0_one_point_inverse_derivative_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → J0 z = 1 →
      ‖(deriv J0 z)⁻¹‖ ≤ C * (1 + ‖z‖) := by
  refine ⟨25 / 7, by norm_num, ?_⟩
  intro z hz hJ
  have hh := J0_inverse_derivative_norm_upper_bound_at_one_point hz hJ
  linarith

end J0RadialUniqueness
