import Solutions.J0RadialUniqueness.Series
import Solutions.J0RadialUniqueness.Spectral

/-! Algebraic consequences and spectral equivalence for the actual series-defined `J0`.
The analytic escape and uniqueness statements are explicit theorem parameters.
No result in this file asserts that those analytic hypotheses have been proved. -/

noncomputable section

namespace J0RadialUniqueness

/-- Theorem A implies Corollary B; the analytic premise is explicit. -/
theorem rayUniqueness_of_radialEscape (hEscape : RadialEscape) : RayUniqueness := by
  intro v hv r₁ r₂ hr₁ hr₂ h₁ h₂
  have impossible (a b : ℝ) (ha : 0 < a) (hab : a < b)
      (hJa : J0 ((a : ℂ) * v) = 1) (hJb : J0 ((b : ℂ) * v) = 1) : False := by
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hc : 1 < b / a := (one_lt_div ha).mpr hab
    have hscale : ((b / a : ℝ) : ℂ) * ((a : ℂ) * v) = (b : ℂ) * v := by
      rw [Complex.ofReal_div, ← mul_assoc, div_mul_cancel₀ _ haC]
    have hg := hEscape ((a : ℂ) * v) (mul_ne_zero haC hv) hJa (b / a) hc
    rw [hscale, hJb, norm_one] at hg
    have hp : 1 < Real.rpow (b / a) (7 / 25 : ℝ) :=
      Real.one_lt_rpow hc (by norm_num)
    linarith
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  · exact False.elim (impossible r₁ r₂ hr₁ hlt h₁ h₂)
  · exact heq
  · exact False.elim (impossible r₂ r₁ hr₂ hgt h₂ h₁)

/-- Positive root ratios must be one, conditional on ray uniqueness. -/
theorem positive_ratio_eq_one_of_rayUniqueness (hRay : RayUniqueness)
    {c : ℝ} (hc : 0 < c) (hmem : (c : ℂ) ∈ ratioSet) : c = 1 := by
  rcases hmem with ⟨α, hα, β, hβ, hquot⟩
  have hαeq : α = (c : ℂ) * β := (div_eq_iff hβ.1).mp hquot
  apply hRay β hβ.1 c 1 hc (by norm_num)
  · simpa only [← hαeq] using hα.2
  · simpa using hβ.2

/-- Equation (6.1): positive nonunit spectral ratios are excluded, conditional on uniqueness. -/
theorem not_mem_ratioSet_of_pos_ne_one (hRay : RayUniqueness)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≠ 1) : (c : ℂ) ∉ ratioSet := by
  intro hmem
  exact hc₁ (positive_ratio_eq_one_of_rayUniqueness hRay hc hmem)

/-- Distinct positive radii have no common nonzero spectral point if uniqueness holds. -/
theorem no_common_spectral_point_of_rayUniqueness (hRay : RayUniqueness)
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hne : r₁ ≠ r₂) :
    ¬ ∃ lam : ℂ, lam ≠ 0 ∧
      J0 (Complex.I * lam * (r₁ : ℂ)) = 1 ∧
      J0 (Complex.I * lam * (r₂ : ℂ)) = 1 := by
  intro hspectral
  have hratio := (spectral_equivalence r₁ r₂ hr₁ hr₂).mpr hspectral
  have heq := positive_ratio_eq_one_of_rayUniqueness hRay (div_pos hr₁ hr₂) hratio
  exact hne ((div_eq_one_iff_eq hr₂.ne').mp heq)

end J0RadialUniqueness
