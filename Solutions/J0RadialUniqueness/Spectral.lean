import Definitions.J0RadialUniqueness.Basic
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

/-- The exact algebraic spectral equivalence from Proposition 6.1. -/
theorem spectral_equivalence (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    ((r₁ / r₂ : ℝ) : ℂ) ∈ ratioSet ↔
      ∃ lam : ℂ, lam ≠ 0 ∧
        J0 (Complex.I * lam * (r₁ : ℂ)) = 1 ∧
        J0 (Complex.I * lam * (r₂ : ℂ)) = 1 := by
  have hr₁C : (r₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₁.ne'
  have hr₂C : (r₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₂.ne'
  constructor
  · rintro ⟨α, hα, β, hβ, hquot⟩
    have hquot' : α / β = (r₁ : ℂ) / (r₂ : ℂ) := by
      simpa only [Complex.ofReal_div] using hquot
    have hcross : α * (r₂ : ℂ) = (r₁ : ℂ) * β :=
      (div_eq_div_iff hβ.1 hr₂C).mp hquot'
    have hcancel : Complex.I * (α / (Complex.I * (r₁ : ℂ))) = α / (r₁ : ℂ) := by
      rw [← mul_div_assoc, mul_div_mul_left _ _ Complex.I_ne_zero]
    refine ⟨α / (Complex.I * (r₁ : ℂ)),
      div_ne_zero hα.1 (mul_ne_zero Complex.I_ne_zero hr₁C), ?_, ?_⟩
    · have heq : Complex.I * (α / (Complex.I * (r₁ : ℂ))) * (r₁ : ℂ) = α := by
        rw [hcancel, div_mul_cancel₀ _ hr₁C]
      rw [heq]
      exact hα.2
    · have heq : Complex.I * (α / (Complex.I * (r₁ : ℂ))) * (r₂ : ℂ) = β := by
        rw [hcancel, div_mul_eq_mul_div, hcross, mul_div_cancel_left₀ _ hr₁C]
      rw [heq]
      exact hβ.2
  · rintro ⟨lam, hlam, h₁, h₂⟩
    refine ⟨Complex.I * lam * (r₁ : ℂ), ⟨?_, h₁⟩,
      Complex.I * lam * (r₂ : ℂ), ⟨?_, h₂⟩, ?_⟩
    · exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hlam) hr₁C
    · exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hlam) hr₂C
    · rw [Complex.ofReal_div]
      exact mul_div_mul_left _ _ (mul_ne_zero Complex.I_ne_zero hlam)

end J0RadialUniqueness
