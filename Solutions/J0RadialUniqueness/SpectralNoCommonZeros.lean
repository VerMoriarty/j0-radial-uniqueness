import Solutions.J0RadialUniqueness.MeanDefectSpectrum
import Solutions.J0RadialUniqueness.CompactHelmholtzResolvent
import Solutions.J0RadialUniqueness.SimpleZeroDivision

/-! The exact no-common-zero input for the cited local theorem.
The hypothesis is the paper's root-ratio exclusion itself; distinctness of the
radii is not imposed, and existence of a nonzero Bessel one-point is not assumed.
The removable value at spectral parameter zero is handled separately. -/

noncomputable section

namespace J0RadialUniqueness

theorem meanDefectMultipliers_no_common_zero_of_ratio_exclusion {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hratio : ((r₁ / r₂ : ℝ) : ℂ) ∉ ratioSet) (ζ : ℂ) :
    meanDefectMultiplier r₁ ζ ≠ 0 ∨ meanDefectMultiplier r₂ ζ ≠ 0 := by
  by_cases hζ : ζ = 0
  · left
    rw [hζ]
    exact meanDefectMultiplier_zero_ne_zero_of_pos r₁ hr₁
  by_cases h₁ : meanDefectMultiplier r₁ ζ = 0
  · right
    intro h₂
    apply hratio
    have hr₁C : (r₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₁.ne'
    have hr₂C : (r₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₂.ne'
    refine ⟨(r₁ : ℂ) * ζ, ⟨mul_ne_zero hr₁C hζ,
      (meanDefectMultiplier_eq_zero_iff r₁ ζ hζ).mp h₁⟩,
      (r₂ : ℂ) * ζ, ⟨mul_ne_zero hr₂C hζ,
        (meanDefectMultiplier_eq_zero_iff r₂ ζ hζ).mp h₂⟩, ?_⟩
    rw [Complex.ofReal_div]
    field_simp [hr₂C, hζ]
  · exact Or.inl h₁

theorem helmholtzResolventMass_eq_neg_meanDefectMultiplier (r : ℝ) (ζ : ℂ) :
    helmholtzResolventMass r ζ = -meanDefectMultiplier r ζ := by
  unfold helmholtzResolventMass helmholtzResolventArg meanDefectMultiplier
  congr 1
  ring

theorem helmholtzResolventMasses_no_common_zero_of_ratio_exclusion {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hratio : ((r₁ / r₂ : ℝ) : ℂ) ∉ ratioSet) (ζ : ℂ) :
    helmholtzResolventMass r₁ ζ ≠ 0 ∨ helmholtzResolventMass r₂ ζ ≠ 0 := by
  simpa only [helmholtzResolventMass_eq_neg_meanDefectMultiplier, neg_ne_zero] using
    meanDefectMultipliers_no_common_zero_of_ratio_exclusion hr₁ hr₂ hratio ζ

theorem helmholtzResolventMass_deriv_ne_zero_at_root {r : ℝ} (hr : 0 < r)
    {ζ : ℂ} (hroot : helmholtzResolventMass r ζ = 0) :
    deriv (helmholtzResolventMass r) ζ ≠ 0 := by
  have he : helmholtzResolventMass r = -meanDefectMultiplier r :=
    funext (helmholtzResolventMass_eq_neg_meanDefectMultiplier r)
  have hmean : meanDefectMultiplier r ζ = 0 := by
    rw [helmholtzResolventMass_eq_neg_meanDefectMultiplier, neg_eq_zero] at hroot
    exact hroot
  rw [he, deriv.neg]
  exact neg_ne_zero.mpr (meanDefectMultiplier_deriv_ne_zero_at_root hr hmean)

end J0RadialUniqueness
