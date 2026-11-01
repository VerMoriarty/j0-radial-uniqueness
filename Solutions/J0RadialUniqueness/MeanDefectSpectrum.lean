import Solutions.J0RadialUniqueness.SpectralKernel
import Solutions.J0RadialUniqueness.BesselExponentialType
import Solutions.J0RadialUniqueness.QAnalytic

noncomputable section

namespace J0RadialUniqueness

theorem meanDefectMultiplier_analyticAt (r : ℝ) (ζ : ℂ) :
    AnalyticAt ℂ (meanDefectMultiplier r) ζ := by
  have hp : AnalyticAt ℂ (fun z : ℂ => -((r : ℂ) * z) ^ 2 / 4) ζ := by fun_prop
  exact analyticAt_const.mul ((Q_analyticAt _).comp hp)

theorem meanDefectMultiplier_norm_bound (r : ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    ‖meanDefectMultiplier r ζ‖ ≤
      (Real.exp (|r| * |ζ.im|) + 1) / ‖ζ‖ ^ 2 := by
  have h := J0_sub_one_eq_sq_mul_meanDefectMultiplier r ζ
  have hn := norm_sourceEta_le_exp_abs_im_add_one ((r : ℂ) * ζ)
  rw [norm_sub_rev, h, norm_mul, norm_pow] at hn
  have him : |((r : ℂ) * ζ).im| = |r| * |ζ.im| := by simp [abs_mul]
  rw [him] at hn
  exact (le_div_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hζ))).mpr (by
    simpa only [mul_comm] using hn)

/-- The actual normalized compact-kernel spectra have no common zero for
distinct positive radii. The origin is handled by its nonzero extended value. -/
theorem meanDefectMultipliers_no_common_zero {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hne : r₁ ≠ r₂) (ζ : ℂ) :
    meanDefectMultiplier r₁ ζ ≠ 0 ∨ meanDefectMultiplier r₂ ζ ≠ 0 := by
  by_cases hz : ζ = 0
  · left
    rw [hz]
    exact meanDefectMultiplier_zero_ne_zero_of_pos r₁ hr₁
  · by_cases h₁ : meanDefectMultiplier r₁ ζ = 0
    · right
      intro h₂
      exact hne (paper_5_3 ζ hz r₁ r₂ hr₁ hr₂
        ((meanDefectMultiplier_eq_zero_iff r₁ ζ hz).mp h₁)
        ((meanDefectMultiplier_eq_zero_iff r₂ ζ hz).mp h₂))
    · exact Or.inl h₁

theorem sourceEta_quadratic_factor (ζ : ℂ) :
    sourceEta ζ = ζ ^ 2 * ((1 / 4 : ℂ) * Q (-ζ ^ 2 / 4)) := by
  have h := F_sub_one (-ζ ^ 2 / 4)
  change 1 - F (-ζ ^ 2 / 4) = _
  linear_combination -h

theorem sourceEta_hasDerivAt (ζ : ℂ) :
    HasDerivAt sourceEta (-deriv J0 ζ) ζ :=
  (J0_differentiable ζ).hasDerivAt.const_sub 1

theorem sourceEta_deriv_ne_zero_at_nonzero_root {ζ : ℂ}
    (hζ : ζ ≠ 0) (hroot : sourceEta ζ = 0) : deriv sourceEta ζ ≠ 0 := by
  rw [(sourceEta_hasDerivAt ζ).deriv]
  exact neg_ne_zero.mpr (J0_deriv_ne_zero_at_one_point hζ ((sourceEta_eq_zero_iff ζ).mp hroot))

end J0RadialUniqueness
