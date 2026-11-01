import Solutions.J0RadialUniqueness.Main

/-! Uniform control of the actual second mean defect along a fixed dilation
of the nonzero Bessel one-point set. The input is the already proved global
radial escape theorem, including its actual localization and symmetry proofs. -/

noncomputable section

namespace J0RadialUniqueness

def scaledOnePointGap (τ : ℝ) : ℝ := Real.rpow τ (7 / 25 : ℝ) - 1

theorem scaledOnePointGap_pos {τ : ℝ} (hτ : 1 < τ) : 0 < scaledOnePointGap τ := by
  unfold scaledOnePointGap
  apply sub_pos.mpr
  simpa only [Real.rpow_eq_pow] using Real.one_lt_rpow hτ (by norm_num : (0 : ℝ) < 7 / 25)

/-- The same positive constant works for every actual nonzero one-point. -/
theorem scaled_one_point_defect_norm_gt {τ : ℝ} (hτ : 1 < τ)
    {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    scaledOnePointGap τ < ‖1 - J0 ((τ : ℂ) * z)‖ := by
  have he := paper_5_2 z hz hJ τ hτ
  have hr : ‖J0 ((τ : ℂ) * z)‖ - 1 ≤ ‖1 - J0 ((τ : ℂ) * z)‖ := by
    simpa only [norm_one, norm_sub_rev] using norm_sub_norm_le (J0 ((τ : ℂ) * z)) (1 : ℂ)
  unfold scaledOnePointGap
  linarith

theorem scaled_one_point_defect_ne_zero {τ : ℝ} (hτ : 1 < τ)
    {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    1 - J0 ((τ : ℂ) * z) ≠ 0 :=
  norm_pos_iff.mp ((scaledOnePointGap_pos hτ).trans (scaled_one_point_defect_norm_gt hτ hz hJ))

/-- The reciprocal of the second spectral defect is uniformly bounded over
the entire nonzero one-point set, rather than merely polynomially bounded. -/
theorem scaled_one_point_inverse_defect_norm_lt {τ : ℝ} (hτ : 1 < τ)
    {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    ‖(1 - J0 ((τ : ℂ) * z))⁻¹‖ < 1 / scaledOnePointGap τ := by
  rw [norm_inv, ← one_div ‖1 - J0 ((τ : ℂ) * z)‖]
  exact one_div_lt_one_div_of_lt (scaledOnePointGap_pos hτ)
    (scaled_one_point_defect_norm_gt hτ hz hJ)

theorem scaled_one_point_uniform_defect_lower_bound {τ : ℝ} (hτ : 1 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, z ≠ 0 → J0 z = 1 →
      c ≤ ‖1 - J0 ((τ : ℂ) * z)‖ := by
  exact ⟨scaledOnePointGap τ, scaledOnePointGap_pos hτ,
    fun _ hz hJ => (scaled_one_point_defect_norm_gt hτ hz hJ).le⟩

theorem scaled_one_point_uniform_inverse_defect_bound {τ : ℝ} (hτ : 1 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → J0 z = 1 →
      ‖(1 - J0 ((τ : ℂ) * z))⁻¹‖ ≤ C := by
  refine ⟨1 / scaledOnePointGap τ, one_div_pos.mpr (scaledOnePointGap_pos hτ), ?_⟩
  exact fun _ hz hJ => (scaled_one_point_inverse_defect_norm_lt hτ hz hJ).le

/-- The same estimate in the actual two-radius spectral parameterization. -/
theorem spectral_second_radius_defect_norm_gt {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₂)
    {lam : ℂ} (hlam : lam ≠ 0) (hJ : J0 (Complex.I * lam * (r₁ : ℂ)) = 1) :
    scaledOnePointGap (r₂ / r₁) < ‖1 - J0 (Complex.I * lam * (r₂ : ℂ))‖ := by
  have hτ : 1 < r₂ / r₁ := (lt_div_iff₀ hr₁).2 (by simpa only [one_mul] using hr)
  have hz : Complex.I * lam * (r₁ : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero hlam) (Complex.ofReal_ne_zero.mpr hr₁.ne')
  have hscale : (((r₂ / r₁ : ℝ) : ℂ)) * (Complex.I * lam * (r₁ : ℂ)) =
      Complex.I * lam * (r₂ : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr₁.ne'] <;> ring
  simpa only [hscale] using scaled_one_point_defect_norm_gt hτ hz hJ

end J0RadialUniqueness
