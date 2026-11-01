import Solutions.J0RadialUniqueness.LocalResolventQuotient
import Solutions.J0RadialUniqueness.SpectralSectorLowerBounds

/-! Actual order-one growth of the filled local quotient in the outer sectors.

The denominator gap is the proved Bessel gap. Large parameters are controlled
through the actual resolvent factorization and actual convolution growth.
The remaining compact parameter disk is bounded using the already proved
entire filled quotient. No quotient-growth hypothesis is introduced.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem outer_sector_positive_real_scale {r : ℝ} (hr : 0 < r) {lam : ℂ}
    (hsector : |lam.re| ≤ |lam.im|) :
    |((r : ℂ) * lam).re| ≤ |((r : ℂ) * lam).im| := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, abs_mul, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left hsector hr.le

/-- The filled actual local quotient has order-one growth throughout both closed
outer sectors. The compact part includes all apparent poles and parameter zero. -/
theorem localResolventQuotient_outer_exp_bound {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ lam : ℂ,
      |lam.re| ≤ |lam.im| → 1 ≤ ‖lam‖ →
      ‖localResolventQuotient r₁ u x lam‖ ≤ A * Real.exp (B * ‖lam‖) := by
  obtain ⟨ε, hε, hgap⟩ := J0_uniform_defect_gap_outside_principal
  obtain ⟨C, hC, haction⟩ := planarResolventTConvolution_uniform_exp_bound hr₁ hu.continuous x
  have hqcont : Continuous (localResolventQuotient r₁ u x) :=
    (localResolventQuotient_differentiable hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx).continuous
  let D : ℝ := max 1 (2 / r₁)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) D).exists_bound_of_continuousOn hqcont.continuousOn
  let A : ℝ := 1 + |K| + C / ε
  let B : ℝ := 2 * r₁ + 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A, hA, B, hB, ?_⟩
  intro lam hsector _hnorm
  by_cases hlarge : D ≤ ‖lam‖
  · have htwo : 2 / r₁ ≤ ‖lam‖ := (le_max_right _ _).trans hlarge
    have hrlam : 2 ≤ r₁ * ‖lam‖ := by
      have hh := (div_le_iff₀ hr₁).mp htwo
      nlinarith
    have hscaled : 2 ≤ ‖(r₁ : ℂ) * lam‖ := by
      rw [norm_mul, Complex.norm_of_nonneg hr₁.le]
      exact hrlam
    have hdefect : ε ≤ ‖1 - J0 ((r₁ : ℂ) * lam)‖ :=
      hgap _ (outer_sector_positive_real_scale hr₁ hsector) hscaled
    have hmassnorm : ‖lam‖ ^ 2 * ‖helmholtzResolventMass r₁ lam‖ =
        ‖1 - J0 ((r₁ : ℂ) * lam)‖ := by
      simpa only [norm_mul, norm_pow] using
        congrArg norm (helmholtzResolventMass_mul_parameter_sq r₁ lam)
    have hgapmul : ε ≤ ‖lam‖ ^ 2 * ‖helmholtzResolventMass r₁ lam‖ := by
      rw [hmassnorm]
      exact hdefect
    have hmassne : helmholtzResolventMass r₁ lam ≠ 0 := by
      intro hz
      rw [hz, norm_zero, mul_zero] at hgapmul
      linarith
    have hordinary : localResolventQuotient r₁ u x lam =
        planarResolventTConvolution r₁ u x lam / helmholtzResolventMass r₁ lam :=
      localResolventQuotient_eq_div r₁ u x hmassne
    have hfactor : ‖planarResolventTConvolution r₁ u x lam‖ =
        ‖helmholtzResolventMass r₁ lam‖ * ‖localResolventQuotient r₁ u x lam‖ := by
      simpa only [norm_mul] using congrArg norm
        (localResolventQuotient_factorization hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx lam)
    have hqprod : ε * ‖localResolventQuotient r₁ u x lam‖ ≤
        ‖lam‖ ^ 2 * (C * Real.exp (2 * r₁ * ‖lam‖)) := by
      calc
        _ ≤ (‖lam‖ ^ 2 * ‖helmholtzResolventMass r₁ lam‖) *
            ‖localResolventQuotient r₁ u x lam‖ :=
          mul_le_mul_of_nonneg_right hgapmul (norm_nonneg _)
        _ = ‖lam‖ ^ 2 * ‖planarResolventTConvolution r₁ u x lam‖ := by
          rw [hfactor]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (haction lam) (sq_nonneg _)
    have hqnorm : ‖localResolventQuotient r₁ u x lam‖ ≤
        (C / ε) * (‖lam‖ ^ 2 * Real.exp (2 * r₁ * ‖lam‖)) := by
      have hh : ‖localResolventQuotient r₁ u x lam‖ ≤
          (‖lam‖ ^ 2 * (C * Real.exp (2 * r₁ * ‖lam‖))) / ε :=
        (le_div_iff₀ hε).mpr (by nlinarith only [hqprod])
      calc
        _ ≤ _ := hh
        _ = _ := by ring
    have hLexp : ‖lam‖ ≤ Real.exp ‖lam‖ := by
      linarith only [Real.add_one_le_exp ‖lam‖]
    have hsq : ‖lam‖ ^ 2 ≤ (Real.exp ‖lam‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg lam) (Real.exp_pos _).le).mpr hLexp
    have hexp : (Real.exp ‖lam‖) ^ 2 * Real.exp (2 * r₁ * ‖lam‖) =
        Real.exp (B * ‖lam‖) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [B]
      ring
    calc
      _ ≤ (C / ε) * (‖lam‖ ^ 2 * Real.exp (2 * r₁ * ‖lam‖)) := hqnorm
      _ ≤ (C / ε) * ((Real.exp ‖lam‖) ^ 2 * Real.exp (2 * r₁ * ‖lam‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le) (by positivity)
      _ = (C / ε) * Real.exp (B * ‖lam‖) := by rw [hexp]
      _ ≤ A * Real.exp (B * ‖lam‖) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        dsimp [A]
        linarith [abs_nonneg K]
  · have hball : lam ∈ Metric.closedBall (0 : ℂ) D := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_not_ge hlarge).le
    have hexp : 1 ≤ Real.exp (B * ‖lam‖) :=
      Real.one_le_exp (mul_nonneg hB (norm_nonneg lam))
    calc
      _ ≤ K := hK lam hball
      _ ≤ A := by
        dsimp [A]
        linarith [le_abs_self K, div_nonneg hC.le hε.le]
      _ ≤ A * Real.exp (B * ‖lam‖) := by
        nlinarith only [mul_le_mul_of_nonneg_left hexp hA.le]

/-- The explicit unit rotation which takes the first quadrant to the upper
closed outer sector, with no branch or argument conversion required. -/
def outerQuadrantRotation : ℂ := Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_outerQuadrantRotation : ‖outerQuadrantRotation‖ = 1 := by
  simp [outerQuadrantRotation, Complex.norm_exp]

theorem outerQuadrantRotation_re : outerQuadrantRotation.re = Real.sqrt 2 / 2 := by
  unfold outerQuadrantRotation
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]

theorem outerQuadrantRotation_im : outerQuadrantRotation.im = Real.sqrt 2 / 2 := by
  unfold outerQuadrantRotation
  rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four]

theorem outerQuadrantRotation_mem_outer_sector {w : ℂ}
    (hre : 0 ≤ w.re) (him : 0 ≤ w.im) :
    |(outerQuadrantRotation * w).re| ≤ |(outerQuadrantRotation * w).im| := by
  let c : ℝ := Real.sqrt 2 / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hr : (outerQuadrantRotation * w).re = c * (w.re - w.im) := by
    rw [Complex.mul_re, outerQuadrantRotation_re, outerQuadrantRotation_im]
    dsimp [c]
    ring
  have hi : (outerQuadrantRotation * w).im = c * (w.re + w.im) := by
    rw [Complex.mul_im, outerQuadrantRotation_re, outerQuadrantRotation_im]
    dsimp [c]
    ring
  rw [hr, hi]
  calc
    |c * (w.re - w.im)| = c * |w.re - w.im| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ c * (w.re + w.im) :=
      mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hc
    _ = |c * (w.re + w.im)| := (abs_of_nonneg (mul_nonneg hc (add_nonneg hre him))).symm

theorem localResolventQuotient_rotated_quadrant_exp_bound {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {R r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ,
      0 < w.re → 0 < w.im → 1 ≤ ‖w‖ →
      ‖localResolventQuotient r₁ u x (outerQuadrantRotation * w)‖ ≤ A * Real.exp (B * ‖w‖) := by
  obtain ⟨A, hA, B, hB, hgrowth⟩ :=
    localResolventQuotient_outer_exp_bound hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx
  refine ⟨A, hA, B, hB, ?_⟩
  intro w hre him hn
  have hnorm : ‖outerQuadrantRotation * w‖ = ‖w‖ := by
    rw [norm_mul, norm_outerQuadrantRotation, one_mul]
  have hh := hgrowth (outerQuadrantRotation * w)
    (outerQuadrantRotation_mem_outer_sector hre.le him.le) (by rwa [hnorm])
  simpa only [hnorm] using hh

end J0RadialUniqueness
