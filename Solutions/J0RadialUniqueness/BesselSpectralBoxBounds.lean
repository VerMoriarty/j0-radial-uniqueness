import Solutions.J0RadialUniqueness.SpectralSectorLowerBounds
import Solutions.J0RadialUniqueness.SpectralZeroStrip
import Solutions.J0RadialUniqueness.BesselExponentialType
import Mathlib.Tactic

/-! Explicit spectral boxes for the actual Bessel mean defect.
The vertical edges use the proved principal-branch amplitude estimate.
The horizontal edges use radial energy monotonicity of the actual F series
and its uniform modulus gap. No spectral avoidance hypothesis is imposed. -/

noncomputable section

open Set

namespace J0RadialUniqueness

def besselSpectralBoxRadius (n : ℕ) : ℝ :=
  2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4

/-- The four actual sides of the centered square of radius N. -/
def besselSpectralBoxBoundary (n : ℕ) : Set ℂ :=
  {z | (|z.re| = besselSpectralBoxRadius n ∧ |z.im| ≤ besselSpectralBoxRadius n) ∨
    (|z.im| = besselSpectralBoxRadius n ∧ |z.re| ≤ besselSpectralBoxRadius n)}

theorem besselSpectralBoxRadius_pos (n : ℕ) : 0 < besselSpectralBoxRadius n := by
  unfold besselSpectralBoxRadius
  positivity

theorem besselSpectralBoxRadius_ge {n : ℕ} (hn : 100 ≤ n) :
    (256 : ℝ) ≤ besselSpectralBoxRadius n := by
  have hnR : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  unfold besselSpectralBoxRadius
  nlinarith [Real.pi_pos]

theorem besselSpectralBoxBoundary_norm_ge {n : ℕ} {z : ℂ}
    (hz : z ∈ besselSpectralBoxBoundary n) : besselSpectralBoxRadius n ≤ ‖z‖ := by
  rcases hz with hz | hz
  · simpa only [hz.1] using Complex.abs_re_le_norm z
  · simpa only [hz.1] using Complex.abs_im_le_norm z

theorem norm_J0_sub_one_quadrantRep (z : ℂ) :
    ‖J0 (quadrantRep z) - 1‖ = ‖J0 z - 1‖ := by
  rcases quadrantRep_orbit z with h | h | h | h
  · rw [h]
  · rw [h, J0_neg]
  · rw [h, J0_conj, ← map_one (starRingEnd ℂ), ← map_sub, RCLike.norm_conj]
    simp only [map_one]
  · rw [h, J0_neg, J0_conj, ← map_one (starRingEnd ℂ), ← map_sub, RCLike.norm_conj]
    simp only [map_one]

/-- In the outer sectors, radial shrinking cannot increase the actual Bessel
modulus. This is a consequence of the proved F energy identity. -/
theorem norm_J0_scale_le_outside_principal {z : ℂ}
    (hsector : |z.re| ≤ |z.im|) (hz : z ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖J0 ((t : ℂ) * z)‖ ≤ ‖J0 z‖ := by
  let w : ℂ := -z ^ 2 / 4
  have hsq : z.re ^ 2 ≤ z.im ^ 2 := by
    nlinarith only [sq_abs z.re, sq_abs z.im,
      mul_self_le_mul_self (abs_nonneg z.re) hsector]
  have hwre : 0 ≤ w.re := by
    dsimp only [w]
    simp only [Complex.div_ofNat_re, Complex.neg_re, pow_two, Complex.mul_re]
    linarith
  have hw : w ≠ 0 := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hz)) (by norm_num)
  have hmono := (FRayNormSq_strictMonoOn_of_ode F_ode_statement w hw hwre).monotoneOn
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hh := hmono (show t ^ 2 ∈ Ici (0 : ℝ) from sq_nonneg t)
    (show (1 : ℝ) ∈ Ici 0 by norm_num) ht2
  have hFnorm : ‖F (((t ^ 2 : ℝ) : ℂ) * w)‖ ≤ ‖F w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [FRayNormSq, FRay, Complex.ofReal_one, one_mul] using hh
  have harg : -((t : ℂ) * z) ^ 2 / 4 = ((t ^ 2 : ℝ) : ℂ) * w := by
    dsimp only [w]
    push_cast
    ring
  change ‖F (-((t : ℂ) * z) ^ 2 / 4)‖ ≤ ‖F w‖
  rw [harg]
  exact hFnorm

/-- One uniform constant bounds the regular-mode/mean-defect quotient on
the entire exterior of the two outer sectors. -/
theorem exists_bessel_outer_sector_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.re| ≤ |z.im| → 2 ≤ ‖z‖ →
      J0 z ≠ 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖J0 ((t : ℂ) * z) / (J0 z - 1)‖ ≤ C := by
  obtain ⟨ε, hε, hgap⟩ := F_uniform_norm_gap
  refine ⟨(1 + ε) / ε, by positivity, ?_⟩
  intro z hsector hnorm
  have hz : z ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖z‖)
  have hsq : z.re ^ 2 ≤ z.im ^ 2 := by
    nlinarith only [sq_abs z.re, sq_abs z.im,
      mul_self_le_mul_self (abs_nonneg z.re) hsector]
  have hwre : 0 ≤ (-z ^ 2 / 4).re := by
    simp only [Complex.div_ofNat_re, Complex.neg_re, pow_two, Complex.mul_re]
    linarith
  have hwnorm : 1 ≤ ‖-z ^ 2 / 4‖ := by
    simp only [norm_div, norm_neg, norm_pow, Complex.norm_ofNat]
    nlinarith [norm_nonneg z]
  have hJ : 1 + ε ≤ ‖J0 z‖ := hgap (-z ^ 2 / 4) hwre hwnorm
  have hd : ε ≤ ‖J0 z - 1‖ := by
    have hh := norm_sub_norm_le (J0 z) (1 : ℂ)
    simp only [norm_one] at hh
    linarith
  have hdpos : 0 < ‖J0 z - 1‖ := hε.trans_le hd
  refine ⟨fun h => (ne_of_gt hdpos) (by simp only [h, sub_self, norm_zero]), ?_⟩
  intro t ht
  have hsmall := norm_J0_scale_le_outside_principal hsector hz ht
  have hupper : ‖J0 ((t : ℂ) * z)‖ ≤ ‖J0 z - 1‖ + 1 := by
    have hh := norm_sub_norm_le (J0 z) (1 : ℂ)
    simp only [norm_one] at hh
    linarith
  have hprod : ε * ‖J0 ((t : ℂ) * z)‖ ≤ (1 + ε) * ‖J0 z - 1‖ := by
    have hh := mul_le_mul_of_nonneg_left hupper hε.le
    nlinarith
  rw [norm_div]
  apply (div_le_iff₀ hdpos).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hε).mpr
  nlinarith

/-- The actual vertical lines give a square-root quotient bound uniformly in
the radial parameter, including both endpoints t=0 and t=1. -/
theorem bessel_vertical_ratio_bound {z : ℂ} (hz : ClosedPrincipalSector z)
    {n : ℕ} (hn : 100 ≤ n) (hline : z.re = besselSpectralBoxRadius n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    J0 z ≠ 1 ∧ ‖J0 ((t : ℂ) * z) / (J0 z - 1)‖ ≤
      4 * Real.sqrt (2 * Real.pi * ‖z‖) := by
  have hden := spectral_vertical_bound_of_index_ge_hundred hz hn hline
  rw [norm_sub_rev (1 : ℂ) (J0 z)] at hden
  have hznorm : 0 < ‖z‖ := hz.2.2.trans_le (Complex.re_le_norm z)
  have hD : 0 < Real.sqrt (2 * Real.pi * ‖z‖) := by positivity
  have hdpos : 0 < ‖J0 z - 1‖ := lt_of_lt_of_le (by positivity) hden
  refine ⟨fun h => (ne_of_gt hdpos) (by simp only [h, sub_self, norm_zero]), ?_⟩
  have hnum : ‖J0 ((t : ℂ) * z)‖ ≤ Real.exp z.im := by
    have hh := norm_J0_le_exp_abs_im ((t : ℂ) * z)
    have him : |((t : ℂ) * z).im| = t * z.im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact abs_of_nonneg (mul_nonneg ht.1 hz.1)
    rw [him] at hh
    exact hh.trans (Real.exp_le_exp.mpr (by nlinarith [ht.2, hz.1]))
  have hEd : Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖) ≤ 4 * ‖J0 z - 1‖ := by
    linarith
  have hE := (div_le_iff₀ hD).mp hEd
  rw [norm_div]
  apply (div_le_iff₀ hdpos).mpr
  nlinarith

/-- Reflection and conjugation transfer the vertical estimate to both actual
vertical sides of the square. -/
theorem bessel_vertical_sides_ratio_bound {n : ℕ} (hn : 100 ≤ n) {z : ℂ}
    (hre : |z.re| = besselSpectralBoxRadius n) (him : |z.im| ≤ besselSpectralBoxRadius n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    J0 z ≠ 1 ∧ ‖J0 ((t : ℂ) * z) / (J0 z - 1)‖ ≤
      4 * Real.sqrt (2 * Real.pi * ‖z‖) := by
  have hw : ClosedPrincipalSector (quadrantRep z) :=
    ⟨abs_nonneg _, by change |z.im| ≤ |z.re|; rwa [hre], by
      change 0 < |z.re|
      rw [hre]
      exact besselSpectralBoxRadius_pos n⟩
  have hline : (quadrantRep z).re = besselSpectralBoxRadius n := hre
  obtain ⟨hroot, hbound⟩ := bessel_vertical_ratio_bound hw hn hline ht
  refine ⟨fun hz => hroot (J0_quadrantRep z hz), ?_⟩
  simp only [norm_div, norm_J0_mul_quadrantRep t ht.1,
    norm_J0_sub_one_quadrantRep, norm_quadrantRep] at hbound
  simpa only [norm_div] using hbound

/-- A single actual constant controls all four unbounded square sides and
proves that no one-point lies on any of these boundaries. -/
theorem exists_bessel_spectral_box_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 100 ≤ n → ∀ z ∈ besselSpectralBoxBoundary n,
      J0 z ≠ 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ‖J0 ((t : ℂ) * z) / (J0 z - 1)‖ ≤ C * Real.sqrt (1 + ‖z‖) := by
  obtain ⟨C₀, hC₀, houter⟩ := exists_bessel_outer_sector_ratio_bound
  let C : ℝ := max C₀ (4 * Real.sqrt (2 * Real.pi))
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n hn z hz
  have hnorm : (256 : ℝ) ≤ ‖z‖ :=
    (besselSpectralBoxRadius_ge hn).trans (besselSpectralBoxBoundary_norm_ge hz)
  have hsqrt : 1 ≤ Real.sqrt (1 + ‖z‖) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [norm_nonneg z]
  rcases hz with hz | hz
  · have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
      bessel_vertical_sides_ratio_bound hn hz.1 hz.2 ht
    refine ⟨(hb 0 ⟨le_rfl, by norm_num⟩).1, ?_⟩
    intro t ht
    calc
      _ ≤ 4 * Real.sqrt (2 * Real.pi * ‖z‖) := (hb t ht).2
      _ = (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt ‖z‖ := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
        ring
      _ ≤ C * Real.sqrt (1 + ‖z‖) := by
        apply mul_le_mul (le_max_right _ _) (Real.sqrt_le_sqrt (by linarith))
          (Real.sqrt_nonneg _) hC.le
  · have hsector : |z.re| ≤ |z.im| := by rw [hz.1]; exact hz.2
    obtain ⟨hroot, hb⟩ := houter z hsector (by linarith)
    refine ⟨hroot, ?_⟩
    intro t ht
    calc
      _ ≤ C₀ := hb t ht
      _ ≤ C := le_max_left _ _
      _ ≤ C * Real.sqrt (1 + ‖z‖) := by nlinarith

end J0RadialUniqueness
