import Solutions.J0RadialUniqueness.BesselSpectralResidueExpansion
import Solutions.J0RadialUniqueness.SquareContourAlgebra

/-! Vanishing of the actual spectral-square boundary integrals. A coarser
integer-power majorant suffices: for every M≥1 the full contour is bounded by
24C/N, including the horizontal and vertical edges and their corner endpoints. -/

noncomputable section
open Set Filter
open scoped Topology

namespace J0RadialUniqueness

theorem squareBoundary_norm_le_twice {a : ℝ} {z : ℂ}
    (hz : z ∈ squareBoundarySet a) : ‖z‖ ≤ 2 * a := by
  have hb : |z.re| + |z.im| ≤ 2 * a := by
    rcases hz with ⟨hr, hi⟩ | ⟨hi, hr⟩ <;> linarith
  exact (Complex.norm_le_abs_re_add_abs_im z).trans hb

theorem besselSpectralBoxRadius_tendsto : Tendsto besselSpectralBoxRadius atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) _
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  intro n
  unfold besselSpectralBoxRadius
  nlinarith [Real.pi_gt_three, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem besselSpectralIntegrand_eq_ratio_div_power (M : ℕ) (t z : ℂ) :
    besselSpectralIntegrand M t z = (J0 (t * z) / (J0 z - 1)) / z ^ (2 * M + 1) := by
  unfold besselSpectralIntegrand
  rw [div_div]
  congr 1
  ring

theorem besselSpectralIntegrand_boundary_bound (M : ℕ) (hM : 1 ≤ M)
    {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 100 ≤ n)
    (hbound : ∀ z ∈ besselSpectralBoxBoundary n, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖J0 ((t : ℂ) * z) / (J0 z - 1)‖ ≤ C * Real.sqrt (1 + ‖z‖))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ besselSpectralBoxBoundary n) :
    ‖besselSpectralIntegrand M t z‖ ≤ 3 * C / (besselSpectralBoxRadius n) ^ 2 := by
  let N := besselSpectralBoxRadius n
  have hN : 0 < N := besselSpectralBoxRadius_pos n
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 256).trans (besselSpectralBoxRadius_ge hn)
  have hlow : N ≤ ‖z‖ := besselSpectralBoxBoundary_norm_ge hz
  have hhigh : ‖z‖ ≤ 2 * N := squareBoundary_norm_le_twice hz
  have hroot : Real.sqrt (1 + ‖z‖) ≤ 1 + ‖z‖ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [norm_nonneg z]⟩
  have hratio : ‖J0 ((t : ℂ) * z) / (J0 z - 1)‖ ≤ 3 * C * N := by
    have hh := (hbound z hz t ht).trans (mul_le_mul_of_nonneg_left hroot hC.le)
    nlinarith
  have hp : N ^ 3 ≤ ‖z‖ ^ (2 * M + 1) :=
    (pow_le_pow_left₀ hN.le hlow 3).trans
      (pow_le_pow_right₀ (hN1.trans hlow) (by omega : 3 ≤ 2 * M + 1))
  rw [besselSpectralIntegrand_eq_ratio_div_power, norm_div, norm_pow]
  calc
    _ ≤ (3 * C * N) / ‖z‖ ^ (2 * M + 1) :=
      div_le_div_of_nonneg_right hratio (by positivity)
    _ ≤ (3 * C * N) / N ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hN 3) hp
    _ = _ := by dsimp only [N]; field_simp [(besselSpectralBoxRadius_pos n).ne']

theorem besselSpectralContourIntegral_tendsto_zero (M : ℕ) (hM : 1 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => squareBoundaryIntegral (besselSpectralBoxRadius n)
      (besselSpectralIntegrand M t)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_bessel_spectral_box_ratio_bound
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖squareBoundaryIntegral (besselSpectralBoxRadius n) (besselSpectralIntegrand M t)‖ ≤
        24 * C / besselSpectralBoxRadius n := by
    filter_upwards [eventually_ge_atTop (100 : ℕ)] with n hn
    have hi := norm_squareBoundaryIntegral_le (besselSpectralBoxRadius_pos n).le
      (besselSpectralIntegrand M t)
      (fun z hz => besselSpectralIntegrand_boundary_bound M hM hC hn
        (fun z hz t ht => (hb n hn z hz).2 t ht) ht hz)
    have he : 8 * besselSpectralBoxRadius n * (3 * C / besselSpectralBoxRadius n ^ 2) =
        24 * C / besselSpectralBoxRadius n := by
      field_simp [(besselSpectralBoxRadius_pos n).ne']
      ring
    exact hi.trans_eq he
  exact squeeze_zero_norm' hbound (besselSpectralBoxRadius_tendsto.const_div_atTop (24 * C))

end J0RadialUniqueness
