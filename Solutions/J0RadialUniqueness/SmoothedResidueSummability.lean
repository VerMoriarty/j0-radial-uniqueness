import Solutions.J0RadialUniqueness.SpectralSmoothingMultiplier
import Solutions.J0RadialUniqueness.RootExponentialSeriesSmooth

/-! Actual smoothing turns the residue coefficients into rapidly summable
coefficients. The finite-order smooth-series theorem consequently gives a
genuine global C∞ cosine series, while preserving any fixed coefficient whose
specified actual multiplier is nonzero. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

namespace J0RadialUniqueness

def smoothedBesselResidueCoefficient (M : ℕ) (τ : ℝ) (ψ : Plane → ℝ) (z : ℂ) : ℂ :=
  scaledBesselResidueCoefficient M τ z * spectralSmoothingMultiplier ψ z

theorem smoothedBesselResidueCoefficient_weight_summable (M : ℕ) (hM : 1 ≤ M)
    {τ : ℝ} (hτ : 1 < τ) {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {η : ℝ} (hη : 0 ≤ η)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η) (b : ℝ) :
    Summable (fun z : onePoints =>
      ‖smoothedBesselResidueCoefficient M τ ψ z‖ * ‖(z : ℂ)‖ ^ b) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (b + η + 1)
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hβ : b + η - (2 * k : ℕ) < 2 * M - 1 := by push_cast; nlinarith
  obtain ⟨C, hC, hb⟩ := spectralSmoothingMultiplier_one_point_rapid_decay hψ hc hη hs k
  have hsum := (scaledBesselResidueCoefficient_weight_summable M hτ hβ).mul_left
    (C * (4 : ℝ) ^ η)
  apply Summable.of_nonneg_of_le
    (fun z => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)) _ hsum
  intro z
  have hρ : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.property.1
  rw [smoothedBesselResidueCoefficient, norm_mul]
  calc
    _ ≤ (‖scaledBesselResidueCoefficient M τ z‖ *
        (C * (4 : ℝ) ^ η * ‖(z : ℂ)‖ ^ (η - (2 * k : ℕ)))) * ‖(z : ℂ)‖ ^ b :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb z z.property.1 z.property.2) (norm_nonneg _))
        (Real.rpow_nonneg hρ.le _)
    _ = (C * (4 : ℝ) ^ η) *
        (‖scaledBesselResidueCoefficient M τ z‖ * ‖(z : ℂ)‖ ^ (b + η - (2 * k : ℕ))) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hρ]
      have he : η - (2 * k : ℕ) + b = b + η - (2 * k : ℕ) := by ring
      rw [he]
      ring

def smoothedBesselCosineSeries (M : ℕ) (τ : ℝ) (ψ : Plane → ℝ) : ℝ → ℂ :=
  rootCosineSeries (fun z : RightOnePoint => smoothedBesselResidueCoefficient M τ ψ z)

theorem smoothedBesselCosineSeries_contDiffOn (M n : ℕ) (hM : 1 ≤ M)
    {τ : ℝ} (hτ : 1 < τ) {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {η : ℝ} (hη : 0 ≤ η)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η) {T : ℝ} (hT : 0 < T) :
    ContDiffOn ℝ (n : ℕ∞ω) (smoothedBesselCosineSeries M τ ψ) (Ioo (-T) T) := by
  apply rootCosineSeries_contDiffOn _ hT n
  intro j _
  exact (smoothedBesselResidueCoefficient_weight_summable M hM hτ hψ hc hη hs
    (T + j)).subtype (fun z : onePoints => 0 < (z : ℂ).re)

theorem smoothedBesselCosineSeries_contDiff (M : ℕ) (hM : 1 ≤ M)
    {τ : ℝ} (hτ : 1 < τ) {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {η : ℝ} (hη : 0 ≤ η)
    (hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η) :
    ContDiff ℝ ∞ (smoothedBesselCosineSeries M τ ψ) := by
  apply contDiff_infty.mpr
  intro n
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hT : 0 < |x| + 1 := by positivity
  have hsm := smoothedBesselCosineSeries_contDiffOn M n hM hτ hψ hc hη hs hT
  exact hsm.contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp (by linarith : |x| < |x| + 1)))

theorem smoothedBesselResidueCoefficient_ne_zero (M : ℕ) {τ : ℝ} (hτ : 1 < τ)
    {ψ : Plane → ℝ} {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1)
    (hγ : spectralSmoothingMultiplier ψ z ≠ 0) :
    smoothedBesselResidueCoefficient M τ ψ z ≠ 0 := by
  apply mul_ne_zero _ hγ
  apply div_ne_zero (besselResidueCoefficient_ne_zero M hz hJ)
  have hh := scaled_one_point_defect_ne_zero hτ hz hJ
  intro he
  exact hh (by rw [sub_eq_zero.mp he, sub_self])

end J0RadialUniqueness
