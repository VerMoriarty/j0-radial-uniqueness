import Solutions.J0RadialUniqueness.CompactComplexConvolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Exchange of two actual compact L1 complex kernels. A product L1 majorant
and a compact bound for the continuous right factor justify the Fubini step.
The local congruence and support statements keep the exact sum of radii. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Convolution

namespace J0RadialUniqueness

theorem complexConvolution_iterated_integrand_integrable
    {k₁ k₂ u : Plane → ℂ} (hk₁ : Integrable k₁) (hk₂ : Integrable k₂)
    {r₁ r₂ : ℝ}
    (hs₁ : ∀ y : Plane, k₁ y ≠ 0 → ‖y‖ ≤ r₁)
    (hs₂ : ∀ y : Plane, k₂ y ≠ 0 → ‖y‖ ≤ r₂)
    (hu : Continuous u) (x : Plane) :
    Integrable (fun p : Plane × Plane => (k₁ p.1 * k₂ p.2) * u (x - p.1 - p.2))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (r₁ + r₂)).exists_bound_of_continuousOn hu.continuousOn
  have hbase : Integrable (fun p : Plane × Plane => (‖k₁ p.1‖ * ‖k₂ p.2‖) * C)
      (volume.prod volume) := (hk₁.norm.mul_prod hk₂.norm).mul_const C
  have hm : AEStronglyMeasurable
      (fun p : Plane × Plane => (k₁ p.1 * k₂ p.2) * u (x - p.1 - p.2)) (volume.prod volume) :=
    ((hk₁.aestronglyMeasurable.comp_fst).mul (hk₂.aestronglyMeasurable.comp_snd)).mul
      (hu.comp (continuous_const.sub continuous_fst |>.sub continuous_snd)).aestronglyMeasurable
  apply hbase.mono' hm
  exact Filter.Eventually.of_forall (fun p => by
    by_cases h₁ : k₁ p.1 = 0
    · simp only [h₁, zero_mul, norm_zero, le_refl]
    by_cases h₂ : k₂ p.2 = 0
    · simp only [h₂, zero_mul, mul_zero, norm_zero, le_refl]
    have hy : x - p.1 - p.2 ∈ Metric.closedBall x (r₁ + r₂) := by
      rw [Metric.mem_closedBall, dist_eq_norm,
        show x - p.1 - p.2 - x = -(p.1 + p.2) by abel, norm_neg]
      exact (norm_add_le _ _).trans (add_le_add (hs₁ p.1 h₁) (hs₂ p.2 h₂))
    have hb := hC (x - p.1 - p.2) hy
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem complexConvolution_iterated_eq_double (k₁ k₂ u : Plane → ℂ) (x : Plane) :
    complexConvolution k₁ (complexConvolution k₂ u) x =
      ∫ s : Plane, ∫ t : Plane, (k₁ s * k₂ t) * u (x - s - t) := by
  simp only [complexConvolution_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by dsimp only; ring))

theorem complexConvolution_iterated_integrable_of_radius
    {k₁ k₂ u : Plane → ℂ} (hk₁ : Integrable k₁) (hk₂ : Integrable k₂)
    {r₁ r₂ : ℝ}
    (hs₁ : ∀ y : Plane, k₁ y ≠ 0 → ‖y‖ ≤ r₁)
    (hs₂ : ∀ y : Plane, k₂ y ≠ 0 → ‖y‖ ≤ r₂)
    (hu : Continuous u) (x : Plane) :
    Integrable (fun s : Plane => k₁ s * complexConvolution k₂ u (x - s)) := by
  have hh := (complexConvolution_iterated_integrand_integrable hk₁ hk₂ hs₁ hs₂ hu x).integral_prod_left
  have he : (fun s : Plane => k₁ s * complexConvolution k₂ u (x - s)) =
      (fun s : Plane => ∫ t : Plane, (k₁ s * k₂ t) * u (x - s - t)) := by
    funext s
    rw [complexConvolution_eq_integral, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by dsimp only; ring)
  rw [he]
  exact hh

/-- Two rough compact kernels commute on a continuous, possibly noncompact,
right factor. The proof explicitly supplies the double-integral L1 bound. -/
theorem complexConvolution_iterated_comm_of_radius
    {k₁ k₂ u : Plane → ℂ} (hk₁ : Integrable k₁) (hk₂ : Integrable k₂)
    {r₁ r₂ : ℝ}
    (hs₁ : ∀ y : Plane, k₁ y ≠ 0 → ‖y‖ ≤ r₁)
    (hs₂ : ∀ y : Plane, k₂ y ≠ 0 → ‖y‖ ≤ r₂)
    (hu : Continuous u) (x : Plane) :
    complexConvolution k₁ (complexConvolution k₂ u) x =
      complexConvolution k₂ (complexConvolution k₁ u) x := by
  have hi := complexConvolution_iterated_integrand_integrable hk₁ hk₂ hs₁ hs₂ hu x
  rw [complexConvolution_iterated_eq_double, complexConvolution_iterated_eq_double,
    integral_integral_swap hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by
      dsimp only
      rw [show x - s - t = x - t - s by abel]
      ring))

theorem complexConvolution_iterated_comm
    {k₁ k₂ u : Plane → ℂ} (hk₁ : Integrable k₁) (hk₂ : Integrable k₂)
    (hc₁ : HasCompactSupport k₁) (hc₂ : HasCompactSupport k₂)
    (hu : Continuous u) (x : Plane) :
    complexConvolution k₁ (complexConvolution k₂ u) x =
      complexConvolution k₂ (complexConvolution k₁ u) x := by
  obtain ⟨r₁, _, hs₁⟩ := hc₁.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
  obtain ⟨r₂, _, hs₂⟩ := hc₂.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
  apply complexConvolution_iterated_comm_of_radius hk₁ hk₂ (r₁ := r₁) (r₂ := r₂) _ _ hu x
  · intro y hy
    exact (show ‖y‖ < r₁ by
      simpa only [Metric.mem_ball, dist_zero_right] using hs₁ (subset_closure hy)).le
  · intro y hy
    exact (show ‖y‖ < r₂ by
      simpa only [Metric.mem_ball, dist_zero_right] using hs₂ (subset_closure hy)).le

/-- The sum of kernel radii controls the actual support, with no enlargement. -/
theorem complexConvolution_eq_zero_outside_sum {k₁ k₂ : Plane → ℂ} {r₁ r₂ : ℝ}
    (hs₁ : ∀ y : Plane, k₁ y ≠ 0 → ‖y‖ ≤ r₁)
    (hs₂ : ∀ y : Plane, k₂ y ≠ 0 → ‖y‖ ≤ r₂)
    {x : Plane} (hx : r₁ + r₂ < ‖x‖) : complexConvolution k₁ k₂ x = 0 := by
  rw [complexConvolution_eq_integral]
  have he : (fun y : Plane => k₁ y * k₂ (x - y)) = 0 := by
    funext y
    by_cases h₁ : k₁ y = 0
    · simp only [h₁, zero_mul, Pi.zero_apply]
    by_cases h₂ : k₂ (x - y) = 0
    · simp only [h₂, mul_zero, Pi.zero_apply]
    have hn : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      simpa only [add_sub_cancel] using norm_add_le y (x - y)
    have hbound := add_le_add (hs₁ y h₁) (hs₂ (x - y) h₂)
    exfalso
    linarith
  rw [he]
  exact integral_zero _ _

theorem complexConvolution_support_radius {k₁ k₂ : Plane → ℂ} {r₁ r₂ : ℝ}
    (hs₁ : ∀ y : Plane, k₁ y ≠ 0 → ‖y‖ ≤ r₁)
    (hs₂ : ∀ y : Plane, k₂ y ≠ 0 → ‖y‖ ≤ r₂)
    {x : Plane} (hx : complexConvolution k₁ k₂ x ≠ 0) : ‖x‖ ≤ r₁ + r₂ := by
  by_contra h
  exact hx (complexConvolution_eq_zero_outside_sum hs₁ hs₂ (lt_of_not_ge h))

theorem complexConvolution_hasCompactSupport {k₁ k₂ : Plane → ℂ}
    (hc₁ : HasCompactSupport k₁) (hc₂ : HasCompactSupport k₂) :
    HasCompactSupport (complexConvolution k₁ k₂) :=
  HasCompactSupport.convolution (L := complexMulPair) hc₁ hc₂

/-- Exact local dependence for two kernels: the required center margin is the
sum r₁+r₂, and no extension of u outside B_R enters the value. -/
theorem complexConvolution_iterated_congr_on_inner_ball
    {k₁ k₂ u v : Plane → ℂ} {r₁ r₂ R : ℝ}
    (hs₁ : ∀ y : Plane, k₁ y ≠ 0 → ‖y‖ ≤ r₁)
    (hs₂ : ∀ y : Plane, k₂ y ≠ 0 → ‖y‖ ≤ r₂)
    (huv : EqOn u v (planeBall R)) {x : Plane} (hx : x ∈ planeBall (R - r₁ - r₂)) :
    complexConvolution k₁ (complexConvolution k₂ u) x =
      complexConvolution k₁ (complexConvolution k₂ v) x := by
  rw [complexConvolution_iterated_eq_double, complexConvolution_iterated_eq_double]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    dsimp only
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only
      by_cases h₁ : k₁ s = 0
      · simp only [h₁, zero_mul]
      by_cases h₂ : k₂ t = 0
      · simp only [h₂, mul_zero, zero_mul]
      have hxnorm : ‖x‖ < R - r₁ - r₂ := by
        simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
      have hs := hs₁ s h₁
      have ht := hs₂ t h₂
      have hinside : x - s - t ∈ planeBall R := by
        rw [planeBall, Metric.mem_ball, dist_zero_right]
        calc
          ‖x - s - t‖ ≤ ‖x - s‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ (‖x‖ + ‖s‖) + ‖t‖ := add_le_add (norm_sub_le _ _) (le_refl _)
          _ < R := by linarith
      rw [huv hinside]))

end J0RadialUniqueness
