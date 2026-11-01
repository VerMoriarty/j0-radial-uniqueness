import Solutions.J0RadialUniqueness.BesselCentralPolynomial
import Solutions.J0RadialUniqueness.CircularMeanDomain

/-! Actual circular means of the convergent root cosine series.  The
summability hypothesis controls the genuine circle integrands uniformly in
the angle.  Dominated convergence therefore gives a HasSum statement for
their actual integrals.  The two residue-coefficient applications discharge
that hypothesis using the proved weighted summability theorem. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace J0RadialUniqueness

def rootCosinePlane (a : RightOnePoint → ℂ) (s : ℝ) (x : Plane) : ℂ :=
  rootCosineSeries a (x 0 / s)

theorem rootCosineSeries_norm_majorant (a : RightOnePoint → ℂ) {T t : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) (z : RightOnePoint) :
    ‖a z * Complex.cos ((z : ℂ) * (t : ℂ))‖ ≤
      (4 : ℝ) ^ T * (‖a z‖ * ‖(z : ℂ)‖ ^ T) := by
  have hh := norm_cos_one_point_real_mul_le z.val.property.1 z.val.property.2 hT ht
  rw [norm_mul]
  calc
    _ ≤ ‖a z‖ * ((4 : ℝ) ^ T * ‖(z : ℂ)‖ ^ T) :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by ring

theorem rootCosineSeries_summable (a : RightOnePoint → ℂ) {T t : ℝ}
    (hT : 0 ≤ T)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ T))
    (ht : |t| ≤ T) :
    Summable (fun z : RightOnePoint => a z * Complex.cos ((z : ℂ) * (t : ℂ))) := by
  exact Summable.of_norm_bounded (hw.mul_left ((4 : ℝ) ^ T))
    (rootCosineSeries_norm_majorant a hT ht)

theorem rootCosineSeries_continuousOn (a : RightOnePoint → ℂ) {T : ℝ}
    (hT : 0 ≤ T)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ T)) :
    ContinuousOn (rootCosineSeries a) (Icc (-T) T) := by
  apply continuousOn_tsum _ (hw.mul_left ((4 : ℝ) ^ T))
    (fun z t ht => rootCosineSeries_norm_majorant a hT (abs_le.mpr ht) z)
  intro z
  exact (by fun_prop : Continuous (fun t : ℝ =>
    a z * Complex.cos ((z : ℂ) * (t : ℂ)))).continuousOn

theorem coordinate_div_abs_lt_of_mem_ball {s T : ℝ} (hs : 0 < s)
    {x : Plane} (hx : x ∈ planeBall (s * T)) : |x 0 / s| < T := by
  have hxn : ‖x‖ < s * T := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
  have hc : |x 0| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  rw [abs_div, abs_of_pos hs]
  apply (div_lt_iff₀ hs).mpr
  nlinarith

theorem coordinate_div_abs_lt_on_natural_ball {s T r : ℝ} (hs : 0 < s)
    (hr : 0 ≤ r) {x : Plane} (hx : x ∈ planeBall (s * T - r)) :
    |x 0 / s| < T := by
  apply coordinate_div_abs_lt_of_mem_ball hs
  have hxn : ‖x‖ < s * T - r := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
  change dist x 0 < s * T
  rw [dist_zero_right]
  linarith

theorem continuous_circle_coordinate_div (x : Plane) (r s : ℝ) :
    Continuous (fun θ : ℝ => (x + r • circleDirection θ) 0 / s) := by
  have hp : Continuous (fun θ : ℝ => x + r • circleDirection θ) :=
    continuous_const.add (continuous_circleDirection.const_smul r)
  exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp hp).div_const s

theorem intervalIntegrable_circle_rootCosinePlane (a : RightOnePoint → ℂ)
    {s T r : ℝ} (hs : 0 < s) (hT : 0 ≤ T) (hr : 0 ≤ r)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ T))
    {x : Plane} (hx : x ∈ planeBall (s * T - r)) :
    IntervalIntegrable (fun θ : ℝ => rootCosinePlane a s (x + r • circleDirection θ))
      volume 0 (2 * Real.pi) := by
  have hc : Continuous (fun θ : ℝ => rootCosinePlane a s (x + r • circleDirection θ)) := by
    apply (rootCosineSeries_continuousOn a hT hw).comp_continuous
      (continuous_circle_coordinate_div x r s)
    intro θ
    exact abs_le.mp
      (coordinate_div_abs_lt_of_mem_ball hs (circleEvaluation_mem_ball hr hx θ)).le
  exact hc.intervalIntegrable _ _

/-- The circle multiplier formula for a single scaled coordinate cosine. -/
theorem circularMean_scaled_coordinate_cosine (nu : ℂ) (s r : ℝ) (x : Plane) :
    circularMean (fun y : Plane => Complex.cos (nu * ((y 0 / s : ℝ) : ℂ))) r x =
      Complex.cos (nu * ((x 0 / s : ℝ) : ℂ)) * J0 (((r / s : ℝ) : ℂ) * nu) := by
  have hfun : (fun y : Plane => Complex.cos (nu * ((y 0 / s : ℝ) : ℂ))) =
      spectralCosine (nu / (s : ℂ)) := by
    funext y
    simp only [spectralCosine, Complex.ofReal_div]
    congr 1
    ring
  have harg : (r : ℂ) * (nu / (s : ℂ)) = ((r / s : ℝ) : ℂ) * nu := by
    rw [Complex.ofReal_div]
    ring
  rw [hfun, circularMean_spectralCosine, harg]
  congr 1
  simp only [spectralCosine, Complex.ofReal_div]
  congr 1
  ring

/-- Actual termwise integration, including the summed multiplier series.
The conclusion is about the original circle integral, with every domination
and convergence input supplied. -/
theorem hasSum_circularMean_rootCosinePlane (a : RightOnePoint → ℂ)
    {s T r : ℝ} (hs : 0 < s) (hT : 0 ≤ T) (hr : 0 ≤ r)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ T))
    {x : Plane} (hx : x ∈ planeBall (s * T - r)) :
    HasSum (fun z : RightOnePoint => a z * J0 (((r / s : ℝ) : ℂ) * (z : ℂ)) *
        Complex.cos ((z : ℂ) * ((x 0 / s : ℝ) : ℂ)))
      (circularMean (rootCosinePlane a s) r x) := by
  let B : RightOnePoint → ℝ := fun z =>
    (4 : ℝ) ^ T * (‖a z‖ * ‖(z : ℂ)‖ ^ T)
  have hB : Summable B := hw.mul_left _
  have hcoord (θ : ℝ) : |(x + r • circleDirection θ) 0 / s| ≤ T :=
    (coordinate_div_abs_lt_of_mem_ball hs (circleEvaluation_mem_ball hr hx θ)).le
  have hsum : HasSum
      (fun z : RightOnePoint => ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        a z * Complex.cos ((z : ℂ) * (((x + r • circleDirection θ) 0 / s : ℝ) : ℂ)))
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        rootCosinePlane a s (x + r • circleDirection θ)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (F := fun z : RightOnePoint => fun θ : ℝ => a z *
        Complex.cos ((z : ℂ) * (((x + r • circleDirection θ) 0 / s : ℝ) : ℂ)))
      (f := fun θ : ℝ => rootCosinePlane a s (x + r • circleDirection θ))
      (fun z (_ : ℝ) => B z)
    · intro z
      apply Continuous.aestronglyMeasurable
      exact continuous_const.mul
        (Complex.continuous_cos.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_circle_coordinate_div x r s))))
    · intro z
      exact Eventually.of_forall fun θ _ => rootCosineSeries_norm_majorant a hT (hcoord θ) z
    · exact Eventually.of_forall fun _ _ => hB
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ _ =>
        (rootCosineSeries_summable a hT hw (hcoord θ)).hasSum
  have heach (z : RightOnePoint) : ((2 * Real.pi)⁻¹ : ℝ) •
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        a z * Complex.cos ((z : ℂ) * (((x + r • circleDirection θ) 0 / s : ℝ) : ℂ))) =
      a z * J0 (((r / s : ℝ) : ℂ) * (z : ℂ)) *
        Complex.cos ((z : ℂ) * ((x 0 / s : ℝ) : ℂ)) := by
    change circularMean (fun y : Plane =>
      a z * Complex.cos ((z : ℂ) * ((y 0 / s : ℝ) : ℂ))) r x = _
    rw [circularMean_complex_mul_const, circularMean_scaled_coordinate_cosine]
    ring
  have hscaled := hsum.const_smul (((2 * Real.pi)⁻¹ : ℝ))
  simp_rw [heach] at hscaled
  exact hscaled

theorem circularMean_rootCosinePlane_eq_tsum (a : RightOnePoint → ℂ)
    {s T r : ℝ} (hs : 0 < s) (hT : 0 ≤ T) (hr : 0 ≤ r)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ T))
    {x : Plane} (hx : x ∈ planeBall (s * T - r)) :
    circularMean (rootCosinePlane a s) r x =
      ∑' z : RightOnePoint, a z * J0 (((r / s : ℝ) : ℂ) * (z : ℂ)) *
        Complex.cos ((z : ℂ) * ((x 0 / s : ℝ) : ℂ)) :=
  (hasSum_circularMean_rootCosinePlane a hs hT hr hw hx).tsum_eq.symm

def scaledBesselCosinePlane (M : ℕ) (τ s : ℝ) : Plane → ℂ :=
  rootCosinePlane (fun z : RightOnePoint => scaledBesselResidueCoefficient M τ (z : ℂ)) s

theorem scaledBesselCosinePlane_apply (M : ℕ) (τ s : ℝ) (x : Plane) :
    scaledBesselCosinePlane M τ s x = scaledBesselCosineSeries M τ (x 0 / s) := rfl

theorem scaledBesselCosinePlane_first_mean (M : ℕ) {τ s T : ℝ}
    (hτ : 1 < τ) (hs : 0 < s) (hT : 0 ≤ T) (hMT : T < 2 * M - 1)
    {x : Plane} (hx : x ∈ planeBall (s * T - s)) :
    circularMean (scaledBesselCosinePlane M τ s) s x = scaledBesselCosinePlane M τ s x := by
  have hw := (scaledBesselResidueCoefficient_weight_summable M hτ hMT).subtype
    (fun z : onePoints => 0 < (z : ℂ).re)
  rw [scaledBesselCosinePlane, circularMean_rootCosinePlane_eq_tsum _ hs hT hs.le hw hx]
  change (∑' z : RightOnePoint, _ ) = ∑' z : RightOnePoint, _
  apply tsum_congr
  intro z
  simp only [div_self hs.ne', Complex.ofReal_one, one_mul, z.val.property.2, mul_one]

theorem scaledBesselCosinePlane_second_defect (M : ℕ) {τ s T : ℝ}
    (hτ : 1 < τ) (hs : 0 < s) (hT : 0 ≤ T) (hMT : T < 2 * M - 1)
    {x : Plane} (hx : x ∈ planeBall (s * T - τ * s)) :
    circularMean (scaledBesselCosinePlane M τ s) (τ * s) x -
      scaledBesselCosinePlane M τ s x = besselCosineSeries M (x 0 / s) := by
  let a : RightOnePoint → ℂ := fun z => scaledBesselResidueCoefficient M τ (z : ℂ)
  have hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ T) :=
    (scaledBesselResidueCoefficient_weight_summable M hτ hMT).subtype
      (fun z : onePoints => 0 < (z : ℂ).re)
  have hr : 0 ≤ τ * s := mul_nonneg (by linarith) hs.le
  have hmean := hasSum_circularMean_rootCosinePlane a hs hT hr hw hx
  have hval := (rootCosineSeries_summable a hT hw
    (coordinate_div_abs_lt_on_natural_ball hs hr hx).le).hasSum
  have hdiff := hmean.sub hval
  have hratio : τ * s / s = τ := mul_div_cancel_right₀ τ hs.ne'
  have heq : (fun z : RightOnePoint =>
      a z * J0 ((((τ * s) / s : ℝ) : ℂ) * (z : ℂ)) *
        Complex.cos ((z : ℂ) * ((x 0 / s : ℝ) : ℂ)) -
      a z * Complex.cos ((z : ℂ) * ((x 0 / s : ℝ) : ℂ))) =
      fun z : RightOnePoint => besselResidueCoefficient M z *
        Complex.cos ((z : ℂ) * ((x 0 / s : ℝ) : ℂ)) := by
    funext z
    have hn : J0 ((τ : ℂ) * (z : ℂ)) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp
        (scaled_one_point_defect_ne_zero hτ z.val.property.1 z.val.property.2)))
    rw [hratio]
    dsimp only [a, scaledBesselResidueCoefficient]
    field_simp [hn]
  rw [heq] at hdiff
  exact hdiff.tsum_eq.symm

/-- On the critical ball of radius s(1+τ), the second natural center domain
is the ball of radius s.  Its genuine defect is the explicit central
polynomial, while the first natural domain has the exact first mean. -/
theorem scaledBesselCosinePlane_critical_mean_defects (M : ℕ) (hM : 2 ≤ M)
    {τ s T : ℝ} (hτ : 1 < τ) (hs : 0 < s)
    (hlarge : 1 + τ ≤ T) (hMT : T < 2 * M - 1) :
    (∀ x ∈ planeBall (s * (1 + τ) - s),
      circularMean (scaledBesselCosinePlane M τ s) s x = scaledBesselCosinePlane M τ s x) ∧
    (∀ x ∈ planeBall (s * (1 + τ) - τ * s),
      circularMean (scaledBesselCosinePlane M τ s) (τ * s) x -
        scaledBesselCosinePlane M τ s x =
          (besselCentralPolynomial M).eval ((x 0 / s : ℝ) : ℂ)) := by
  have hT : 0 ≤ T := by linarith
  have hsub (r : ℝ) : planeBall (s * (1 + τ) - r) ⊆ planeBall (s * T - r) := by
    intro x hx
    have hn : ‖x‖ < s * (1 + τ) - r := by
      simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
    change dist x 0 < s * T - r
    rw [dist_zero_right]
    nlinarith
  constructor
  · intro x hx
    exact scaledBesselCosinePlane_first_mean M hτ hs hT hMT (hsub s hx)
  · intro x hx
    rw [scaledBesselCosinePlane_second_defect M hτ hs hT hMT (hsub (τ * s) hx)]
    apply besselCosineSeries_eq_centralPolynomial M hM
    have hx' : x ∈ planeBall (s * 1) := by
      convert! hx using 1 <;> ring
    exact abs_le.mp (coordinate_div_abs_lt_of_mem_ball hs hx').le

end J0RadialUniqueness
