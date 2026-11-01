import Definitions.J0RadialUniqueness.TwoRadius
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! Representative independence and integrability for the actual circular mean.

The almost-everywhere assertion is proved by a measurable null hull and Fubini.
It does not claim that changing an ambient null set leaves every individual
circle unchanged.  The integrability results below use a measure-preserving
skew translation and the finite angle interval.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace J0RadialUniqueness

theorem continuous_circleDirection : Continuous circleDirection := by
  unfold circleDirection
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using (show Continuous (fun t : ℝ => Real.cos t) from Real.continuous_cos)
  · simpa using (show Continuous (fun t : ℝ => Real.sin t) from Real.continuous_sin)

@[simp] theorem norm_circleDirection (t : ℝ) : ‖circleDirection t‖ = 1 := by
  have hs : ‖circleDirection t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [circleDirection, Fin.sum_univ_two, add_comm] using Real.sin_sq_add_cos_sq t
  nlinarith [norm_nonneg (circleDirection t)]

/-- Measurable families of translations transport an ambient AE equality to
AE parameters for AE centers.  A measurable null hull permits arbitrary
representatives, without assuming that either representative is measurable. -/
theorem ae_ae_add_of_aeEq {V B : Type*} [MeasurableSpace B]
    (ν : Measure B) [SFinite ν] {f g : Plane → V}
    (hfg : f =ᵐ[volume] g) {b : B → Plane} (hb : Measurable b) :
    ∀ᵐ x : Plane, ∀ᵐ t ∂ν, f (x + b t) = g (x + b t) := by
  obtain ⟨N, hsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hfg)
  have hNae : ∀ᵐ x : Plane, x ∉ N := by
    apply ae_iff.mpr
    simp only [not_not]
    convert! hNzero using 1
  have hfirst : ∀ᵐ t ∂ν, ∀ᵐ x : Plane, x + b t ∉ N := by
    exact Eventually.of_forall (fun t =>
      (measurePreserving_add_right (volume : Measure Plane) (b t)).quasiMeasurePreserving.ae hNae)
  have hm : MeasurableSet {p : B × Plane | p.2 + b p.1 ∉ N} :=
    hNm.compl.preimage (measurable_snd.add (hb.comp measurable_fst))
  have hsecond := (MeasureTheory.Measure.ae_ae_comm hm).mp hfirst
  filter_upwards [hsecond] with x hx
  filter_upwards [hx] with t ht
  by_contra hneq
  exact ht (hsub hneq)

theorem ae_circleEvaluation_congr {V : Type*} {f g : Plane → V}
    (hfg : f =ᵐ[volume] g) (r : ℝ) :
    ∀ᵐ x : Plane,
      (fun t : ℝ => f (x + r • circleDirection t)) =ᵐ[volume]
        (fun t : ℝ => g (x + r • circleDirection t)) :=
  ae_ae_add_of_aeEq volume hfg (continuous_circleDirection.const_smul r).measurable

/-- The circular mean depends only on the ambient almost-everywhere class. -/
theorem circularMean_congr_ae {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Plane → V} (hfg : f =ᵐ[volume] g) (r : ℝ) :
    circularMean f r =ᵐ[volume] circularMean g r := by
  filter_upwards [ae_circleEvaluation_congr hfg r] with x hx
  unfold circularMean
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hx] with t ht using fun _ => ht

theorem meanIdentityOn_congr_ae {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Plane → V} (hfg : f =ᵐ[volume] g) (r : ℝ) (U : Set Plane) :
    MeanIdentityOn f r U ↔ MeanIdentityOn g r U := by
  have hmean := ae_restrict_of_ae (s := U) (circularMean_congr_ae hfg r)
  have hvalues := ae_restrict_of_ae (s := U) hfg
  constructor <;> intro h
  · filter_upwards [h, hmean, hvalues] with x hx hm hv
    exact hm.symm.trans (hx.trans hv)
  · filter_upwards [h, hmean, hvalues] with x hx hm hv
    exact hm.trans (hx.trans hv.symm)

/-- Skew translation on parameter-center space preserves the product measure. -/
theorem measurePreserving_parameter_translation {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [SFinite ν] {b : B → Plane} (hb : Measurable b) :
    MeasurePreserving (fun p : B × Plane => (p.1, p.2 + b p.1))
      (ν.prod volume) (ν.prod volume) := by
  apply (MeasurePreserving.id ν).skew_product
    (g := fun t x => x + b t)
  · exact measurable_snd.add (hb.comp measurable_fst)
  · exact Eventually.of_forall (fun t =>
      (measurePreserving_add_right (volume : Measure Plane) (b t)).map_eq)

theorem integrable_circleEvaluation_product {V : Type*} [NormedAddCommGroup V]
    {f : Plane → V} (hf : Integrable f) (r : ℝ) :
    Integrable (fun p : ℝ × Plane => f (p.2 + r • circleDirection p.1))
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod volume) := by
  exact (measurePreserving_parameter_translation
    (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    (continuous_circleDirection.const_smul r).measurable).integrable_comp_of_integrable
      (hf.comp_snd (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))

/-- For an ambient L1 function, the circle integral exists at almost every center. -/
theorem ae_intervalIntegrable_circleEvaluation {V : Type*} [NormedAddCommGroup V]
    {f : Plane → V} (hf : Integrable f) (r : ℝ) :
    ∀ᵐ x : Plane,
      IntervalIntegrable (fun t : ℝ => f (x + r • circleDirection t)) volume
        0 (2 * Real.pi) := by
  filter_upwards [(integrable_circleEvaluation_product hf r).prod_left_ae] with x hx
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr hx

/-- Averaging over the circle sends ambient L1 functions to ambient L1 functions. -/
theorem integrable_circularMean {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : Integrable f) (r : ℝ) : Integrable (circularMean f r) := by
  have h := (integrable_circleEvaluation_product hf r).integral_prod_right
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  unfold circularMean
  simp only [intervalIntegral.integral_of_le hle]
  convert! h.smul ((2 * Real.pi)⁻¹ : ℝ) using 1

/-- A cutoff agrees on every circle contained in its cutoff set. -/
theorem circularMean_indicator_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) (r : ℝ) (x : Plane) (S : Set Plane)
    (hS : ∀ t : ℝ, x + r • circleDirection t ∈ S) :
    circularMean (S.indicator f) r x = circularMean f r x := by
  unfold circularMean
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact indicator_of_mem (hS t) f

/-- A closed-ball cutoff contains each circle whose center has the indicated margin. -/
theorem circleEvaluation_mem_closedBall {r S : ℝ} {x : Plane}
    (hx : ‖x‖ + |r| ≤ S) (t : ℝ) :
    x + r • circleDirection t ∈ Metric.closedBall (0 : Plane) S := by
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖x + r • circleDirection t‖ ≤ ‖x‖ + ‖r • circleDirection t‖ := norm_add_le _ _
    _ = ‖x‖ + |r| := by rw [norm_smul, Real.norm_eq_abs, norm_circleDirection, mul_one]
    _ ≤ S := hx

/-- The actual circular mean is integrable on every smaller center ball for which
the closed-ball cutoff of the original function is integrable. -/
theorem integrableOn_circularMean_ball_of_integrableOn_closedBall
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} {r S T : ℝ}
    (hf : IntegrableOn f (Metric.closedBall (0 : Plane) S)) (hTS : T + |r| ≤ S) :
    IntegrableOn (circularMean f r) (Metric.ball (0 : Plane) T) := by
  have hg : Integrable ((Metric.closedBall (0 : Plane) S).indicator f) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr hf
  apply ((integrable_circularMean hg r).integrableOn).congr_fun _ measurableSet_ball
  intro x hx
  apply circularMean_indicator_eq
  intro t
  exact circleEvaluation_mem_closedBall (by
    have hnorm : ‖x‖ < T := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    linarith) t

theorem ae_intervalIntegrable_circleEvaluation_ball_of_integrableOn_closedBall
    {V : Type*} [NormedAddCommGroup V] {f : Plane → V} {r S T : ℝ}
    (hf : IntegrableOn f (Metric.closedBall (0 : Plane) S)) (hTS : T + |r| ≤ S) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Plane) T),
      IntervalIntegrable (fun t : ℝ => f (x + r • circleDirection t)) volume
        0 (2 * Real.pi) := by
  have hg : Integrable ((Metric.closedBall (0 : Plane) S).indicator f) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr hf
  filter_upwards [ae_restrict_of_ae (ae_intervalIntegrable_circleEvaluation hg r),
    ae_restrict_mem measurableSet_ball] with x hx hxt
  apply hx.congr
  intro t _
  apply indicator_of_mem _ f
  apply circleEvaluation_mem_closedBall
  have hnorm : ‖x‖ < T := by simpa only [Metric.mem_ball, dist_zero_right] using hxt
  linarith

/-- Every compact inner center ball has a globally integrable cutoff with the
same circle evaluations. -/
theorem circle_cutoff_integrable_of_locallyIntegrableOn
    {V : Type*} [NormedAddCommGroup V] {f : Plane → V} {R r T : ℝ}
    (hf : LocallyIntegrableOn f (planeBall R)) (hr : 0 ≤ r) (hT : T + r < R) :
    IntegrableOn f (Metric.closedBall (0 : Plane) ((T + r + R) / 2)) ∧
      T + |r| ≤ (T + r + R) / 2 := by
  constructor
  · apply hf.integrableOn_compact_subset _ (isCompact_closedBall (0 : Plane) _)
    intro x hx
    have hxnorm : ‖x‖ ≤ (T + r + R) / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change dist x 0 < R
    rw [dist_zero_right]
    linarith
  · rw [abs_of_nonneg hr]
    linarith

/-- Local integrability of the actual mean on its full natural domain. -/
theorem locallyIntegrableOn_circularMean_ball
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} {R r : ℝ} (hf : LocallyIntegrableOn f (planeBall R))
    (hr : 0 ≤ r) : LocallyIntegrableOn (circularMean f r) (planeBall (R - r)) := by
  intro x hx
  have hxn : ‖x‖ < R - r := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
  obtain ⟨T, hxT, hTR⟩ := exists_between hxn
  obtain ⟨hcut, hmargin⟩ := circle_cutoff_integrable_of_locallyIntegrableOn hf hr
    (show T + r < R by linarith)
  refine ⟨Metric.ball (0 : Plane) T, ?_,
    integrableOn_circularMean_ball_of_integrableOn_closedBall hcut hmargin⟩
  apply mem_nhdsWithin_of_mem_nhds
  exact Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hxT)

/-- Fubini and countable inner-ball exhaustion give circle integrability almost
everywhere throughout `B_(R-r)`, for a function locally integrable on `B_R`. -/
theorem ae_intervalIntegrable_circleEvaluation_of_locallyIntegrableOn_ball
    {V : Type*} [NormedAddCommGroup V] {f : Plane → V} {R r : ℝ}
    (hf : LocallyIntegrableOn f (planeBall R)) (hr : 0 ≤ r) :
    ∀ᵐ x ∂volume.restrict (planeBall (R - r)),
      IntervalIntegrable (fun t : ℝ => f (x + r • circleDirection t)) volume
        0 (2 * Real.pi) := by
  let Q := {q : ℚ // (q : ℝ) + r < R}
  have hballs : planeBall (R - r) = ⋃ q : Q, Metric.ball (0 : Plane) (q.1 : ℝ) := by
    ext x
    constructor
    · intro hx
      have hxn : ‖x‖ < R - r := by
        simpa only [planeBall, Metric.mem_ball, dist_zero_right] using hx
      obtain ⟨q, hxq, hqR⟩ := exists_rat_btwn hxn
      apply mem_iUnion.mpr
      refine ⟨⟨q, by linarith⟩, ?_⟩
      simpa only [Metric.mem_ball, dist_zero_right] using hxq
    · intro hx
      obtain ⟨q, hxq⟩ := mem_iUnion.mp hx
      have hxn : ‖x‖ < (q.1 : ℝ) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hxq
      have hq := q.2
      change dist x 0 < R - r
      rw [dist_zero_right]
      linarith
  rw [hballs]
  apply (ae_restrict_iUnion_iff _ _).mpr
  intro q
  obtain ⟨hcut, hmargin⟩ := circle_cutoff_integrable_of_locallyIntegrableOn hf hr q.2
  exact ae_intervalIntegrable_circleEvaluation_ball_of_integrableOn_closedBall hcut hmargin

end J0RadialUniqueness
