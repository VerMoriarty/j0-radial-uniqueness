import Solutions.J0RadialUniqueness.ClassicalWeakHarmonic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Actual geometric dilation of the sharpness candidates.  The circle
identity is pointwise under its defining integral.  Almost-everywhere mean
identities are transported by the proved quasi-measure-preserving homothety.
The Laplacian formula uses the actual second multilinear derivative, and the
local C² distribution bridge supplies the nonharmonicity transport. -/

noncomputable section

open MeasureTheory Set Filter Laplacian
open scoped Topology ContDiff

namespace J0RadialUniqueness

def sharpnessScale {V : Type*} (f : Plane → V) (s : ℝ) (x : Plane) : V :=
  f (s⁻¹ • x)

theorem mem_scaled_ball_iff {s R : ℝ} (hs : 0 < s) (x : Plane) :
    x ∈ planeBall (s * R) ↔ s⁻¹ • x ∈ planeBall R := by
  have hnorm : ‖s⁻¹ • x‖ = ‖x‖ / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
    ring
  simp only [planeBall, Metric.mem_ball, dist_zero_right, hnorm]
  rw [div_lt_iff₀ hs]
  simp only [mul_comm R s]

theorem smul_mem_scaled_ball {s R : ℝ} (hs : 0 < s) {x : Plane}
    (hx : x ∈ planeBall R) : s • x ∈ planeBall (s * R) := by
  apply (mem_scaled_ball_iff hs (s • x)).mpr
  simpa only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using hx

theorem circularMean_sharpnessScale {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Plane → V)
    {s : ℝ} (hs : 0 < s) (r : ℝ) (x : Plane) :
    circularMean (sharpnessScale f s) (s * r) x =
      circularMean f r (s⁻¹ • x) := by
  unfold circularMean sharpnessScale
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  simp only [smul_add, smul_smul, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

/-- This transports a genuine a.e. mean equation.  The exceptional set is
pulled back through the nonzero homothety using its actual Haar-measure
quasi-invariance. -/
theorem meanIdentityOn_sharpnessScale {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Plane → V}
    {s r R : ℝ} (hs : 0 < s) (hm : MeanIdentityOn f r (planeBall R)) :
    MeanIdentityOn (sharpnessScale f s) (s * r) (planeBall (s * R)) := by
  have ha : ∀ᵐ y : Plane, y ∈ planeBall R → circularMean f r y = f y :=
    ae_imp_of_ae_restrict hm
  have ht := (Measure.quasiMeasurePreserving_smul (volume : Measure Plane)
    (inv_ne_zero hs.ne')).ae ha
  apply (ae_restrict_iff' (show MeasurableSet (planeBall (s * R)) from measurableSet_ball)).mpr
  filter_upwards [ht] with x hx hball
  rw [circularMean_sharpnessScale f hs r x]
  exact hx ((mem_scaled_ball_iff hs x).mp hball)

theorem meanIdentityOn_sharpnessScale_natural {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Plane → V}
    {s r R : ℝ} (hs : 0 < s) (hm : MeanIdentityOn f r (planeBall (R - r))) :
    MeanIdentityOn (sharpnessScale f s) (s * r) (planeBall (s * R - s * r)) := by
  have hh := meanIdentityOn_sharpnessScale hs hm
  simpa only [mul_sub] using hh

theorem sharpnessScale_contDiff {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Plane → V}
    {n : ℕ∞ω} (hf : ContDiff ℝ n f) (s : ℝ) :
    ContDiff ℝ n (sharpnessScale f s) := by
  exact hf.comp (contDiff_id.const_smul s⁻¹)

theorem sharpnessScale_contDiffOn {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Plane → V}
    {n : ℕ∞ω} {s R : ℝ} (hs : 0 < s)
    (hf : ContDiffOn ℝ n f (planeBall R)) :
    ContDiffOn ℝ n (sharpnessScale f s) (planeBall (s * R)) := by
  apply hf.comp (contDiff_id.const_smul s⁻¹).contDiffOn
  intro x hx
  exact (mem_scaled_ball_iff hs x).mp hx

def planeDilation (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
  (LinearEquiv.smulOfNeZero ℝ Plane c hc).toContinuousLinearEquiv

@[simp] theorem planeDilation_apply (c : ℝ) (hc : c ≠ 0) (x : Plane) :
    planeDilation c hc x = c • x := rfl

/-- A nonzero scalar change of variables multiplies the actual Laplacian
by the square of that scalar.  The totalized iterated derivative definitions
make this identity valid even without a regularity assumption. -/
theorem laplacian_comp_planeDilation {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Plane → V)
    (c : ℝ) (hc : c ≠ 0) (x : Plane) :
    laplacian (f ∘ planeDilation c hc) x = c ^ 2 • laplacian f (c • x) := by
  let e := planeDilation c hc
  let v := stdOrthonormalBasis ℝ Plane
  have hcomp : iteratedFDeriv ℝ 2 (f ∘ e) x =
      (iteratedFDeriv ℝ 2 f (e x)).compContinuousLinearMap
        (fun _ : Fin 2 => e.toContinuousLinearMap) := by
    have hh := e.iteratedFDerivWithin_comp_right f
      (s := Set.univ) uniqueDiffOn_univ (x := x) (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hh
    convert! hh using 1 <;> rfl
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ e) v,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f v,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (iteratedFDeriv ℝ 2 f (c • x))
      (fun j : Fin 2 => c • (![v i, v i] j)) =
    c ^ 2 • (iteratedFDeriv ℝ 2 f (c • x)) ![v i, v i]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Fin.prod_univ_two, pow_two]

theorem laplacian_sharpnessScale {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Plane → V)
    {s : ℝ} (hs : 0 < s) (x : Plane) :
    laplacian (sharpnessScale f s) x = (s⁻¹) ^ 2 • laplacian f (s⁻¹ • x) := by
  exact laplacian_comp_planeDilation f s⁻¹ (inv_ne_zero hs.ne') x

theorem laplacian_sharpnessScale_complex (f : Plane → ℂ)
    {s : ℝ} (hs : 0 < s) (x : Plane) :
    laplacian (sharpnessScale f s) x =
      (((s⁻¹) ^ 2 : ℝ) : ℂ) * laplacian f (s⁻¹ • x) := by
  rw [laplacian_sharpnessScale f hs, Complex.real_smul]

/-- Local C² weak harmonicity is equivalent before and after a positive
dilation, by the actual classical/distributional bridge on the two balls. -/
theorem distributionHarmonicOn_sharpnessScale_iff {f : Plane → ℂ}
    {s R : ℝ} (hs : 0 < s) (hf : ContDiffOn ℝ 2 f (planeBall R)) :
    DistributionHarmonicOn (sharpnessScale f s) (planeBall (s * R)) ↔
      DistributionHarmonicOn f (planeBall R) := by
  have hscaled : ContDiffOn ℝ 2 (sharpnessScale f s) (planeBall (s * R)) :=
    sharpnessScale_contDiffOn hs hf
  have h₁ : DistributionHarmonicOn (sharpnessScale f s) (planeBall (s * R)) ↔
      ∀ x ∈ planeBall (s * R), laplacian (sharpnessScale f s) x = 0 :=
    distributionHarmonicOn_iff_laplacian_eq_zero Metric.isOpen_ball hscaled
  have h₂ : DistributionHarmonicOn f (planeBall R) ↔
      ∀ x ∈ planeBall R, laplacian f x = 0 :=
    distributionHarmonicOn_iff_laplacian_eq_zero Metric.isOpen_ball hf
  constructor
  · intro hw
    apply h₂.mpr
    intro x hx
    have hz := h₁.mp hw
    have hy := hz (s • x) (smul_mem_scaled_ball hs hx)
    rw [laplacian_sharpnessScale_complex f hs,
      smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at hy
    have hn : (((s⁻¹) ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hs.ne'))
    exact (mul_eq_zero.mp hy).resolve_left hn
  · intro hw
    apply h₁.mpr
    intro x hx
    have hz := h₂.mp hw
    rw [laplacian_sharpnessScale f hs, hz _ ((mem_scaled_ball_iff hs x).mp hx), smul_zero]

theorem not_distributionHarmonicOn_sharpnessScale {f : Plane → ℂ}
    {s R : ℝ} (hs : 0 < s) (hf : ContDiffOn ℝ 2 f (planeBall R))
    (hn : ¬ DistributionHarmonicOn f (planeBall R)) :
    ¬ DistributionHarmonicOn (sharpnessScale f s) (planeBall (s * R)) :=
  fun hw => hn ((distributionHarmonicOn_sharpnessScale_iff hs hf).mp hw)

end J0RadialUniqueness
