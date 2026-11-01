import Solutions.J0RadialUniqueness.CircularMeanRegularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! Actual first and second radial derivatives of the circular mean.

The finite-parameter integral lemma below derives its uniform majorant from
continuity on a compact rectangle.  The circle derivatives are then obtained
from the real Fréchet derivative of the original function and differentiation
under the actual interval integral.  No mean-value, harmonicity or Green identity
is assumed. These derivative nodes precede the angular trace calculation needed
for the radial Laplace equation.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

section FiniteParameterIntegral

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuously parametrized derivative can be integrated over any fixed
finite interval. Compactness supplies the domination; it is not an extra input. -/
theorem hasDerivAt_intervalIntegral_of_joint_continuous
    {G H : ℝ → ℝ → V}
    (hG : Continuous (Function.uncurry G)) (hH : Continuous (Function.uncurry H))
    (hd : ∀ s t : ℝ, HasDerivAt (fun u : ℝ => G u t) (H s t) s)
    (a b s : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ t : ℝ in a..b, G u t)
      (∫ t : ℝ in a..b, H s t) s := by
  have hcompact : IsCompact (Metric.closedBall s (1 : ℝ) ×ˢ uIcc a b) :=
    (isCompact_closedBall s 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hH.continuousOn
  have hGc : ∀ u : ℝ, Continuous (G u) := fun u =>
    hG.comp (continuous_const.prodMk continuous_id)
  have hHc : Continuous (H s) := hH.comp (continuous_const.prodMk continuous_id)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := H) (μ := volume) (bound := fun _ : ℝ => C)
    (s := Metric.closedBall s 1)
    (Metric.closedBall_mem_nhds s (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun u => (hGc u).aestronglyMeasurable))
    ((hGc s).intervalIntegrable a b) hHc.aestronglyMeasurable
    (Eventually.of_forall (fun t ht u hu => hC (u, t) ⟨hu, uIoc_subset_uIcc ht⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun t _ u _ => hd u t))
  exact h.2

end FiniteParameterIntegral

section CircleProfiles

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def circleProfile (f : Plane → V) (x : Plane) (r : ℝ) : V := circularMean f r x

def circleValueIntegrand (f : Plane → V) (x : Plane) (r t : ℝ) : V :=
  f (x + r • circleDirection t)

def circleSlopeIntegrand (f : Plane → V) (x : Plane) (r t : ℝ) : V :=
  fderiv ℝ f (x + r • circleDirection t) (circleDirection t)

def circleAccelIntegrand (f : Plane → V) (x : Plane) (r t : ℝ) : V :=
  fderiv ℝ (fderiv ℝ f) (x + r • circleDirection t)
    (circleDirection t) (circleDirection t)

def circleRadialSlope (f : Plane → V) (x : Plane) (r : ℝ) : V :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circleSlopeIntegrand f x r t

def circleRadialAccel (f : Plane → V) (x : Plane) (r : ℝ) : V :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), circleAccelIntegrand f x r t

@[simp] theorem circleProfile_zero [CompleteSpace V] (f : Plane → V) (x : Plane) :
    circleProfile f x 0 = f x := by
  simp only [circleProfile, circularMean, zero_smul, add_zero,
    intervalIntegral.integral_const, sub_zero, smul_smul]
  rw [inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]

theorem continuous_circleParameterMap (x : Plane) :
    Continuous (fun p : ℝ × ℝ => x + p.1 • circleDirection p.2) :=
  continuous_const.add (continuous_fst.smul (continuous_circleDirection.comp continuous_snd))

theorem circleParameterMap_hasDerivAt (x : Plane) (r t : ℝ) :
    HasDerivAt (fun u : ℝ => x + u • circleDirection t) (circleDirection t) r := by
  convert! ((hasDerivAt_id r).smul_const (circleDirection t)).const_add x using 1 <;>
    simp only [id_eq, one_smul]

theorem continuous_circleValueIntegrand {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) : Continuous (Function.uncurry (circleValueIntegrand f x)) :=
  hf.continuous.comp (continuous_circleParameterMap x)

theorem continuous_circleSlopeIntegrand {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) : Continuous (Function.uncurry (circleSlopeIntegrand f x)) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact (hdf.continuous.comp (continuous_circleParameterMap x)).clm_apply
    (continuous_circleDirection.comp continuous_snd)

theorem continuous_circleAccelIntegrand {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) : Continuous (Function.uncurry (circleAccelIntegrand f x)) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hddf : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hdf.fderiv_right (by simp)
  exact ((hddf.continuous.comp (continuous_circleParameterMap x)).clm_apply
    (continuous_circleDirection.comp continuous_snd)).clm_apply
      (continuous_circleDirection.comp continuous_snd)

/-- The pointwise chain rule is proved before passing any derivative under an integral. -/
theorem circleValueIntegrand_hasDerivAt {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r t : ℝ) :
    HasDerivAt (fun u : ℝ => circleValueIntegrand f x u t)
      (circleSlopeIntegrand f x r t) r := by
  have hdf := ((hf.differentiable (by simp)).differentiableAt
    (x := x + r • circleDirection t)).hasFDerivAt
  exact hdf.comp_hasDerivAt r (circleParameterMap_hasDerivAt x r t)

/-- Differentiating the directional first derivative gives the actual second jet. -/
theorem circleSlopeIntegrand_hasDerivAt {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r t : ℝ) :
    HasDerivAt (fun u : ℝ => circleSlopeIntegrand f x u t)
      (circleAccelIntegrand f x r t) r := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd := ((hdf.differentiable (by simp)).differentiableAt
    (x := x + r • circleDirection t)).hasFDerivAt
  have hcomp := hd.comp_hasDerivAt r (circleParameterMap_hasDerivAt x r t)
  have h := hcomp.clm_apply (hasDerivAt_const r (circleDirection t))
  simp only [ContinuousLinearMap.map_zero, add_zero] at h
  convert! h using 1 <;> rfl

theorem intervalIntegrable_circleSlopeIntegrand {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    IntervalIntegrable (circleSlopeIntegrand f x r) volume 0 (2 * Real.pi) :=
  ((continuous_circleSlopeIntegrand hf x).comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * Real.pi)

theorem intervalIntegrable_circleAccelIntegrand {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    IntervalIntegrable (circleAccelIntegrand f x r) volume 0 (2 * Real.pi) :=
  ((continuous_circleAccelIntegrand hf x).comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * Real.pi)

/-- First radial derivative of the actual normalized circular mean, at every real radius. -/
theorem circleProfile_hasDerivAt {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    HasDerivAt (circleProfile f x) (circleRadialSlope f x r) r := by
  have h := hasDerivAt_intervalIntegral_of_joint_continuous
    (continuous_circleValueIntegrand hf x) (continuous_circleSlopeIntegrand hf x)
    (circleValueIntegrand_hasDerivAt hf x) 0 (2 * Real.pi) r
  exact h.const_smul ((2 * Real.pi)⁻¹ : ℝ)

/-- Second radial derivative, obtained by a second justified parameter differentiation. -/
theorem circleRadialSlope_hasDerivAt {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    HasDerivAt (circleRadialSlope f x) (circleRadialAccel f x r) r := by
  have h := hasDerivAt_intervalIntegral_of_joint_continuous
    (continuous_circleSlopeIntegrand hf x) (continuous_circleAccelIntegrand hf x)
    (circleSlopeIntegrand_hasDerivAt hf x) 0 (2 * Real.pi) r
  exact h.const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem circleProfile_deriv {f : Plane → V} (hf : ContDiff ℝ ∞ f) (x : Plane) (r : ℝ) :
    deriv (circleProfile f x) r = circleRadialSlope f x r :=
  (circleProfile_hasDerivAt hf x r).deriv

theorem circleProfile_deriv_hasDerivAt {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    HasDerivAt (deriv (circleProfile f x)) (circleRadialAccel f x r) r := by
  have heq : deriv (circleProfile f x) = circleRadialSlope f x :=
    funext (circleProfile_deriv hf x)
  rw [heq]
  exact circleRadialSlope_hasDerivAt hf x r

theorem circleProfile_second_deriv {f : Plane → V} (hf : ContDiff ℝ ∞ f)
    (x : Plane) (r : ℝ) :
    deriv (deriv (circleProfile f x)) r = circleRadialAccel f x r :=
  (circleProfile_deriv_hasDerivAt hf x r).deriv

theorem circleProfile_differentiable {f : Plane → V} (hf : ContDiff ℝ ∞ f) (x : Plane) :
    Differentiable ℝ (circleProfile f x) :=
  fun r => (circleProfile_hasDerivAt hf x r).differentiableAt

theorem circleRadialSlope_differentiable {f : Plane → V} (hf : ContDiff ℝ ∞ f) (x : Plane) :
    Differentiable ℝ (circleRadialSlope f x) :=
  fun r => (circleRadialSlope_hasDerivAt hf x r).differentiableAt

end CircleProfiles

end J0RadialUniqueness
