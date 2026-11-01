import Definitions.J0RadialUniqueness.TwoRadius
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-! Transport of the actual plane Laplacian and circular mean to the complex plane.

The transport of the Laplacian is proved using the second iterated derivative
and an orthonormal basis mapped by a linear isometry.  The circle parametrization
is then identified pointwise, before applying Mathlib's harmonic mean-value theorem.
-/

noncomputable section

open Laplacian MeasureTheory
open scoped Topology Interval ContDiff

namespace J0RadialUniqueness

section Isometries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A linear isometric change of variables preserves the actual Laplacian.
The equality also respects the totalized derivative definitions. -/
theorem laplacian_comp_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] G) (f : G → V) (x : E) :
    laplacian (f ∘ e) x = laplacian f (e x) := by
  let v := stdOrthonormalBasis ℝ E
  have hcomp : iteratedFDeriv ℝ 2 (f ∘ e) x =
      (iteratedFDeriv ℝ 2 f (e x)).compContinuousLinearMap
        (fun _ : Fin 2 => e.toContinuousLinearEquiv.toContinuousLinearMap) := by
    have h := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
      (s := Set.univ) uniqueDiffOn_univ (x := x) (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
    convert! h using 1 <;> rfl
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ e) v,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (v.map e)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  apply congrArg (iteratedFDeriv ℝ 2 f (e x))
  funext j
  fin_cases j <;> rfl

/-- Harmonicity is preserved by the same change of variables on the domain. -/
theorem harmonicAt_comp_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] G) (f : G → V) (x : E)
    (hf : InnerProductSpace.HarmonicAt f (e x)) :
    InnerProductSpace.HarmonicAt (f ∘ e) x := by
  constructor
  · exact hf.1.comp x
      e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt
  · filter_upwards [hf.2.comp_tendsto e.continuous.continuousAt] with y hy
    simpa only [laplacian_comp_linearIsometryEquiv, Function.comp_apply, Pi.zero_apply] using hy

/-- Setwise version, with the domain pulled back exactly by the isometry. -/
theorem harmonicOnNhd_comp_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] G) (f : G → V)
    {s : Set G} (hf : InnerProductSpace.HarmonicOnNhd f s) :
    InnerProductSpace.HarmonicOnNhd (f ∘ e) (e ⁻¹' s) := by
  intro x hx
  exact harmonicAt_comp_linearIsometryEquiv e f x (hf (e x) hx)

end Isometries

/-- The concrete real linear isometry from the complex plane to `Plane`. -/
def complexToPlane : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

@[simp] theorem complexToPlane_symm_apply (x : Plane) :
    complexToPlane.symm x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  rfl

/-- The coordinate bridge preserves the actual Lebesgue measures. -/
theorem complexToPlane_measurePreserving :
    MeasurePreserving complexToPlane (volume : Measure ℂ) (volume : Measure Plane) :=
  complexToPlane.measurePreserving

/-- Its inverse preserves Lebesgue measure as well. -/
theorem planeToComplex_measurePreserving :
    MeasurePreserving complexToPlane.symm (volume : Measure Plane) (volume : Measure ℂ) :=
  complexToPlane.symm.measurePreserving

section PlaneFunctions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem laplacian_comp_complexToPlane (f : Plane → V) (z : ℂ) :
    laplacian (f ∘ complexToPlane) z = laplacian f (complexToPlane z) :=
  laplacian_comp_linearIsometryEquiv complexToPlane f z

theorem harmonicOnNhd_comp_complexToPlane (f : Plane → V) {s : Set Plane}
    (hf : InnerProductSpace.HarmonicOnNhd f s) :
    InnerProductSpace.HarmonicOnNhd (f ∘ complexToPlane) (complexToPlane ⁻¹' s) :=
  harmonicOnNhd_comp_linearIsometryEquiv complexToPlane f hf

/-- The inverse image of the geometric closed ball has the same radius. -/
theorem complexToPlane_preimage_closedBall (x : Plane) (R : ℝ) :
    complexToPlane ⁻¹' Metric.closedBall x R =
      Metric.closedBall (complexToPlane.symm x) R := by
  ext z
  simp only [Set.mem_preimage, Metric.mem_closedBall]
  have hd : dist (complexToPlane z) x = dist z (complexToPlane.symm x) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      complexToPlane.dist_map z (complexToPlane.symm x)
  rw [hd]

/-- The paper's actual cosine-sine direction equals the standard complex exponential. -/
theorem complexToPlane_symm_circleDirection (t : ℝ) :
    complexToPlane.symm (circleDirection t) = Complex.exp ((t : ℂ) * Complex.I) := by
  simp [complexToPlane_symm_apply, circleDirection, PiLp.toLp_apply,
    Complex.exp_ofReal_mul_I]

/-- The actual plane circle is the isometric image of Mathlib's `circleMap`. -/
theorem complexToPlane_circleMap (c : ℂ) (r t : ℝ) :
    complexToPlane (circleMap c r t) = complexToPlane c + r • circleDirection t := by
  have hexp := congrArg complexToPlane (complexToPlane_symm_circleDirection t)
  rw [complexToPlane.apply_symm_apply] at hexp
  unfold circleMap
  rw [← Complex.real_smul, complexToPlane.map_add, complexToPlane.map_smul, ← hexp]

/-- Both circular means use exactly the same angular parametrization and normalization. -/
theorem circularMean_eq_circleAverage (f : Plane → V) (r : ℝ) (x : Plane) :
    circularMean f r x =
      Real.circleAverage (f ∘ complexToPlane) (complexToPlane.symm x) r := by
  unfold circularMean Real.circleAverage
  apply congrArg (fun v : V => ((2 * Real.pi)⁻¹ : ℝ) • v)
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [Function.comp_apply, complexToPlane_circleMap,
    LinearIsometryEquiv.apply_symm_apply]

variable [CompleteSpace V]

/-- Local mean-value property on a neighborhood of the closed ball, for all real radii. -/
theorem circularMean_eq_of_harmonicOnNhd_closedBall (f : Plane → V) (r : ℝ) (x : Plane)
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall x |r|)) :
    circularMean f r x = f x := by
  have htransport := harmonicOnNhd_comp_complexToPlane f hf
  rw [complexToPlane_preimage_closedBall] at htransport
  calc
    circularMean f r x =
        Real.circleAverage (f ∘ complexToPlane) (complexToPlane.symm x) r :=
      circularMean_eq_circleAverage f r x
    _ = (f ∘ complexToPlane) (complexToPlane.symm x) := htransport.circleAverage_eq
    _ = f x := by
      change f (complexToPlane (complexToPlane.symm x)) = f x
      rw [complexToPlane.apply_symm_apply]

/-- Global plane harmonic functions have the paper's circular mean property at every radius. -/
theorem circularMean_eq_of_harmonicOnNhd (f : Plane → V)
    (hf : InnerProductSpace.HarmonicOnNhd f Set.univ) (r : ℝ) (x : Plane) :
    circularMean f r x = f x := by
  apply circularMean_eq_of_harmonicOnNhd_closedBall
  exact hf.mono (Set.subset_univ _)

end PlaneFunctions

end J0RadialUniqueness
