import Solutions.J0RadialUniqueness.BesselPolynomialExpansion
import Solutions.J0RadialUniqueness.SpectralCosine
import Solutions.J0RadialUniqueness.EvenPoissonInjectivity

/-! The actual Poisson transform of the convergent cosine root series.
Countability follows from the proved finite-box exhaustion. Dominated
convergence uses the actual compact-interval majorant, so the Bessel series
is identified with a genuine circle integral before applying Abel inversion. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

namespace J0RadialUniqueness

instance rightOnePoint_countable : Countable RightOnePoint := by
  apply Set.countable_univ_iff.mp
  have heq : (Set.univ : Set RightOnePoint) = ⋃ n : ℕ, (rightOnePointBoxFinset n : Set RightOnePoint) := by
    ext z
    constructor
    · intro _
      obtain ⟨n, hn⟩ := rightOnePointBoxFinset_exhausts z
      exact mem_iUnion.mpr ⟨n, hn⟩
    · intro _
      exact mem_univ _
  rw [heq]
  exact Set.countable_iUnion fun n => (rightOnePointBoxFinset n).finite_toSet.countable

theorem evenPoissonTransform_cosine (nu : ℂ) (t : ℝ) :
    evenPoissonTransform (fun x : ℝ => Complex.cos (nu * (x : ℂ))) t = J0 ((t : ℂ) * nu) := by
  change circularMean (spectralCosine nu) t 0 = _
  rw [circularMean_spectralCosine, spectralCosine_zero, one_mul]

theorem besselCosineSeries_even (M : ℕ) : Function.Even (besselCosineSeries M) := by
  intro x
  unfold besselCosineSeries
  apply tsum_congr
  intro z
  simp only [Complex.ofReal_neg, mul_neg, Complex.cos_neg]

theorem evenPoissonTransform_besselCosineSeries_eq_radial (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    evenPoissonTransform (besselCosineSeries M) t = besselRadialRootSeries M t := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMT : (1 : ℝ) < 2 * M - 1 := by linarith
  let B : RightOnePoint → ℝ := fun z =>
    (4 : ℝ) ^ (1 : ℝ) * (‖besselResidueCoefficient M z‖ * ‖(z : ℂ)‖ ^ (1 : ℝ))
  have hB : Summable B := (besselCosineSeries_compact_majorant M (T := 1) (by norm_num) hMT).1
  have hx (θ : ℝ) : t * Real.cos θ ∈ Icc (-1 : ℝ) 1 := by
    have ha : |t * Real.cos θ| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ), ht.1, ht.2]
    exact abs_le.mp ha
  have hmajor (z : RightOnePoint) (θ : ℝ) :
      ‖besselResidueCoefficient M z * Complex.cos ((z : ℂ) * ((t * Real.cos θ : ℝ) : ℂ))‖ ≤ B z := by
    have hh := norm_cos_one_point_real_mul_le z.val.property.1 z.val.property.2
      (show (0 : ℝ) ≤ 1 by norm_num) (abs_le.mpr (hx θ))
    rw [norm_mul]
    calc
      _ ≤ ‖besselResidueCoefficient M z‖ *
          ((4 : ℝ) ^ (1 : ℝ) * ‖(z : ℂ)‖ ^ (1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = B z := by dsimp only [B]; ring
  have hsum : HasSum
      (fun z : RightOnePoint => ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        besselResidueCoefficient M z * Complex.cos ((z : ℂ) * ((t * Real.cos θ : ℝ) : ℂ)))
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, besselCosineSeries M (t * Real.cos θ)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (F := fun z : RightOnePoint => fun θ : ℝ => besselResidueCoefficient M z *
        Complex.cos ((z : ℂ) * ((t * Real.cos θ : ℝ) : ℂ)))
      (f := fun θ : ℝ => besselCosineSeries M (t * Real.cos θ)) (fun z (_ : ℝ) => B z)
    · intro z
      exact (by fun_prop : Continuous (fun θ : ℝ => besselResidueCoefficient M z *
        Complex.cos ((z : ℂ) * ((t * Real.cos θ : ℝ) : ℂ)))).aestronglyMeasurable
    · intro z
      exact Eventually.of_forall fun θ _ => hmajor z θ
    · exact Eventually.of_forall fun _ _ => hB
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ _ =>
        (besselCosineSeries_summable M (T := 1) (by norm_num) hMT (hx θ)).hasSum
  have heach (z : RightOnePoint) : ((2 * Real.pi)⁻¹ : ℝ) •
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        besselResidueCoefficient M z * Complex.cos ((z : ℂ) * ((t * Real.cos θ : ℝ) : ℂ))) =
      besselResidueCoefficient M z * J0 ((t : ℂ) * (z : ℂ)) := by
    calc
      _ = evenPoissonTransform (fun x : ℝ =>
          besselResidueCoefficient M z * Complex.cos ((z : ℂ) * (x : ℂ))) t :=
        (evenPoissonTransform_eq_integral _ _).symm
      _ = _ := by rw [evenPoissonTransform_const_mul, evenPoissonTransform_cosine]
  have hscaled := hsum.const_smul (((2 * Real.pi)⁻¹ : ℝ))
  simp_rw [heach] at hscaled
  rw [← evenPoissonTransform_eq_integral] at hscaled
  exact hscaled.unique (besselRadialRootSeries_summable M hM ht).hasSum

end J0RadialUniqueness
