import Solutions.J0RadialUniqueness.BesselCosinePoisson
import Solutions.J0RadialUniqueness.BesselBiorthogonality
import Mathlib.Tactic

/-! Coefficient isolation for the actual J₀ one-point series. The weighted
summability condition is an explicit intermediate analytic condition. Under
that condition, the proved actual J₀ bound and the continuous dual mode give
an integrable summable majorant. Dominated convergence and the actual Green
pairings then isolate each coefficient; no completeness theorem is assumed. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace J0RadialUniqueness

def rootBesselSeries (a : RightOnePoint → ℂ) (t : ℝ) : ℂ :=
  ∑' ν : RightOnePoint, a ν * J0 ((t : ℂ) * (ν : ℂ))

theorem rootBesselSeries_summable {a : RightOnePoint → ℂ}
    (ha : Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun ν : RightOnePoint => a ν * J0 ((t : ℂ) * (ν : ℂ))) := by
  apply Summable.of_norm_bounded (ha.mul_left 4)
  intro ν
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (norm_J0_one_point_scale_le ν.val.property.1 ν.val.property.2 ht)
    (norm_nonneg _)).trans_eq (by ring)

theorem rootBesselTerm_dual_integral (a : RightOnePoint → ℂ)
    (σ ν : RightOnePoint) :
    (∫ s : ℝ in (0 : ℝ)..1,
      (a ν * J0 ((s : ℂ) * (ν : ℂ))) * volchkovDualMode σ s) =
      a ν * (∫ s : ℝ in (0 : ℝ)..1, helmholtzP ν s * volchkovDualMode σ s) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [helmholtzP_eq_J0]
  ring

theorem rootBesselTerm_dual_integral_off_diagonal (a : RightOnePoint → ℂ)
    (σ ν : RightOnePoint) (hνσ : ν ≠ σ) :
    (∫ s : ℝ in (0 : ℝ)..1,
      (a ν * J0 ((s : ℂ) * (ν : ℂ))) * volchkovDualMode σ s) = 0 := by
  rw [rootBesselTerm_dual_integral,
    volchkovDualMode_orthogonal σ.val.property.2 ν.val.property.2, mul_zero]
  intro heq
  exact hνσ (rightOnePoint_sq_injective heq.symm)

theorem rootBesselTerm_dual_integral_diagonal (a : RightOnePoint → ℂ) (σ : RightOnePoint) :
    (∫ s : ℝ in (0 : ℝ)..1,
      (a σ * J0 ((s : ℂ) * (σ : ℂ))) * volchkovDualMode σ s) =
      a σ * (-deriv J0 (σ : ℂ) / (Real.pi : ℂ)) := by
  rw [rootBesselTerm_dual_integral, volchkovDualMode_diagonal]

theorem volchkovDualMode_unit_interval_bound (σ : RightOnePoint) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1, ‖volchkovDualMode σ s‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (continuous_volchkovDualMode (σ : ℂ)).continuousOn
  exact ⟨max K 0, le_max_right _ _, fun s hs => (hK s hs).trans (le_max_left _ _)⟩

/-- The actual dominated integral/sum exchange. Its majorant is built from
the weighted coefficient norm and a genuine compact-interval dual bound. -/
theorem rootBesselSeries_dual_integral_hasSum {a : RightOnePoint → ℂ}
    (ha : Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖))
    (σ : RightOnePoint) :
    HasSum (fun ν : RightOnePoint => ∫ s : ℝ in (0 : ℝ)..1,
      (a ν * J0 ((s : ℂ) * (ν : ℂ))) * volchkovDualMode σ s)
      (∫ s : ℝ in (0 : ℝ)..1, rootBesselSeries a s * volchkovDualMode σ s) := by
  obtain ⟨K, hK, hbound⟩ := volchkovDualMode_unit_interval_bound σ
  let B : RightOnePoint → ℝ := fun ν => (4 * K) * (‖a ν‖ * ‖(ν : ℂ)‖)
  have hB : Summable B := ha.mul_left (4 * K)
  have hunit {s : ℝ} (hs : s ∈ Ι (0 : ℝ) 1) : s ∈ Icc (0 : ℝ) 1 := by
    apply Ioc_subset_Icc_self
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun ν (_s : ℝ) => B ν)
  · intro ν
    have hJ : Continuous (fun s : ℝ => J0 ((s : ℂ) * (ν : ℂ))) :=
      J0_differentiable.continuous.comp (Complex.continuous_ofReal.mul continuous_const)
    exact ((continuous_const.mul hJ).mul
      (continuous_volchkovDualMode (σ : ℂ))).aestronglyMeasurable
  · intro ν
    exact Eventually.of_forall fun s hs => by
      have hs' := hunit hs
      have hJ := norm_J0_one_point_scale_le ν.val.property.1 ν.val.property.2 hs'
      have hd := hbound s hs'
      simp only [norm_mul]
      calc
        ‖a ν‖ * ‖J0 ((s : ℂ) * (ν : ℂ))‖ * ‖volchkovDualMode σ s‖ ≤
            (‖a ν‖ * (4 * ‖(ν : ℂ)‖)) * K := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)) hd
            (norm_nonneg _) (mul_nonneg (norm_nonneg _) (by positivity))
        _ = B ν := by dsimp only [B]; ring
  · exact Eventually.of_forall fun _ _ => hB
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun s hs =>
      (rootBesselSeries_summable ha (hunit hs)).hasSum.mul_right (volchkovDualMode σ s)

/-- Exact coefficient extraction by the actual boundary-conditioned dual.
The diagonal normalizer is the derivative of the genuine J₀ series. -/
theorem rootBesselSeries_dual_pairing {a : RightOnePoint → ℂ}
    (ha : Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖))
    (σ : RightOnePoint) :
    (∫ s : ℝ in (0 : ℝ)..1, rootBesselSeries a s * volchkovDualMode σ s) =
      a σ * (-deriv J0 (σ : ℂ) / (Real.pi : ℂ)) := by
  have hsum := rootBesselSeries_dual_integral_hasSum ha σ
  have hsingle : HasSum (fun ν : RightOnePoint => ∫ s : ℝ in (0 : ℝ)..1,
      (a ν * J0 ((s : ℂ) * (ν : ℂ))) * volchkovDualMode σ s)
      (∫ s : ℝ in (0 : ℝ)..1,
        (a σ * J0 ((s : ℂ) * (σ : ℂ))) * volchkovDualMode σ s) :=
    hasSum_single σ (fun ν hν => rootBesselTerm_dual_integral_off_diagonal a σ ν hν)
  exact (hsum.unique hsingle).trans (rootBesselTerm_dual_integral_diagonal a σ)

/-- Vanishing of the actual J₀ root series on [0,1] forces every coefficient
to vanish under the stated weighted absolute summability condition. -/
theorem rootBesselSeries_coefficients_eq_zero {a : RightOnePoint → ℂ}
    (ha : Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖))
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, rootBesselSeries a t = 0) :
    ∀ σ : RightOnePoint, a σ = 0 := by
  intro σ
  have hI : (∫ s : ℝ in (0 : ℝ)..1,
      rootBesselSeries a s * volchkovDualMode σ s) = 0 := by
    calc
      _ = ∫ _s : ℝ in (0 : ℝ)..1, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        have hs' : s ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
        rw [hzero s hs', zero_mul]
      _ = 0 := by simp
  have hn : (-deriv J0 (σ : ℂ) / (Real.pi : ℂ)) ≠ 0 := by
    rw [← volchkovDualMode_diagonal]
    exact volchkovDualMode_diagonal_ne_zero σ.val.property.1 σ.val.property.2
  rw [rootBesselSeries_dual_pairing ha σ] at hI
  exact (mul_eq_zero.mp hI).resolve_right hn

end J0RadialUniqueness
