import Definitions.J0RadialUniqueness.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The actual zeroth and first moments of the paper's Laplace density. -/

noncomputable section

open MeasureTheory Set

namespace J0RadialUniqueness

theorem muDensity_integrableOn : IntegrableOn muDensity (Ioi (0 : ℝ)) volume := by
  have h : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * Real.rpow t (-1 / 2 : ℝ)) (Ioi 0) volume := by
    simpa only [Real.rpow_eq_pow, show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] using
      (Real.GammaIntegral_convergent (s := (1 / 2 : ℝ)) (by norm_num))
  change IntegrableOn (fun t : ℝ =>
    Real.exp (-t) * Real.rpow t (-1 / 2 : ℝ) / Real.sqrt Real.pi) (Ioi 0) volume
  exact h.div_const (Real.sqrt Real.pi)

theorem firstMoment_density_eq {t : ℝ} (ht : 0 < t) :
    t * muDensity t =
      Real.exp (-t) * Real.rpow t (1 / 2 : ℝ) / Real.sqrt Real.pi := by
  have hp : Real.rpow t (1 / 2 : ℝ) = Real.rpow t (-1 / 2 : ℝ) * t := by
    simpa only [Real.rpow_eq_pow, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using
      (Real.rpow_add_one (ne_of_gt ht) (-1 / 2 : ℝ))
  rw [muDensity, hp]
  ring

theorem firstMoment_integrableOn :
    IntegrableOn (fun t => t * muDensity t) (Ioi (0 : ℝ)) volume := by
  have h : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * Real.rpow t (1 / 2 : ℝ)) (Ioi 0) volume := by
    simpa only [Real.rpow_eq_pow, show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] using
      (Real.GammaIntegral_convergent (s := (3 / 2 : ℝ)) (by norm_num))
  have hdiv : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * Real.rpow t (1 / 2 : ℝ) / Real.sqrt Real.pi)
      (Ioi 0) volume := h.div_const (Real.sqrt Real.pi)
  apply hdiv.congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact (firstMoment_density_eq ht).symm

theorem muDensity_integral : (∫ t in Ioi (0 : ℝ), muDensity t) = 1 := by
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hg : (∫ t : ℝ in Ioi 0,
      Real.exp (-t) * Real.rpow t (-1 / 2 : ℝ)) = Real.Gamma (1 / 2) := by
    simpa only [Real.rpow_eq_pow, show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] using
      (Real.Gamma_eq_integral (s := (1 / 2 : ℝ)) (by norm_num)).symm
  change (∫ t : ℝ in Ioi 0,
    (Real.exp (-t) * Real.rpow t (-1 / 2 : ℝ)) / Real.sqrt Real.pi) = 1
  rw [integral_div, hg, Real.Gamma_one_half_eq, div_self hs]

theorem firstMoment_integral :
    (∫ t in Ioi (0 : ℝ), t * muDensity t) = 1 / 2 := by
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hg : (∫ t : ℝ in Ioi 0,
      Real.exp (-t) * Real.rpow t (1 / 2 : ℝ)) = Real.Gamma (3 / 2) := by
    simpa only [Real.rpow_eq_pow, show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] using
      (Real.Gamma_eq_integral (s := (3 / 2 : ℝ)) (by norm_num)).symm
  have hγ : Real.Gamma (3 / 2) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    calc
      Real.Gamma (3 / 2) = Real.Gamma ((1 / 2 : ℝ) + 1) := by norm_num
      _ = (1 / 2 : ℝ) * Real.Gamma (1 / 2) :=
        Real.Gamma_add_one (by norm_num)
      _ = (1 / 2 : ℝ) * Real.sqrt Real.pi := by rw [Real.Gamma_one_half_eq]
  calc
    (∫ t in Ioi (0 : ℝ), t * muDensity t) =
        ∫ t : ℝ in Ioi 0,
          Real.exp (-t) * Real.rpow t (1 / 2 : ℝ) / Real.sqrt Real.pi := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact firstMoment_density_eq ht
    _ = Real.Gamma (3 / 2) / Real.sqrt Real.pi := by rw [integral_div, hg]
    _ = 1 / 2 := by rw [hγ, mul_div_cancel_right₀ _ hs]

theorem mu_moments : MuMomentsStatement :=
  ⟨muDensity_integrableOn, firstMoment_integrableOn,
    muDensity_integral, firstMoment_integral⟩

end J0RadialUniqueness
