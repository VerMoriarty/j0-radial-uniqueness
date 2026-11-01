import Solutions.J0RadialUniqueness.LaplaceKernel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

/-- A branch-consistent inverse-square-root estimate along the actual line segment. -/
theorem inverse_sqrt_sub_one_bound (ξ : ℂ) (B : ℝ)
    (hbranch : ∀ s ∈ Set.Icc (0 : ℝ) 1, 1 + (s : ℂ) * ξ ∈ Complex.slitPlane)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖Complex.cpow (1 + (s : ℂ) * ξ) (-3 / 2 : ℂ)‖ ≤ B) :
    ‖Complex.cpow (1 + ξ) (-1 / 2 : ℂ) - 1‖ ≤ (‖ξ‖ / 2) * B := by
  let g : ℝ → ℂ := fun s => Complex.cpow (1 + (s : ℂ) * ξ) (-1 / 2 : ℂ)
  let g' : ℝ → ℂ := fun s =>
    (-1 / 2 : ℂ) * Complex.cpow (1 + (s : ℂ) * ξ) (-3 / 2 : ℂ) * ξ
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' s) s := by
    intro s hs
    have h := (((hasDerivAt_id (s : ℂ)).mul_const ξ).const_add 1).cpow_const
      (c := (-1 / 2 : ℂ)) (hbranch s hs)
    have hh := h.comp_ofReal
    change HasDerivAt g
      ((-1 / 2 : ℂ) * Complex.cpow (1 + (s : ℂ) * ξ) ((-1 / 2 : ℂ) - 1) *
        (1 * ξ)) s at hh
    simpa only [one_mul, show (-1 / 2 : ℂ) - 1 = -3 / 2 by norm_num] using hh
  have hnorm : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖g' s‖ ≤ (‖ξ‖ / 2) * B := by
    intro s hs
    dsimp only [g']
    rw [norm_mul, norm_mul]
    norm_num
    have hb := hbound s ⟨hs.1, hs.2.le⟩
    norm_num [Complex.cpow_eq_pow] at hb
    calc
      _ ≤ (1 / 2 : ℝ) * B * ‖ξ‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (by norm_num)) (norm_nonneg _)
      _ = _ := by ring
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs => (hd s hs).hasDerivWithinAt) hnorm
  simpa [g] using hm

end J0RadialUniqueness
