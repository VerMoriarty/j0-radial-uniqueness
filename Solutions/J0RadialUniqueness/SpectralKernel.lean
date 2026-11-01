import Solutions.J0RadialUniqueness.Series
import Mathlib.Tactic

/-! Exact algebraic bridges for the local two-radius theorem.

The multiplier below removes the double zero at the origin from the spherical
mean defect.  It is defined by the existing entire series `Q`, so its value at
zero does not use division by the spectral variable.

`sourceRootRatioSet` retains the source convention that only the denominator
must be nonzero.  Its comparison with `ratioSet` is restricted to nonzero ratios,
and in particular to the positive real ratios required by the paper.

No distributional kernel, Fourier identification, or local uniqueness theorem
is assumed or proved in this file.
-/

noncomputable section

namespace J0RadialUniqueness

/-- The normalized mean-defect multiplier `(J0 (r * ζ) - 1) / ζ^2`, extended at zero. -/
def meanDefectMultiplier (r : ℝ) (ζ : ℂ) : ℂ :=
  -(r : ℂ) ^ 2 / 4 * Q (-((r : ℂ) * ζ) ^ 2 / 4)

/-- The factorization holds at zero as well as at nonzero frequencies. -/
theorem J0_sub_one_eq_sq_mul_meanDefectMultiplier (r : ℝ) (ζ : ℂ) :
    J0 ((r : ℂ) * ζ) - 1 = ζ ^ 2 * meanDefectMultiplier r ζ := by
  rw [J0, F_sub_one]
  unfold meanDefectMultiplier
  ring

@[simp] theorem meanDefectMultiplier_zero (r : ℝ) :
    meanDefectMultiplier r 0 = -(r : ℂ) ^ 2 / 4 := by
  simp [meanDefectMultiplier]

theorem meanDefectMultiplier_zero_ne_zero (r : ℝ) (hr : r ≠ 0) :
    meanDefectMultiplier r 0 ≠ 0 := by
  rw [meanDefectMultiplier_zero]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hrC)) (by norm_num)

theorem meanDefectMultiplier_zero_ne_zero_of_pos (r : ℝ) (hr : 0 < r) :
    meanDefectMultiplier r 0 ≠ 0 :=
  meanDefectMultiplier_zero_ne_zero r hr.ne'

/-- Away from zero, removing the quadratic factor preserves exactly the one-points. -/
theorem meanDefectMultiplier_eq_zero_iff (r : ℝ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    meanDefectMultiplier r ζ = 0 ↔ J0 ((r : ℂ) * ζ) = 1 := by
  have hfactor := J0_sub_one_eq_sq_mul_meanDefectMultiplier r ζ
  constructor
  · intro hzero
    rw [hzero, mul_zero] at hfactor
    exact sub_eq_zero.mp hfactor
  · intro hone
    rw [hone, sub_self] at hfactor
    exact (mul_eq_zero.mp hfactor.symm).resolve_left (pow_ne_zero 2 hζ)

/-- Volchkov's source entire function in dimension two; its zero at zero is retained. -/
def sourceEta (ζ : ℂ) : ℂ := 1 - J0 ζ

@[simp] theorem sourceEta_zero : sourceEta 0 = 0 := by
  simp [sourceEta]

theorem sourceEta_eq_zero_iff (ζ : ℂ) : sourceEta ζ = 0 ↔ J0 ζ = 1 := by
  unfold sourceEta
  constructor
  · intro hzero
    exact (sub_eq_zero.mp hzero).symm
  · intro hone
    exact sub_eq_zero.mpr hone.symm

/-- The source root-ratio set: the denominator is nonzero, while the numerator may be zero. -/
def sourceRootRatioSet : Set ℂ :=
  {c | ∃ α β : ℂ, sourceEta α = 0 ∧ sourceEta β = 0 ∧ β ≠ 0 ∧ α / β = c}

/-- A nonzero ratio forces the source numerator to be nonzero as well. -/
theorem mem_sourceRootRatioSet_iff_of_ne_zero (c : ℂ) (hc : c ≠ 0) :
    c ∈ sourceRootRatioSet ↔ c ∈ ratioSet := by
  constructor
  · rintro ⟨α, β, hα, hβ, hβ0, hratio⟩
    have hα0 : α ≠ 0 := by
      intro hzero
      have hzeroRatio : (0 : ℂ) = c := by simpa [hzero] using hratio
      exact hc hzeroRatio.symm
    exact ⟨α, ⟨hα0, (sourceEta_eq_zero_iff α).mp hα⟩,
      β, ⟨hβ0, (sourceEta_eq_zero_iff β).mp hβ⟩, hratio⟩
  · rintro ⟨α, hα, β, hβ, hratio⟩
    exact ⟨α, β, (sourceEta_eq_zero_iff α).mpr hα.2,
      (sourceEta_eq_zero_iff β).mpr hβ.2, hβ.1, hratio⟩

/-- This is the comparison required for positive ratios of the two geometric radii. -/
theorem positive_mem_sourceRootRatioSet_iff_ratioSet (c : ℝ) (hc : 0 < c) :
    (c : ℂ) ∈ sourceRootRatioSet ↔ (c : ℂ) ∈ ratioSet := by
  apply mem_sourceRootRatioSet_iff_of_ne_zero
  exact_mod_cast hc.ne'

end J0RadialUniqueness
