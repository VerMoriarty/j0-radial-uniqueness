import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Exact rational bounds used in Proposition 4.2.

Only a cubic exponential partial sum and its proved Taylor remainder are
needed. There is no floating-point evaluation or native_decide certificate.
-/

namespace J0RadialUniqueness

/-- The cubic partial sum already exceeds two. -/
theorem exp_seven_tenths_gt_two : (2 : ℝ) < Real.exp (7 / 10 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (7 / 10 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A degree-two partial sum with its cubic remainder gives a rational upper bound. -/
theorem exp_seven_tenths_lt_two_hundred_three_hundredths :
    Real.exp (7 / 10 : ℝ) < (203 / 100 : ℝ) := by
  have h := Real.exp_bound' (x := (7 / 10 : ℝ))
    (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem exp_seven_fifths_eq_square :
    Real.exp (7 / 5 : ℝ) = Real.exp (7 / 10 : ℝ) ^ 2 := by
  calc
    Real.exp (7 / 5 : ℝ) = Real.exp ((7 / 10 : ℝ) + 7 / 10) := by
      congr 1
      norm_num
    _ = Real.exp (7 / 10 : ℝ) ^ 2 := by rw [Real.exp_add, pow_two]

theorem exp_seven_fifths_gt_four : (4 : ℝ) < Real.exp (7 / 5 : ℝ) := by
  have h := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 2)
    (Real.exp_pos (7 / 10 : ℝ)).le).mpr exp_seven_tenths_gt_two
  norm_num at h
  rwa [← exp_seven_fifths_eq_square] at h

theorem exp_seven_fifths_lt_rational_square :
    Real.exp (7 / 5 : ℝ) < (203 / 100 : ℝ) ^ 2 := by
  have h := (sq_lt_sq₀ (Real.exp_pos (7 / 10 : ℝ)).le
    (by norm_num : (0 : ℝ) ≤ 203 / 100)).mpr
      exp_seven_tenths_lt_two_hundred_three_hundredths
  rwa [← exp_seven_fifths_eq_square] at h

/-- The first numerical inequality in the quantitative separation proof. -/
theorem cosh_seven_fifths_lt_eleven_fifths :
    Real.cosh (7 / 5 : ℝ) < (11 / 5 : ℝ) := by
  have hinv : (Real.exp (7 / 5 : ℝ))⁻¹ < (4 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos (7 / 5 : ℝ)) (by norm_num)).mpr
      exp_seven_fifths_gt_four
  have hnegative : Real.exp (-(7 / 5 : ℝ)) < (1 / 4 : ℝ) := by
    simpa only [Real.exp_neg, one_div] using hinv
  rw [Real.cosh_eq]
  nlinarith [exp_seven_fifths_lt_rational_square]

/-- Squaring the strict lower bound at seven fifths proves the second inequality. -/
theorem exp_fourteen_fifths_gt_sixteen :
    (16 : ℝ) < Real.exp (14 / 5 : ℝ) := by
  have heq : Real.exp (14 / 5 : ℝ) = Real.exp (7 / 5 : ℝ) ^ 2 := by
    calc
      Real.exp (14 / 5 : ℝ) = Real.exp ((7 / 5 : ℝ) + 7 / 5) := by
        congr 1
        norm_num
      _ = Real.exp (7 / 5 : ℝ) ^ 2 := by rw [Real.exp_add, pow_two]
  have h := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 4)
    (Real.exp_pos (7 / 5 : ℝ)).le).mpr exp_seven_fifths_gt_four
  norm_num at h
  rwa [← heq] at h

/-- The square-root comparison only needs the exact library bound pi > 3. -/
theorem weighted_sqrt_eight_pi_gt_eleven_fifths :
    (11 / 5 : ℝ) < (8 / 17 : ℝ) * Real.sqrt (8 * Real.pi) := by
  have hs : (19 / 4 : ℝ) ^ 2 < 8 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hr : (19 / 4 : ℝ) < Real.sqrt (8 * Real.pi) := Real.lt_sqrt_of_sq_lt hs
  linarith

end J0RadialUniqueness
