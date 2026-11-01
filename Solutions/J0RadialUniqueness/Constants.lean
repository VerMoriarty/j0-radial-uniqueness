import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Exact arithmetic and algebraic estimates used in Sections 4 and 5 of
`j0_radial_uniqueness.tex`.  These lemmas do not assume any Bessel identity.
-/

namespace J0RadialUniqueness

theorem separation_mass_constant :
    (1 / 6 : ℝ) * (17 / 16) ^ 2 * (257 / 240) ^ 2 < 11 / 50 := by
  norm_num

theorem radial_error_constant :
    (1 / 15 : ℝ) + (2 * (187 / 750) + (2 / 15) * (17 / 240)) /
      (1 - 17 / 240) < 31 / 50 := by
  norm_num

theorem radial_margin_identity :
    (7 / 5 : ℝ) - 1 / 2 - 31 / 50 = 7 / 25 := by
  norm_num

theorem radial_derivative_lower_bound {y e d : ℝ}
    (hy : 7 / 5 < y) (he : -(31 / 50) < e)
    (hd : d = y - 1 / 2 + e) : 7 / 25 < d := by
  linarith

theorem radial_derivative_lower_bound_of_abs {y e d : ℝ}
    (hy : 7 / 5 < y) (he : |e| < 31 / 50)
    (hd : d = y - 1 / 2 + e) : 7 / 25 < d := by
  exact radial_derivative_lower_bound hy (abs_lt.mp he).1 hd

theorem norm_bounds_of_norm_sub_one_lt {a : ℂ}
    (h : ‖a - 1‖ < (1 / 16 : ℝ)) :
    (15 / 16 : ℝ) < ‖a‖ ∧ ‖a‖ < (17 / 16 : ℝ) := by
  have hu : ‖a‖ ≤ ‖a - 1‖ + 1 := by
    calc
      ‖a‖ = ‖(a - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖a - 1‖ + 1 := by simp
  have hl : (1 : ℝ) ≤ ‖a - 1‖ + ‖a‖ := by
    calc
      (1 : ℝ) = ‖((1 : ℂ) - a) + a‖ := by simp
      _ ≤ ‖(1 : ℂ) - a‖ + ‖a‖ := norm_add_le _ _
      _ = ‖a - 1‖ + ‖a‖ := by rw [norm_sub_rev]
  constructor <;> linarith

theorem ne_zero_of_norm_sub_one_lt {a : ℂ}
    (h : ‖a - 1‖ < (1 / 16 : ℝ)) : a ≠ 0 := by
  intro ha
  subst a
  norm_num at h

theorem amplitude_ratio_lt {a b : ℝ}
    (ha : a < 17 / 16) (hb : 15 / 16 < b) : a / b < 17 / 15 := by
  have hb0 : 0 < b := by linarith
  apply (div_lt_iff₀ hb0).2
  linarith

theorem delta_lt_of_amplitudes {e a b : ℝ}
    (he0 : 0 ≤ e) (he : e < 1 / 16)
    (ha : a < 17 / 16) (hb : 15 / 16 < b) :
    e * (a / b) < 17 / 240 := by
  have hab := amplitude_ratio_lt ha hb
  calc
    e * (a / b) ≤ e * (17 / 15) :=
      mul_le_mul_of_nonneg_left hab.le he0
    _ < (1 / 16 : ℝ) * (17 / 15) :=
      mul_lt_mul_of_pos_right he (by norm_num)
    _ = 17 / 240 := by norm_num

theorem weighted_delta_lt_of_amplitudes {r e a b : ℝ}
    (hr : 0 ≤ r) (he : 0 ≤ e) (hre : r * e < 11 / 50)
    (ha : a < 17 / 16) (hb : 15 / 16 < b) :
    r * (e * (a / b)) < 187 / 750 := by
  have hab := amplitude_ratio_lt ha hb
  calc
    r * (e * (a / b)) = (r * e) * (a / b) := by ring
    _ ≤ (r * e) * (17 / 15) :=
      mul_le_mul_of_nonneg_left hab.le (mul_nonneg hr he)
    _ < (11 / 50 : ℝ) * (17 / 15) :=
      mul_lt_mul_of_pos_right hre (by norm_num)
    _ = 187 / 750 := by norm_num

theorem logarithmic_amplitude_bound {z a b : ℂ}
    (ha : (15 / 16 : ℝ) < ‖a‖)
    (hb : ‖z‖ * ‖b‖ < (1 / 16 : ℝ)) :
    ‖z * b / a‖ < (1 / 15 : ℝ) := by
  rw [norm_div, norm_mul]
  have ha0 : 0 < ‖a‖ := by linarith
  apply (div_lt_iff₀ ha0).2
  linarith

theorem one_add_ne_zero_of_norm_lt {d : ℂ}
    (hd : ‖d‖ < (17 / 240 : ℝ)) : 1 + d ≠ 0 := by
  intro hzero
  have hd' : d = -1 := by linear_combination hzero
  rw [hd'] at hd
  norm_num at hd

theorem radial_error_bound {a b d q : ℝ}
    (ha : a ≤ 1 / 15) (hb : b ≤ 1 / 15)
    (hd0 : 0 ≤ d) (hd : d ≤ 17 / 240)
    (hq : q ≤ 187 / 750) :
    a + (2 * q + (a + b) * d) / (1 - d) < 31 / 50 := by
  have hab : a + b ≤ 2 / 15 := by linarith
  have hprod : (a + b) * d ≤ (2 / 15 : ℝ) * (17 / 240) := by
    calc
      (a + b) * d ≤ (2 / 15 : ℝ) * d :=
        mul_le_mul_of_nonneg_right hab hd0
      _ ≤ (2 / 15 : ℝ) * (17 / 240) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
  have hnum : 2 * q + (a + b) * d ≤
      2 * (187 / 750) + (2 / 15 : ℝ) * (17 / 240) := by
    linarith
  have hden : (1 - 17 / 240 : ℝ) ≤ 1 - d := by linarith
  have hdiv := div_le_div₀ (by norm_num :
      (0 : ℝ) ≤ 2 * (187 / 750) + (2 / 15) * (17 / 240))
      hnum (by norm_num : (0 : ℝ) < 1 - 17 / 240) hden
  exact lt_of_le_of_lt (add_le_add ha hdiv) radial_error_constant

end J0RadialUniqueness
