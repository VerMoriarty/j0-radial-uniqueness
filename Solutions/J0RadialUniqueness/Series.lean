import Definitions.J0RadialUniqueness.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

theorem fTerm_summable (w : ℂ) : Summable (fTerm w) := by
  apply (Real.summable_pow_div_factorial ‖w‖).of_norm_bounded
  intro n
  have hp : (0 : ℝ) < n.factorial := by positivity
  have hge : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  simp only [fTerm, norm_div, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _) hp
    (by nlinarith)

theorem qTerm_summable (w : ℂ) :
    Summable (fun n : ℕ => w ^ n / ((n + 1).factorial : ℂ) ^ 2) := by
  apply (Real.summable_pow_div_factorial ‖w‖).of_norm_bounded
  intro n
  have hp : (0 : ℝ) < n.factorial := by positivity
  have hge : (1 : ℝ) ≤ (n + 1).factorial := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hle : (n.factorial : ℝ) ≤ (n + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 1)
  simp only [norm_div, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _) hp
    (by nlinarith)

theorem J0_series (z : ℂ) :
    J0 z = ∑' n : ℕ, (-1 : ℂ) ^ n * z ^ (2 * n) /
      (4 ^ n * (n.factorial : ℂ) ^ 2) := by
  unfold J0 F fTerm
  apply tsum_congr
  intro n
  rw [div_pow, neg_pow, pow_mul]
  ring

@[simp] theorem F_zero : F 0 = 1 := by
  rw [F, tsum_eq_single 0]
  · simp [fTerm]
  · intro n hn
    simp [fTerm, zero_pow hn]

@[simp] theorem Q_zero : Q 0 = 1 := by
  rw [Q, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

@[simp] theorem J0_zero : J0 0 = 1 := by simp [J0]

theorem F_sub_one (w : ℂ) : F w - 1 = w * Q w := by
  have hs := (fTerm_summable w).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, fTerm, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one] at hs
  have ht : (∑' n : ℕ, w ^ (n + 1) / ((n + 1).factorial : ℂ) ^ 2) =
      w * Q w := by
    rw [Q, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [pow_succ]
    ring
  change (1 : ℂ) + (∑' n : ℕ, w ^ (n + 1) / ((n + 1).factorial : ℂ) ^ 2) = F w at hs
  rw [ht] at hs
  linear_combination -hs

@[simp] theorem J0_neg (z : ℂ) : J0 (-z) = J0 z := by simp [J0]

theorem fTerm_conj (w : ℂ) (n : ℕ) :
    fTerm (starRingEnd ℂ w) n = starRingEnd ℂ (fTerm w n) := by
  simp [fTerm]

theorem F_conj (w : ℂ) : F (starRingEnd ℂ w) = starRingEnd ℂ (F w) := by
  unfold F
  rw [Complex.conj_tsum]
  exact tsum_congr (fTerm_conj w)

theorem J0_conj (z : ℂ) : J0 (starRingEnd ℂ z) = starRingEnd ℂ (J0 z) := by
  unfold J0
  rw [← F_conj]
  congr 1
  have hc4 : starRingEnd ℂ (4 : ℂ) = 4 := by apply Complex.ext <;> norm_num
  simp [hc4]

end J0RadialUniqueness
