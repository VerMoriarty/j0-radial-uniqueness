import Definitions.J0RadialUniqueness.Analytic
import Solutions.J0RadialUniqueness.Constants

namespace J0RadialUniqueness

theorem kappa_pos : 0 < kappa :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem kappa_lt_quarter : kappa < (1 / 4 : ℝ) := by
  have h : Real.rpow 2 (-9 / 4 : ℝ) < Real.rpow 2 (-2 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have htwo : Real.rpow 2 (-2 : ℝ) = (1 / 4 : ℝ) := by norm_num
  exact h.trans_eq htwo

theorem kappa_div_lt_one_sixteenth {r : ℝ} (hr : 4 ≤ r) :
    kappa / r < (1 / 16 : ℝ) := by
  have hr0 : 0 < r := by linarith
  apply (div_lt_iff₀ hr0).2
  have hk := kappa_lt_quarter
  linarith

theorem weighted_derivative_lt_one_sixteenth {r d : ℝ}
    (hr : 4 ≤ r) (hd : d ≤ kappa / r ^ 2) : r * d < (1 / 16 : ℝ) := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hclear : d * r ^ 2 ≤ kappa := (le_div_iff₀ hr2).1 hd
  have hprod : r * d ≤ kappa / r := by
    apply (le_div_iff₀ hr0).2
    nlinarith only [hclear]
  exact hprod.trans_lt (kappa_div_lt_one_sixteenth hr)

end J0RadialUniqueness
