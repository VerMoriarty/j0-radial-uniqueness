import Solutions.J0RadialUniqueness.FRightHalfPlane
import Solutions.J0RadialUniqueness.RealAxis
import Solutions.J0RadialUniqueness.ZeroFree

namespace J0RadialUniqueness

/-- Proposition 2.4, with all three localization lemmas proved. -/
theorem globalLocalization :
    GlobalLocalizationStatement := by
  intro z hz hJ
  have hnorm : 4 ≤ ‖z‖ := one_point_norm_ge_four z hz hJ
  have hsector : 0 < (z ^ 2).re := by
    by_contra! hc
    have hw : -z ^ 2 / 4 ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hz)) (by norm_num)
    have hwre : 0 ≤ (-z ^ 2 / 4).re := by
      simp only [Complex.div_ofNat_re, Complex.neg_re]
      linarith
    have he := F_rightHalfPlane _ hw hwre
    change 1 < ‖J0 z‖ at he
    rw [hJ, norm_one] at he
    exact lt_irrefl _ he
  have him : z.im ≠ 0 := by
    intro hc
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hc]
    have hzre : z.re ≠ 0 := by intro hh; apply hz; rw [← he, hh, Complex.ofReal_zero]
    have heR := noRealOnePoints z.re hzre
    rw [he, hJ, norm_one] at heR
    exact lt_irrefl _ heR
  exact ⟨hsector, him, hnorm⟩

end J0RadialUniqueness
