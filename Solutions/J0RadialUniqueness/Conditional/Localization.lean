import Definitions.J0RadialUniqueness.Analytic
import Solutions.J0RadialUniqueness.ZeroFree
import Solutions.J0RadialUniqueness.Symmetry

noncomputable section

namespace J0RadialUniqueness

/-- Exact reduction of Proposition 2.4 to Lemmas 2.1--2.2; Lemma 2.3 is closed. -/
theorem globalLocalization_of_halfPlane_and_real
    (hF : FRightHalfPlaneStatement) (hR : NoRealOnePointsStatement) :
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
    have he := hF _ hw hwre
    change 1 < ‖J0 z‖ at he
    rw [hJ, norm_one] at he
    exact lt_irrefl _ he
  have him : z.im ≠ 0 := by
    intro hc
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hc]
    have hzre : z.re ≠ 0 := by intro hh; apply hz; rw [← he, hh, Complex.ofReal_zero]
    have heR := hR z.re hzre
    rw [he, hJ, norm_one] at heR
    exact lt_irrefl _ heR
  exact ⟨hsector, him, hnorm⟩

/-- The global theorem follows from actual localization and principal-sector escape. -/
theorem radialEscape_of_principal
    (hloc : GlobalLocalizationStatement) (hprincipal : PrincipalRadialEscapeStatement) :
    RadialEscape := by
  intro z hz hJ c hc
  have hl := hloc z hz hJ
  have hp := quadrantRep_in_principalSector z hl.1 hl.2.1
  have hj := J0_quadrantRep z hJ
  have he := (hprincipal (quadrantRep z) hj hp).2 c hc
  rwa [norm_J0_mul_quadrantRep c (by linarith) z] at he

end J0RadialUniqueness
