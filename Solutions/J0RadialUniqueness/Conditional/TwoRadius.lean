import Definitions.J0RadialUniqueness.TwoRadius
import Solutions.J0RadialUniqueness.Conditional.Spectral

/-! The logical application in Corollary 6.4.
Both ray uniqueness and the cited Volchkov theorem remain explicit hypotheses.
This module does not claim an unconditional two-radius theorem. -/

namespace J0RadialUniqueness

/-- The paper's local application, conditional on its two substantive inputs. -/
theorem localTwoRadius_of_rayUniqueness_and_volchkov
    (hRay : RayUniqueness) (hVolchkov : VolchkovLocalStatement) :
    LocalTwoRadiusStatement := by
  intro r₁ r₂ R f hr₁ hr₂ hne hR hf hmean₁ hmean₂
  apply hVolchkov r₁ r₂ R f hr₁ hr₂ hR hf hmean₁ hmean₂
  apply not_mem_ratioSet_of_pos_ne_one hRay (div_pos hr₁ hr₂)
  intro hratio
  exact hne ((div_eq_one_iff_eq hr₂.ne').mp hratio)

/-- The same application with Theorem A as the explicitly supplied analytic premise. -/
theorem localTwoRadius_of_radialEscape_and_volchkov
    (hEscape : RadialEscape) (hVolchkov : VolchkovLocalStatement) :
    LocalTwoRadiusStatement :=
  localTwoRadius_of_rayUniqueness_and_volchkov
    (rayUniqueness_of_radialEscape hEscape) hVolchkov

end J0RadialUniqueness
