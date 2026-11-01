import Solutions.J0RadialUniqueness.Main
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Filter
open scoped Topology

namespace J0RadialUniqueness

theorem J0_hasDerivAt (z : ℂ) :
    HasDerivAt J0 (deriv F (-z ^ 2 / 4) * (-z / 2)) z := by
  have harg : HasDerivAt (fun v : ℂ => -v ^ 2 / 4) (-z / 2) z := by
    convert! (((hasDerivAt_id z).pow 2).neg).div_const (4 : ℂ) using 1
    simp only [id_eq, Pi.pow_apply]
    ring
  exact (F_differentiable (-z ^ 2 / 4)).hasDerivAt.comp z harg

theorem J0_differentiable : Differentiable ℂ J0 :=
  fun z => (J0_hasDerivAt z).differentiableAt

theorem J0_analyticAt (z : ℂ) : AnalyticAt ℂ J0 z :=
  (J0_differentiable.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)

/-- The paper's strictly positive radial derivative makes every nonzero
one-point simple, including points outside the principal quadrant. -/
theorem J0_deriv_ne_zero_at_one_point {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) :
    deriv J0 z ≠ 0 := by
  intro hzero
  have hj : HasDerivAt J0 0 z := by
    simpa only [hzero] using (J0_differentiable z).hasDerivAt
  have hpath : HasDerivAt (fun t : ℝ => J0 ((t : ℂ) * z)) 0 1 := by
    have hj' : HasDerivAt J0 0 ((1 : ℂ) * z) := by simpa only [one_mul] using hj
    have hp := (hj'.comp (1 : ℂ) ((hasDerivAt_id (1 : ℂ)).mul_const z)).comp_ofReal
    simpa only [Function.comp_def, id_eq, Complex.ofReal_one, one_mul, zero_mul] using hp
  have hlog : HasDerivAt (rayLogNorm z) 0 1 := by
    have hn : J0 (((1 : ℝ) : ℂ) * z) ≠ 0 := by simp [hJ]
    convert! hasDerivAt_log_norm hpath hn using 1 <;> simp only [zero_div, Complex.zero_re]
  have hl := globalLocalization z hz hJ
  have hsector := quadrantRep_in_principalSector z hl.1 hl.2.1
  have hpoint := J0_quadrantRep z hJ
  have heq : rayLogNorm (quadrantRep z) =ᶠ[𝓝 (1 : ℝ)] rayLogNorm z := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    unfold rayLogNorm
    rw [norm_J0_mul_quadrantRep t ht.le z]
  have hzrep := hlog.congr_of_eventuallyEq heq
  have hb := ((paper_5_1 (quadrantRep z) hpoint hsector).1 1 le_rfl).2
  unfold rayLogDerivative at hb
  rw [hzrep.deriv] at hb
  norm_num at hb

end J0RadialUniqueness
