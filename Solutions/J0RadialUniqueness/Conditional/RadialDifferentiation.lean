import Solutions.J0RadialUniqueness.AmplitudeDomain
import Solutions.J0RadialUniqueness.BranchGeometry
import Solutions.J0RadialUniqueness.LogNorm
import Solutions.J0RadialUniqueness.Conditional.RaySeparation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

noncomputable section
open scoped Topology

namespace J0RadialUniqueness

def radialModel (w : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (w - (Real.pi : ℂ) / 4) -
    (1 / 2 : ℂ) * Complex.log (2 * (Real.pi : ℂ) * w)) * AMinus w * (1 + delta w)

theorem radialModel_eq_of_factorization (hfact : FactorizationStatement)
    {w : ℂ} (hw : w ∈ amplitudeDomain) : radialModel w = J0 w := by
  have hw0 := rightHalfPlane_ne_zero hw.1
  have hn : 2 * (Real.pi : ℂ) * w ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hw0
  rw [hfact w hw]
  unfold radialModel
  rw [mul_comm (1 / 2 : ℂ) (Complex.log (2 * (Real.pi : ℂ) * w))]
  rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hn, Complex.exp_sub]
  ring

theorem J0_hasDerivAt_of_factorization (hfact : FactorizationStatement)
    {w : ℂ} (hw : w ∈ amplitudeDomain) (hd : 1 + delta w ≠ 0) :
    HasDerivAt J0
      (J0 w * (-Complex.I - 1 / (2 * w) + deriv AMinus w / AMinus w +
        deriv delta w / (1 + delta w))) w := by
  have hw0 := rightHalfPlane_ne_zero hw.1
  have hA := (AMinus_hasDerivAt hw.1).differentiableAt.hasDerivAt
  have hD := (delta_differentiableAt hw).hasDerivAt
  have hAn : AMinus w ≠ 0 := (mul_ne_zero_iff.mp hw.2).2
  have hslit : 2 * (Real.pi : ℂ) * w ∈ Complex.slitPlane := by
    change 0 < (2 * (Real.pi : ℂ) * w).re ∨ (2 * (Real.pi : ℂ) * w).im ≠ 0
    left
    have hre : (2 * (Real.pi : ℂ) * w).re = 2 * Real.pi * w.re := by simp
    rw [hre]
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hw.1
  have hlog := ((hasDerivAt_id w).const_mul (2 * (Real.pi : ℂ))).clog hslit
  have harg : HasDerivAt
      (fun v : ℂ => -Complex.I * (v - (Real.pi : ℂ) / 4) -
        (1 / 2 : ℂ) * Complex.log (2 * (Real.pi : ℂ) * v))
      (-Complex.I - 1 / (2 * w)) w := by
    convert! (((hasDerivAt_id w).sub_const ((Real.pi : ℂ) / 4)).const_mul
      (-Complex.I)).sub (hlog.const_mul (1 / 2 : ℂ)) using 1
    simp only [id_eq]
    field_simp [hw0, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hm := (harg.cexp.mul hA).mul (hD.const_add 1)
  have hm' : HasDerivAt radialModel
      (radialModel w * (-Complex.I - 1 / (2 * w) + deriv AMinus w / AMinus w +
        deriv delta w / (1 + delta w))) w := by
    convert! hm using 1
    unfold radialModel
    simp only [Pi.mul_apply]
    field_simp [hAn, hd]
    <;> ring
  have heq : J0 =ᶠ[𝓝 w] radialModel := by
    filter_upwards [amplitudeDomain_isOpen.mem_nhds hw] with v hv
    exact (radialModel_eq_of_factorization hfact hv).symm
  rw [radialModel_eq_of_factorization hfact hw] at hm'
  exact hm'.congr_of_eventuallyEq heq

/-- Ordinary real derivatives, including at tau=1; no one-sided derivative is substituted. -/
theorem radialDerivativeDecomposition_of_factorization_and_ray
    (hfact : FactorizationStatement) (hray : RaySeparationStatement) :
    RadialDerivativeDecompositionStatement := by
  intro z hJ hz τ hτ
  let w : ℂ := (τ : ℂ) * z
  obtain ⟨hw, hd, _, hJn⟩ := hray z hJ hz τ hτ
  have hJn' : J0 w ≠ 0 := hJn
  have hdn := one_add_ne_zero_of_norm_lt hd
  let L : ℂ := -Complex.I - 1 / (2 * w) + deriv AMinus w / AMinus w +
    deriv delta w / (1 + delta w)
  have hcomplex : HasDerivAt J0 (J0 w * L) w :=
    J0_hasDerivAt_of_factorization hfact hw hdn
  have hpath : HasDerivAt (fun t : ℝ => J0 ((t : ℂ) * z)) (J0 w * L * z) τ := by
    simpa only [Function.comp_def, id_eq, one_mul] using
      (hcomplex.comp (τ : ℂ) ((hasDerivAt_id (τ : ℂ)).mul_const z)).comp_ofReal
  have hlog : HasDerivAt (rayLogNorm z) (L * z).re τ := by
    have h := hasDerivAt_log_norm hpath hJn
    change HasDerivAt (rayLogNorm z) (J0 w * L * z / J0 w).re τ at h
    convert! h using 1
    congr 1
    field_simp [hJn']
  refine ⟨hlog.differentiableAt, ?_⟩
  change τ * deriv (rayLogNorm z) τ = _
  rw [hlog.deriv]
  have hw0 : w ≠ 0 := rightHalfPlane_ne_zero hw.1
  have halg : w * L = -Complex.I * w - 1 / 2 +
      (w * deriv AMinus w / AMinus w + w * deriv delta w / (1 + delta w)) := by
    dsimp [L]
    field_simp [hw0]
    <;> ring
  have hscale : τ * (L * z).re = (w * L).re := by
    dsimp [w]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    ring
  change τ * (L * z).re = w.im - 1 / 2 +
    (w * deriv AMinus w / AMinus w + w * deriv delta w / (1 + delta w)).re
  rw [hscale, halg]
  simp [Complex.mul_re, Complex.mul_im]

end J0RadialUniqueness
