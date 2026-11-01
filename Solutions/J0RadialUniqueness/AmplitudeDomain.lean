import Solutions.J0RadialUniqueness.AmplitudeAnalytic
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
open scoped Topology

namespace J0RadialUniqueness

theorem amplitudeDomain_isOpen : IsOpen amplitudeDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hr : ∀ᶠ w in 𝓝 z, 0 < w.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hz.1)
  have hp := (APlus_hasDerivAt hz.1).continuousAt
  have hm := (AMinus_hasDerivAt hz.1).continuousAt
  have hn : ∀ᶠ w in 𝓝 z, APlus w * AMinus w ≠ 0 :=
    (hp.mul hm).eventually_ne hz.2
  exact hr.and hn

theorem delta_differentiableAt {z : ℂ} (hz : z ∈ amplitudeDomain) :
    DifferentiableAt ℂ delta z := by
  have he : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (2 * Complex.I * (w - (Real.pi : ℂ) / 4))) z := by
    fun_prop
  exact (he.mul (APlus_hasDerivAt hz.1).differentiableAt).div
    (AMinus_hasDerivAt hz.1).differentiableAt (mul_ne_zero_iff.mp hz.2).2

/-- Pointwise logarithmic differentiation of the actual definition of δ. -/
theorem delta_derivative_of_hasDerivAt {z : ℂ}
    (hp : HasDerivAt APlus (deriv APlus z) z)
    (hm : HasDerivAt AMinus (deriv AMinus z) z)
    (hp0 : APlus z ≠ 0) (hm0 : AMinus z ≠ 0) :
    z * deriv delta z = delta z *
      (2 * Complex.I * z + z * deriv APlus z / APlus z -
        z * deriv AMinus z / AMinus z) := by
  let E : ℂ := Complex.exp (2 * Complex.I * (z - (Real.pi : ℂ) / 4))
  have he : HasDerivAt
      (fun w : ℂ => Complex.exp (2 * Complex.I * (w - (Real.pi : ℂ) / 4)))
      (E * (2 * Complex.I)) z := by
    simpa [E] using
      (((hasDerivAt_id z).sub_const ((Real.pi : ℂ) / 4)).const_mul
        (2 * Complex.I)).cexp
  have hd : HasDerivAt delta
      (((E * (2 * Complex.I) * APlus z + E * deriv APlus z) * AMinus z -
        (E * APlus z) * deriv AMinus z) / AMinus z ^ 2) z :=
    (he.mul hp).div hm hm0
  rw [hd.deriv]
  change z *
      (((E * (2 * Complex.I) * APlus z + E * deriv APlus z) * AMinus z -
        (E * APlus z) * deriv AMinus z) / AMinus z ^ 2) =
    (E * APlus z / AMinus z) *
      (2 * Complex.I * z + z * deriv APlus z / APlus z -
        z * deriv AMinus z / AMinus z)
  field_simp [hp0, hm0] <;> ring

theorem deltaDerivative_of_amplitudeDerivative
    (h : AmplitudeDerivativeStatement) : DeltaDerivativeStatement := by
  intro z hz
  have hpoint := h.2.2 z hz.1
  exact delta_derivative_of_hasDerivAt
    hpoint.1.differentiableAt.hasDerivAt hpoint.2.differentiableAt.hasDerivAt
    (mul_ne_zero_iff.mp hz.2).1 (mul_ne_zero_iff.mp hz.2).2


/-- The delta derivative formula with all amplitude derivative inputs discharged. -/
theorem delta_derivative : DeltaDerivativeStatement :=
  deltaDerivative_of_amplitudeDerivative amplitude_derivatives

end J0RadialUniqueness
