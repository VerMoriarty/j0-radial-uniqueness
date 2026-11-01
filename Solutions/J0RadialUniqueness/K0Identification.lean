import Solutions.J0RadialUniqueness.LaplaceRealODE
import Solutions.J0RadialUniqueness.LaplaceLogConstant
import Solutions.J0RadialUniqueness.K0RealODE
import Solutions.J0RadialUniqueness.K0RealValue
import Solutions.J0RadialUniqueness.K0Continuation
import Solutions.J0RadialUniqueness.SingularBesselUniqueness

noncomputable section
open Filter
open scoped Topology

namespace J0RadialUniqueness

theorem kSpectral_sub_realK0Series_tendsto_zero :
    Tendsto (fun x : ℝ => kSpectral x - realK0Series x) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun x : ℝ => laplaceK (x : ℂ) - K0Series (x : ℂ))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have h := laplaceK_add_log_half_tendsto_neg_eulerMascheroni.sub
      K0Series_positive_real_limit
    simpa only [add_sub_add_right_eq_sub, sub_self] using h
  have hr : Tendsto (fun x : ℝ => (laplaceK (x : ℂ) - K0Series (x : ℂ)).re)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hc
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [laplaceK_ofReal_eq_kSpectral hx]
  rfl

theorem kSpectral_eq_realK0Series {x : ℝ} (hx : 0 < x) :
    kSpectral x = realK0Series x := by
  let b : ℝ → ℝ := fun t => kSpectral t - realK0Series t
  let bp : ℝ → ℝ := fun t => kSpectralPrime t - realK0SeriesSlope t
  have hb (t : ℝ) (ht : 0 < t) : HasDerivAt b (bp t) t :=
    (kSpectral_hasDerivAt ht).sub (realK0Series_hasDerivAt ht)
  have hbp (t : ℝ) (ht : 0 < t) : HasDerivAt bp (b t - bp t / t) t := by
    have h := (kSpectralPrime_hasDerivAt_normalized ht).sub
      (realK0SeriesSlope_hasDerivAt ht)
    apply h.congr_deriv
    dsimp only [b, bp]
    ring
  have hz := singularBessel_zero_of_limits realI0 realI0Slope b bp
    (fun t _ => realI0_hasDerivAt t) (fun _ ht => realI0Slope_hasDerivAt ht)
    hb hbp (fun t _ => realI0_ne_zero t) realI0_tendsto_one
    kSpectral_sub_realK0Series_tendsto_zero x hx
  exact sub_eq_zero.mp hz

theorem laplaceK_eq_K0Series_positive_real {x : ℝ} (hx : 0 < x) :
    laplaceK (x : ℂ) = K0Series (x : ℂ) := by
  rw [laplaceK_ofReal_eq_kSpectral hx, kSpectral_eq_realK0Series hx]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    exact (K0Series_ofReal_im hx).symm

/-- Proposition 3.1: independent series/integral identification on all of Omega. -/
theorem k_laplace_identification : KLaplaceIdentificationStatement :=
  laplaceIdentification_of_positive_real (fun _ hx => laplaceK_eq_K0Series_positive_real hx)

theorem paper_3_1 : KLaplaceStatement ∧ KLaplaceIdentificationStatement :=
  ⟨k_laplace_analytic, k_laplace_identification⟩

end J0RadialUniqueness
