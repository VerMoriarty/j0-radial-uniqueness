import Solutions.J0RadialUniqueness.K0Identification
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The actual hyperbolic-cosine integral for the independently defined K₀
series. The genuine Jacobian theorem is applied on `(0,∞)`, whose image under
`cosh` is exactly `(1,∞)`. Thus the zero-derivative endpoint is excluded from
the substitution, and no finite-endpoint or convergence assumption is added. -/

noncomputable section

open MeasureTheory Set

namespace J0RadialUniqueness

theorem positiveCosh_image : Real.cosh '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Real.one_lt_cosh.mpr (ne_of_gt hu)
  · intro hv
    exact ⟨Real.arcosh v, Real.arcosh_pos hv, Real.cosh_arcosh hv.le⟩

theorem positiveCosh_injOn : InjOn Real.cosh (Ioi (0 : ℝ)) :=
  Real.cosh_injOn.mono Ioi_subset_Ici_self

theorem positiveCosh_sqrt_jacobian {u : ℝ} (hu : 0 < u) :
    Real.sqrt (Real.cosh u ^ 2 - 1) = Real.sinh u := by
  rw [← Real.sinh_sq, Real.sqrt_sq (Real.sinh_pos_iff.mpr hu).le]

/-- Cancellation is used only where the derivative `sinh u` is positive. -/
theorem positiveSpectralKernel_cosh_jacobian (x : ℝ) {u : ℝ} (hu : 0 < u) :
    |Real.sinh u| • positiveSpectralKernel x (Real.cosh u) =
      Real.exp (-x * Real.cosh u) := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  unfold positiveSpectralKernel
  rw [abs_of_pos hs, smul_eq_mul, positiveCosh_sqrt_jacobian hu]
  field_simp [hs.ne'] <;> ring

/-- Absolute convergence follows from the already proved actual spectral
integral and the genuine unbounded-domain Jacobian equivalence. -/
theorem realCoshKernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-x * Real.cosh u)) (Ioi 0) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun u _ => (Real.hasDerivAt_cosh u).hasDerivWithinAt)
    positiveCosh_injOn (positiveSpectralKernel x)
  rw [positiveCosh_image] at hchange
  apply (hchange.mp (positiveSpectralKernel_integrable hx)).congr_fun ?_ measurableSet_Ioi
  intro u hu
  exact positiveSpectralKernel_cosh_jacobian x hu

theorem positiveSpectralKernel_integral_eq_cosh (x : ℝ) :
    (∫ v : ℝ in Ioi 1, positiveSpectralKernel x v) =
      ∫ u : ℝ in Ioi 0, Real.exp (-x * Real.cosh u) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi (fun u _ => (Real.hasDerivAt_cosh u).hasDerivWithinAt)
    positiveCosh_injOn (positiveSpectralKernel x)
  rw [positiveCosh_image] at hchange
  calc
    _ = ∫ u : ℝ in Ioi 0, |Real.sinh u| • positiveSpectralKernel x (Real.cosh u) := hchange
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact positiveSpectralKernel_cosh_jacobian x hu

theorem realCoshKernel_ofReal (x u : ℝ) :
    (Real.exp (-x * Real.cosh u) : ℂ) =
      Complex.exp (-(x : ℂ) * (Real.cosh u : ℂ)) := by
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]

theorem complexCoshKernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(x : ℂ) * (Real.cosh u : ℂ))) (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => (Real.exp (-x * Real.cosh u) : ℂ)) (Ioi 0) :=
    (realCoshKernel_integrable hx).ofReal
  exact hi.congr (Filter.Eventually.of_forall (realCoshKernel_ofReal x))

theorem K0Series_ofReal_cosh_integral {x : ℝ} (hx : 0 < x) :
    K0Series (x : ℂ) =
      ∫ u : ℝ in Ioi 0, Complex.exp (-(x : ℂ) * (Real.cosh u : ℂ)) := by
  calc
    _ = laplaceK (x : ℂ) := (laplaceK_eq_K0Series_positive_real hx).symm
    _ = ((∫ v : ℝ in Ioi 1, positiveSpectralKernel x v : ℝ) : ℂ) :=
      laplaceK_ofReal_spectral_integral hx
    _ = ((∫ u : ℝ in Ioi 0, Real.exp (-x * Real.cosh u) : ℝ) : ℂ) := by
      rw [positiveSpectralKernel_integral_eq_cosh]
    _ = _ := by
      have hcast : (∫ u : ℝ in Ioi 0, (Real.exp (-x * Real.cosh u) : ℂ)) =
          ((∫ u : ℝ in Ioi 0, Real.exp (-x * Real.cosh u) : ℝ) : ℂ) := integral_ofReal
      calc
        _ = ∫ u : ℝ in Ioi 0, (Real.exp (-x * Real.cosh u) : ℂ) := hcast.symm
        _ = _ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (realCoshKernel_ofReal x)

/-- The independent paper-facing integral identity and its actual absolute
convergence, with exactly the original positive-real hypothesis. -/
theorem paper_k0_cosh_integral : ∀ x : ℝ, 0 < x →
    IntegrableOn (fun u : ℝ => Complex.exp (-(x : ℂ) * (Real.cosh u : ℂ))) (Ioi 0) ∧
      K0Series (x : ℂ) =
        ∫ u : ℝ in Ioi 0, Complex.exp (-(x : ℂ) * (Real.cosh u : ℂ)) := by
  intro x hx
  exact ⟨complexCoshKernel_integrable hx, K0Series_ofReal_cosh_integral hx⟩

end J0RadialUniqueness
