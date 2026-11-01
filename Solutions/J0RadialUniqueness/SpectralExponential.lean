import Definitions.J0RadialUniqueness.TwoRadius
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Differential and nonharmonic parts of the explicit spectral counterexample.

All functions here are the actual `spectralExponential`, `spectralRealPart`, and
`spectralImagPart` from `Definitions.J0RadialUniqueness.TwoRadius`.  The circle
mean multiplier identity is a separate obligation.
-/

noncomputable section

open Laplacian
open scoped ContDiff

namespace J0RadialUniqueness

/-- The real-linear exponent of the explicit spectral exponential. -/
def spectralExponentLinear (lam : ℂ) : Plane →L[ℝ] ℂ :=
  lam • (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0))

@[simp] theorem spectralExponentLinear_apply (lam : ℂ) (x : Plane) :
    spectralExponentLinear lam x = lam * (x 0 : ℂ) := by
  simp [spectralExponentLinear, ContinuousLinearMap.comp_apply, smul_eq_mul]

/-- Its first real Fréchet derivative, as a continuous real-linear map. -/
theorem spectralExponential_hasFDerivAt (lam : ℂ) (x : Plane) :
    HasFDerivAt (spectralExponential lam)
      (spectralExponential lam x • spectralExponentLinear lam) x := by
  convert! (spectralExponentLinear lam).hasFDerivAt.cexp using 1 <;>
    simp [spectralExponential, spectralExponentLinear, ContinuousLinearMap.comp_apply,
      smul_eq_mul]

theorem spectralExponential_fderiv (lam : ℂ) :
    fderiv ℝ (spectralExponential lam) =
      fun x => spectralExponential lam x • spectralExponentLinear lam := by
  funext x
  exact (spectralExponential_hasFDerivAt lam x).fderiv

/-- The full second derivative is supported in the first coordinate direction. -/
theorem spectralExponential_iteratedFDeriv_two (lam : ℂ) (x : Plane)
    (v : Fin 2 → Plane) :
    iteratedFDeriv ℝ 2 (spectralExponential lam) x v =
      spectralExponential lam x * spectralExponentLinear lam (v 0) *
        spectralExponentLinear lam (v 1) := by
  rw [iteratedFDeriv_two_apply, spectralExponential_fderiv]
  rw [((spectralExponential_hasFDerivAt lam x).smul_const
    (spectralExponentLinear lam)).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

@[fun_prop] theorem spectralExponential_contDiff (lam : ℂ) :
    ContDiff ℝ ∞ (spectralExponential lam) := by
  convert! (spectralExponentLinear lam).contDiff.cexp using 1 <;>
    first | rfl | simp [spectralExponential, spectralExponentLinear_apply]

@[fun_prop] theorem spectralRealPart_contDiff (lam : ℂ) :
    ContDiff ℝ ∞ (spectralRealPart lam) := by
  convert! Complex.reCLM.contDiff.comp (spectralExponential_contDiff lam) using 1 <;>
    first | rfl | simp only [spectralRealPart, Function.comp_def, Complex.reCLM_apply]

@[fun_prop] theorem spectralImagPart_contDiff (lam : ℂ) :
    ContDiff ℝ ∞ (spectralImagPart lam) := by
  convert! Complex.imCLM.contDiff.comp (spectralExponential_contDiff lam) using 1 <;>
    first | rfl | simp only [spectralImagPart, Function.comp_def, Complex.imCLM_apply]

/-- The complex-valued plane exponential satisfies the expected Laplace eigen-equation. -/
theorem laplacian_spectralExponential (lam : ℂ) (x : Plane) :
    laplacian (spectralExponential lam) x = lam ^ 2 * spectralExponential lam x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (spectralExponential lam) (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp [Fin.sum_univ_two, spectralExponential_iteratedFDeriv_two,
    spectralExponentLinear_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  ring

/-- Taking the real part commutes with this Laplacian. -/
theorem laplacian_spectralRealPart (lam : ℂ) (x : Plane) :
    laplacian (spectralRealPart lam) x = (lam ^ 2 * spectralExponential lam x).re := by
  have hs : ContDiff ℝ 2 (spectralExponential lam) :=
    (contDiff_infty.mp (spectralExponential_contDiff lam)) 2
  have h := hs.contDiffAt.laplacian_CLM_comp_left (x := x) (l := Complex.reCLM)
  convert! h using 1 <;>
    first | rfl | simp only [spectralRealPart, Function.comp_def, Complex.reCLM_apply,
      laplacian_spectralExponential]

/-- Taking the imaginary part commutes with this Laplacian. -/
theorem laplacian_spectralImagPart (lam : ℂ) (x : Plane) :
    laplacian (spectralImagPart lam) x = (lam ^ 2 * spectralExponential lam x).im := by
  have hs : ContDiff ℝ 2 (spectralExponential lam) :=
    (contDiff_infty.mp (spectralExponential_contDiff lam)) 2
  have h := hs.contDiffAt.laplacian_CLM_comp_left (x := x) (l := Complex.imCLM)
  convert! h using 1 <;>
    first | rfl | simp only [spectralImagPart, Function.comp_def, Complex.imCLM_apply,
      laplacian_spectralExponential]

@[simp] theorem spectralExponential_zero (lam : ℂ) :
    spectralExponential lam (0 : Plane) = 1 := by
  simp [spectralExponential]

@[simp] theorem laplacian_spectralRealPart_zero (lam : ℂ) :
    laplacian (spectralRealPart lam) (0 : Plane) = (lam ^ 2).re := by
  rw [laplacian_spectralRealPart]
  simp

@[simp] theorem laplacian_spectralImagPart_zero (lam : ℂ) :
    laplacian (spectralImagPart lam) (0 : Plane) = (lam ^ 2).im := by
  rw [laplacian_spectralImagPart]
  simp

/-- A nonzero real component of `lam^2` gives the explicit real-part witness. -/
theorem spectralRealPart_not_harmonic_of_sq_re_ne_zero (lam : ℂ)
    (hre : (lam ^ 2).re ≠ 0) :
    ¬ InnerProductSpace.HarmonicOnNhd (spectralRealPart lam) Set.univ := by
  intro h
  have hzero : laplacian (spectralRealPart lam) (0 : Plane) = 0 :=
    (h 0 (Set.mem_univ _)).2.eq_of_nhds
  exact hre (by simpa only [laplacian_spectralRealPart_zero] using hzero)

/-- A nonzero imaginary component of `lam^2` gives the explicit imaginary-part witness. -/
theorem spectralImagPart_not_harmonic_of_sq_im_ne_zero (lam : ℂ)
    (him : (lam ^ 2).im ≠ 0) :
    ¬ InnerProductSpace.HarmonicOnNhd (spectralImagPart lam) Set.univ := by
  intro h
  have hzero : laplacian (spectralImagPart lam) (0 : Plane) = 0 :=
    (h 0 (Set.mem_univ _)).2.eq_of_nhds
  exact him (by simpa only [laplacian_spectralImagPart_zero] using hzero)

/-- The part of Proposition 6.2 independent of the circle mean multiplier.

The witness is selected explicitly by the components of `lam^2` at the origin:
use the real part if its Laplacian is nonzero, and the imaginary part otherwise.
-/
theorem exists_spectral_nonharmonic_witness (lam : ℂ) (hlam : lam ≠ 0) :
    ∃ g : Plane → ℝ,
      (g = spectralRealPart lam ∨ g = spectralImagPart lam) ∧
      ContDiff ℝ ∞ g ∧
      ¬ InnerProductSpace.HarmonicOnNhd g Set.univ ∧
      laplacian g (0 : Plane) ≠ 0 := by
  classical
  by_cases hre : (lam ^ 2).re = 0
  · have him : (lam ^ 2).im ≠ 0 := by
      intro him
      apply pow_ne_zero 2 hlam
      exact Complex.ext (by simpa using hre) (by simpa using him)
    refine ⟨spectralImagPart lam, Or.inr rfl, spectralImagPart_contDiff lam,
      spectralImagPart_not_harmonic_of_sq_im_ne_zero lam him, ?_⟩
    simpa only [laplacian_spectralImagPart_zero] using him
  · refine ⟨spectralRealPart lam, Or.inl rfl, spectralRealPart_contDiff lam,
      spectralRealPart_not_harmonic_of_sq_re_ne_zero lam hre, ?_⟩
    simpa only [laplacian_spectralRealPart_zero] using hre

end J0RadialUniqueness
