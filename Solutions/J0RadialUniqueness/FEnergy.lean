import Solutions.J0RadialUniqueness.FODE
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The radial energy identity of Lemma 2.1 for the actual factorial series F.
The differential equation is proved in `FODE`; the final statement discharges it.
The derivatives and boundary values are proved from the already closed
analyticity of F and its coefficients.
-/

noncomputable section

namespace J0RadialUniqueness

def FRay (a : ℂ) (s : ℝ) : ℂ := F ((s : ℂ) * a)

def FRaySlope (a : ℂ) (s : ℝ) : ℂ := a * deriv F ((s : ℂ) * a)

def FRayAccel (a : ℂ) (s : ℝ) : ℂ := a ^ 2 * deriv (deriv F) ((s : ℂ) * a)

def FRayNormSq (a : ℂ) (s : ℝ) : ℝ := ‖FRay a s‖ ^ 2

def FRayFlux (a : ℂ) (s : ℝ) : ℝ :=
  s * (2 * inner ℝ (FRay a s) (FRaySlope a s))

theorem FRay_hasDerivAt (a : ℂ) (s : ℝ) :
    HasDerivAt (FRay a) (FRaySlope a s) s := by
  have h := (F_differentiable ((s : ℂ) * a)).hasDerivAt.comp (s : ℂ)
    ((hasDerivAt_id (s : ℂ)).mul_const a)
  have hr := h.comp_ofReal
  change HasDerivAt (fun u : ℝ => F ((u : ℂ) * a))
    (deriv F ((s : ℂ) * a) * (1 * a)) s at hr
  have hfun : (fun u : ℝ => F ((u : ℂ) * a)) = FRay a := by funext u; rfl
  rw [hfun] at hr
  apply hr.congr_deriv
  dsimp only [FRaySlope]
  ring

@[simp] theorem FRay_deriv (a : ℂ) (s : ℝ) : deriv (FRay a) s = FRaySlope a s :=
  (FRay_hasDerivAt a s).deriv

theorem FRaySlope_hasDerivAt (a : ℂ) (s : ℝ) :
    HasDerivAt (FRaySlope a) (FRayAccel a s) s := by
  have h := (F_deriv_differentiable ((s : ℂ) * a)).hasDerivAt.comp (s : ℂ)
    ((hasDerivAt_id (s : ℂ)).mul_const a)
  have hr := h.comp_ofReal.const_mul a
  change HasDerivAt (fun u : ℝ => a * deriv F ((u : ℂ) * a))
    (a * (deriv (deriv F) ((s : ℂ) * a) * (1 * a))) s at hr
  have hfun : (fun u : ℝ => a * deriv F ((u : ℂ) * a)) = FRaySlope a := by
    funext u
    rfl
  rw [hfun] at hr
  apply hr.congr_deriv
  dsimp only [FRayAccel]
  ring

@[simp] theorem FRaySlope_deriv (a : ℂ) (s : ℝ) :
    deriv (FRaySlope a) s = FRayAccel a s :=
  (FRaySlope_hasDerivAt a s).deriv

@[simp] theorem FRay_zero (a : ℂ) : FRay a 0 = 1 := by simp [FRay]

@[simp] theorem FRaySlope_zero (a : ℂ) : FRaySlope a 0 = a := by
  simp [FRaySlope, deriv_F_zero]

/-- The radial ODE has no division by s, so it includes the endpoint s = 0. -/
theorem FRay_ode (hode : FODEStatement) (a : ℂ) (s : ℝ) :
    (s : ℂ) * FRayAccel a s + FRaySlope a s = a * FRay a s := by
  have h := hode.2.2 ((s : ℂ) * a)
  dsimp only [FRayAccel, FRaySlope, FRay]
  linear_combination a * h

theorem FRayNormSq_hasDerivAt (a : ℂ) (s : ℝ) :
    HasDerivAt (FRayNormSq a) (2 * inner ℝ (FRay a s) (FRaySlope a s)) s :=
  (FRay_hasDerivAt a s).norm_sq

@[simp] theorem FRayNormSq_deriv (a : ℂ) (s : ℝ) :
    deriv (FRayNormSq a) s = 2 * inner ℝ (FRay a s) (FRaySlope a s) :=
  (FRayNormSq_hasDerivAt a s).deriv

theorem FRayFlux_eq (a : ℂ) (s : ℝ) :
    FRayFlux a s = s * deriv (FRayNormSq a) s := by
  rw [FRayNormSq_deriv]
  rfl

@[simp] theorem FRayFlux_zero (a : ℂ) : FRayFlux a 0 = 0 := by simp [FRayFlux]

theorem real_inner_complex_mul_self (a v : ℂ) :
    inner ℝ v (a * v) = a.re * ‖v‖ ^ 2 := by
  rw [Complex.inner, mul_assoc, Complex.mul_conj]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.normSq_eq_norm_sq]

/-- The derivative of s Y'(s), expressed without singular terms at zero. -/
theorem FRayFlux_hasDerivAt (hode : FODEStatement) (a : ℂ) (s : ℝ) :
    HasDerivAt (FRayFlux a)
      (2 * (s * ‖FRaySlope a s‖ ^ 2 + a.re * ‖FRay a s‖ ^ 2)) s := by
  have hi := (FRay_hasDerivAt a s).inner ℝ (FRaySlope_hasDerivAt a s)
  have hd := (hasDerivAt_id s).mul (hi.const_mul 2)
  have hscalar : inner ℝ (FRay a s) ((s : ℂ) * FRayAccel a s) =
      s * inner ℝ (FRay a s) (FRayAccel a s) := by
    change inner ℝ (FRay a s) (s • FRayAccel a s) =
      s * inner ℝ (FRay a s) (FRayAccel a s)
    exact real_inner_smul_right _ _ _
  have he : s * inner ℝ (FRay a s) (FRayAccel a s) +
      inner ℝ (FRay a s) (FRaySlope a s) = a.re * ‖FRay a s‖ ^ 2 := by
    have he' := congrArg (fun v : ℂ => inner ℝ (FRay a s) v) (FRay_ode hode a s)
    simpa only [inner_add_right, hscalar, real_inner_complex_mul_self] using he'
  have hval :
      2 * inner ℝ (FRay a s) (FRaySlope a s) +
        s * (2 * (inner ℝ (FRay a s) (FRayAccel a s) +
          inner ℝ (FRaySlope a s) (FRaySlope a s))) =
      2 * (s * ‖FRaySlope a s‖ ^ 2 + a.re * ‖FRay a s‖ ^ 2) := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith only [he]
  have hfun : (id * fun u : ℝ => 2 * inner ℝ (FRay a u) (FRaySlope a u)) =
      FRayFlux a := by
    funext u
    rfl
  rw [hfun] at hd
  apply hd.congr_deriv
  simpa only [one_mul, id_eq] using hval

/-- The general energy identity, valid for every complex direction and real endpoint. -/
theorem FRay_energy (hode : FODEStatement) (a : ℂ) (s : ℝ) :
    s * deriv (FRayNormSq a) s =
      2 * ∫ u in (0 : ℝ)..s,
        (u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2) := by
  have hh : Continuous (FRay a) :=
    continuous_iff_continuousAt.mpr (fun u => (FRay_hasDerivAt a u).continuousAt)
  have hs : Continuous (FRaySlope a) :=
    continuous_iff_continuousAt.mpr (fun u => (FRaySlope_hasDerivAt a u).continuousAt)
  have hc : Continuous (fun u : ℝ =>
      2 * (u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2)) :=
    continuous_const.mul
      ((continuous_id.mul (hs.norm.pow 2)).add (continuous_const.mul (hh.norm.pow 2)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := s) (f := FRayFlux a)
    (f' := fun u => 2 * (u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2))
    (fun u _ => FRayFlux_hasDerivAt hode a u) (hc.intervalIntegrable 0 s)
  rw [FRayFlux_zero, sub_zero] at hftc
  calc
    s * deriv (FRayNormSq a) s = FRayFlux a s := (FRayFlux_eq a s).symm
    _ = ∫ u in (0 : ℝ)..s,
        2 * (u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2) := hftc.symm
    _ = 2 * ∫ u in (0 : ℝ)..s,
        (u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2) :=
      intervalIntegral.integral_const_mul _ _

/-- The exact energy statement used by the paper follows from the actual F ODE. -/
theorem fEnergy_of_ode (hode : FODEStatement) : FEnergyStatement := by
  intro φ _ _
  let a : ℂ := Complex.exp (Complex.I * (φ : ℂ))
  have hare : a.re = Real.cos φ := by
    simp [a, Complex.exp_re, Complex.mul_re, Complex.mul_im]
  change FRay a 0 = 1 ∧ deriv (FRay a) 0 = a ∧
    ∀ s : ℝ, 0 ≤ s → s * deriv (FRayNormSq a) s =
      2 * ∫ u in (0 : ℝ)..s,
        (u * ‖deriv (FRay a) u‖ ^ 2 + Real.cos φ * ‖FRay a u‖ ^ 2)
  refine ⟨FRay_zero a, ?_, ?_⟩
  · rw [FRay_deriv, FRaySlope_zero]
  · intro s _
    simpa only [FRay_deriv, hare] using FRay_energy hode a s

/-- The paper's energy identity, with all inputs discharged. -/
theorem fEnergy : FEnergyStatement := fEnergy_of_ode F_ode_statement

end J0RadialUniqueness
