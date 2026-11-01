import Solutions.J0RadialUniqueness.AngularProjectionOperators
import Solutions.J0RadialUniqueness.SpectralCosine

/-! The actual complex lowering derivative and its covariance under plane
rotation. Differentiation of the angular integral uses the proved compact
parameter theorem. In particular, the spectral-mode lowering identities below
have no derivative-exchange or rotation-covariance premise. -/

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff Interval

set_option maxHeartbeats 1000000

namespace J0RadialUniqueness

theorem loweringAngularProjection_const_mul (c : ℂ) (f : Plane → ℂ) (m : ℤ) (x : Plane) :
    angularProjection (fun y => c * f y) m x = c * angularProjection f m x := by
  simp only [angularProjection_eq_integral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  ring

def complexLowering (f : Plane → ℂ) (x : Plane) : ℂ :=
  directionalKernel f distributionAxis0 x -
    Complex.I * directionalKernel f distributionAxis1 x

def complexLoweringIterate : ℕ → (Plane → ℂ) → Plane → ℂ
  | 0, f => f
  | k + 1, f => complexLowering (complexLoweringIterate k f)

theorem complexLowering_contDiff {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (complexLowering f) :=
  (directionalKernel_contDiff hf distributionAxis0).sub
    (contDiff_const.mul (directionalKernel_contDiff hf distributionAxis1))

theorem complexLoweringIterate_contDiff {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (complexLoweringIterate k f) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact complexLowering_contDiff ih

theorem complexLowering_const_mul {f : Plane → ℂ} (hf : Differentiable ℝ f)
    (c : ℂ) (x : Plane) :
    complexLowering (fun y => c * f y) x = c * complexLowering f x := by
  unfold complexLowering directionalKernel
  rw [fderiv_const_mul (hf x) c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem complexLowering_add {f g : Plane → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Plane) :
    complexLowering (fun y => f y + g y) x = complexLowering f x + complexLowering g x := by
  unfold complexLowering directionalKernel
  rw [fderiv_fun_add (hf x) (hg x)]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem complexLoweringIterate_const_mul {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (c : ℂ) (x : Plane) :
    complexLoweringIterate k (fun y => c * f y) x = c * complexLoweringIterate k f x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have he : complexLoweringIterate k (fun y => c * f y) =
          fun y => c * complexLoweringIterate k f y := funext ih
      simp only [complexLoweringIterate, he]
      exact complexLowering_const_mul
        ((complexLoweringIterate_contDiff hf k).differentiable (by simp)) c x

theorem complexLoweringIterate_add {f g : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : Plane) :
    complexLoweringIterate k (fun y => f y + g y) x =
      complexLoweringIterate k f x + complexLoweringIterate k g x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have he : complexLoweringIterate k (fun y => f y + g y) =
          fun y => complexLoweringIterate k f y + complexLoweringIterate k g y := funext ih
      simp only [complexLoweringIterate, he]
      exact complexLowering_add
        ((complexLoweringIterate_contDiff hf k).differentiable (by simp))
        ((complexLoweringIterate_contDiff hg k).differentiable (by simp)) x

theorem planeRotation_distributionAxis0 (θ : ℝ) :
    planeRotation θ distributionAxis0 =
      Real.cos θ • distributionAxis0 + Real.sin θ • distributionAxis1 := by
  apply complexToPlane.symm.injective
  rw [planeRotation_apply, LinearIsometryEquiv.symm_apply_apply]
  simp only [map_add, map_smul]
  simp [complexToPlane_symm_apply, distributionAxis0, distributionAxis1,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, Complex.exp_ofReal_mul_I] <;> ring

theorem planeRotation_distributionAxis1 (θ : ℝ) :
    planeRotation θ distributionAxis1 =
      -Real.sin θ • distributionAxis0 + Real.cos θ • distributionAxis1 := by
  apply complexToPlane.symm.injective
  rw [planeRotation_apply, LinearIsometryEquiv.symm_apply_apply]
  simp only [map_add, map_smul]
  simp [complexToPlane_symm_apply, distributionAxis0, distributionAxis1,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, Complex.exp_ofReal_mul_I] <;>
    ring_nf <;> simp [Complex.I_sq, sub_eq_add_neg]

/-- The rotation phase follows from the real Fréchet chain rule and the two
actual basis images. -/
theorem complexLowering_comp_planeRotation {f : Plane → ℂ}
    (hf : Differentiable ℝ f) (θ : ℝ) (x : Plane) :
    complexLowering (fun y => f (planeRotation θ y)) x =
      Complex.exp ((θ : ℂ) * Complex.I) * complexLowering f (planeRotation θ x) := by
  let e := (planeRotation θ).toContinuousLinearEquiv.toContinuousLinearMap
  have hd : HasFDerivAt (fun y => f (planeRotation θ y))
      ((fderiv ℝ f (planeRotation θ x)).comp e) x := by
    convert! (hf (planeRotation θ x)).hasFDerivAt.comp x e.hasFDerivAt using 1 <;> rfl
  unfold complexLowering directionalKernel
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change fderiv ℝ f (planeRotation θ x) (planeRotation θ distributionAxis0) -
      Complex.I * fderiv ℝ f (planeRotation θ x) (planeRotation θ distributionAxis1) = _
  rw [planeRotation_distributionAxis0, planeRotation_distributionAxis1,
    Complex.exp_ofReal_mul_I]
  simp only [map_add, map_smul, Complex.real_smul, Complex.ofReal_neg]
  ring_nf <;> simp [Complex.I_sq]

theorem complexLowering_plane_intervalIntegral {G : Plane × ℝ → ℂ}
    (hG : ContDiff ℝ 1 G) (a b : ℝ) (x : Plane) :
    complexLowering (fun y => ∫ t : ℝ in a..b, G (y, t)) x =
      ∫ t : ℝ in a..b, complexLowering (fun y => G (y, t)) x := by
  have hi (v : Plane) : IntervalIntegrable
      (fun t : ℝ => planeParameterDirectional G v (x, t)) volume a b :=
    (((planeParameterDirectional_contDiff (n := 0) hG v).continuous).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  unfold complexLowering
  rw [directionalKernel_plane_intervalIntegral hG,
    directionalKernel_plane_intervalIntegral hG, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hi distributionAxis0)
      ((hi distributionAxis1).const_mul Complex.I)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [directionalKernel_plane_parameter hG, directionalKernel_plane_parameter hG]

/-- The integer angular mode drops by one under the actual lowering
derivative. All differentiation and phase identities have been proved. -/
theorem complexLowering_angularProjection {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (m : ℤ) (x : Plane) :
    complexLowering (angularProjection f m) x =
      angularProjection (complexLowering f) (m - 1) x := by
  have hw : ContDiff ℝ 1 (fun p : Plane × ℝ => helmholtzAngularWeight m p.2) := by
    unfold helmholtzAngularWeight
    have ht : ContDiff ℝ 1 (fun p : Plane × ℝ => (p.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_snd
    exact (contDiff_const.mul ht).cexp
  have hf₁ : ContDiff ℝ 1 f := (contDiff_infty.mp hf) 1
  have hG : ContDiff ℝ 1 (fun p : Plane × ℝ =>
      helmholtzAngularWeight m p.2 * f (planeRotation p.2 p.1)) :=
    hw.mul (hf₁.comp contDiff_planeRotation_joint)
  have he : angularProjection f m = fun y : Plane =>
      ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        helmholtzAngularWeight m θ * f (planeRotation θ y) :=
    funext (angularProjection_eq_integral f m)
  rw [he, complexLowering_plane_intervalIntegral hG, angularProjection_eq_integral]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  have hrot : Differentiable ℝ (fun y => f (planeRotation θ y)) :=
    (hf.differentiable (by simp)).comp (planeRotation θ).toContinuousLinearEquiv.differentiable
  rw [complexLowering_const_mul hrot, complexLowering_comp_planeRotation
    (hf.differentiable (by simp))]
  rw [← mul_assoc, angularWeight_mul_rotation_exp]

theorem complexLowering_spectralExponential (lam : ℂ) (x : Plane) :
    complexLowering (spectralExponential lam) x = lam * spectralExponential lam x := by
  unfold complexLowering directionalKernel
  rw [(spectralExponential_hasFDerivAt lam x).fderiv]
  simp [spectralExponentLinear_apply, distributionAxis0, distributionAxis1,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, smul_eq_mul] <;> ring

theorem complexLowering_angularProjection_spectralExponential (lam : ℂ) (m : ℤ) (x : Plane) :
    complexLowering (angularProjection (spectralExponential lam) m) x =
      lam * angularProjection (spectralExponential lam) (m - 1) x := by
  rw [complexLowering_angularProjection (spectralExponential_contDiff lam)]
  have he : complexLowering (spectralExponential lam) =
      fun y => lam * spectralExponential lam y := funext (complexLowering_spectralExponential lam)
  rw [he, loweringAngularProjection_const_mul]

/-- Iterating the actual first-order operator gives the exact spectral
power, with the mode index reduced at every step. -/
theorem complexLoweringIterate_angularProjection_spectralExponential
    (lam : ℂ) (m : ℤ) (k : ℕ) (x : Plane) :
    complexLoweringIterate k (angularProjection (spectralExponential lam) m) x =
      lam ^ k * angularProjection (spectralExponential lam) (m - (k : ℤ)) x := by
  induction k generalizing x with
  | zero => simp only [complexLoweringIterate, Nat.cast_zero, sub_zero, pow_zero, one_mul]
  | succ k ih =>
      have he : complexLoweringIterate k (angularProjection (spectralExponential lam) m) =
          fun y => lam ^ k * angularProjection (spectralExponential lam) (m - (k : ℤ)) y := funext ih
      simp only [complexLoweringIterate, he]
      rw [complexLowering_const_mul
        ((angularProjection_contDiff (spectralExponential_contDiff lam) _).differentiable (by simp)),
        complexLowering_angularProjection_spectralExponential]
      have hind : m - (k : ℤ) - 1 = m - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hind, pow_succ]
      ring

theorem complexLoweringIterate_diagonal_mode_spectralExponential (lam : ℂ) (k : ℕ) (x : Plane) :
    complexLoweringIterate k (angularProjection (spectralExponential lam) (k : ℤ)) x =
      lam ^ k * angularProjection (spectralExponential lam) 0 x := by
  simpa only [sub_self] using
    complexLoweringIterate_angularProjection_spectralExponential lam (k : ℤ) k x

theorem angularProjection_add {f g : Plane → ℂ} (hf : Continuous f) (hg : Continuous g)
    (m : ℤ) (x : Plane) :
    angularProjection (fun y => f y + g y) m x =
      angularProjection f m x + angularProjection g m x := by
  simp only [angularProjection_eq_integral, mul_add]
  have hi (h : Plane → ℂ) (hh : Continuous h) : IntervalIntegrable
      (fun θ : ℝ => helmholtzAngularWeight m θ * h (planeRotation θ x))
        volume 0 (2 * Real.pi) :=
    ((continuous_angularProjection_integrand hh m).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  exact intervalIntegral.integral_add (hi f hf) (hi g hg)

/-- For every even natural mode, cosine lowering has the same spectral
power as the positive exponential. -/
theorem complexLoweringIterate_diagonal_mode_spectralCosine
    (ν : ℂ) (k : ℕ) (hk : Even k) (x : Plane) :
    complexLoweringIterate k (angularProjection (spectralCosine ν) (k : ℤ)) x =
      (Complex.I * ν) ^ k * angularProjection (spectralCosine ν) 0 x := by
  have he (m : ℤ) : angularProjection (spectralCosine ν) m = fun y =>
      (1 / 2 : ℂ) * (angularProjection (spectralExponential (Complex.I * ν)) m y +
        angularProjection (spectralExponential (-Complex.I * ν)) m y) := by
    funext y
    rw [spectralCosine_eq_exponential_combination, loweringAngularProjection_const_mul,
      angularProjection_add (spectralExponential_contDiff _).continuous
        (spectralExponential_contDiff _).continuous]
  have hp := angularProjection_contDiff (spectralExponential_contDiff (Complex.I * ν)) (k : ℤ)
  have hn := angularProjection_contDiff (spectralExponential_contDiff (-Complex.I * ν)) (k : ℤ)
  rw [he, complexLoweringIterate_const_mul (hp.add hn),
    complexLoweringIterate_add hp hn,
    complexLoweringIterate_diagonal_mode_spectralExponential,
    complexLoweringIterate_diagonal_mode_spectralExponential, he]
  have hpow : (-Complex.I * ν) ^ k = (Complex.I * ν) ^ k := by
    rw [show -Complex.I * ν = -(Complex.I * ν) by ring, hk.neg_pow]
  rw [hpow]
  ring

theorem planeRotation_smul_distributionAxis0 (θ t : ℝ) :
    planeRotation θ (t • distributionAxis0) = t • circleDirection θ := by
  rw [map_smul, planeRotation_distributionAxis0]
  ext j
  fin_cases j <;>
    simp [distributionAxis0, distributionAxis1, EuclideanSpace.basisFun_apply,
      PiLp.single_apply, PiLp.smul_apply, circleDirection, smul_eq_mul]

/-- The zero mode on the first coordinate axis is exactly the actual circle
integral, with the unnormalized angular projection contributing `2π`. -/
theorem angularProjection_zero_axis (f : Plane → ℂ) (t : ℝ) :
    angularProjection f 0 (t • distributionAxis0) =
      (2 * (Real.pi : ℂ)) * circularMean f t 0 := by
  have hpi : 2 * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [angularProjection_eq_integral, circularMean_eq_complex_prefactor]
  simp only [helmholtzAngularWeight, Int.cast_zero, mul_zero, zero_mul,
    Complex.exp_zero, one_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [planeRotation_smul_distributionAxis0, zero_add]

theorem angularProjection_zero_spectralCosine_axis (ν : ℂ) (t : ℝ) :
    angularProjection (spectralCosine ν) 0 (t • distributionAxis0) =
      (2 * (Real.pi : ℂ)) * J0 ((t : ℂ) * ν) := by
  rw [angularProjection_zero_axis, circularMean_spectralCosine, spectralCosine_zero, one_mul]

theorem complexLoweringIterate_diagonal_mode_spectralCosine_axis
    (ν : ℂ) (k : ℕ) (hk : Even k) (t : ℝ) :
    complexLoweringIterate k (angularProjection (spectralCosine ν) (k : ℤ))
        (t • distributionAxis0) =
      (Complex.I * ν) ^ k * ((2 * (Real.pi : ℂ)) * J0 ((t : ℂ) * ν)) := by
  rw [complexLoweringIterate_diagonal_mode_spectralCosine ν k hk,
    angularProjection_zero_spectralCosine_axis]

end J0RadialUniqueness
