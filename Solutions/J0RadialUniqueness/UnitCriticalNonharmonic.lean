import Solutions.J0RadialUniqueness.ComplexLoweringProjection
import Solutions.J0RadialUniqueness.UnitCriticalProjectedCandidate
import Solutions.J0RadialUniqueness.LocalHarmonicSmoothing
import Solutions.J0RadialUniqueness.RootBesselSeriesIsolation
import Solutions.J0RadialUniqueness.OnePointExistence
import Solutions.J0RadialUniqueness.SmoothingRootCosineSeries
import Solutions.J0RadialUniqueness.RapidRootCosineDifferentiation

/-! Local differential facts for the nonharmonicity of the critical-radius
candidate. In particular a function that is zero on an open set has every
actual iterated complex lowering derivative zero there. These are statements
about the actual Fréchet derivatives, without extra smoothness premises.

The final spectral contradiction uses the independently proved rapid-series
lowering identity. No spectral identity is postulated as a premise of the
paper-level sharpness witness. -/

noncomputable section

open MeasureTheory Set Filter Laplacian
open scoped Topology ContDiff

namespace J0RadialUniqueness

theorem complexLowering_eventuallyEq {f g : Plane → ℂ} {x : Plane}
    (h : f =ᶠ[𝓝 x] g) : complexLowering f =ᶠ[𝓝 x] complexLowering g := by
  have hd : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ g := h.fderiv
  filter_upwards [hd] with y hy
  unfold complexLowering directionalKernel
  rw [hy]

theorem complexLoweringIterate_eventuallyEq {f g : Plane → ℂ} {x : Plane}
    (k : ℕ) (h : f =ᶠ[𝓝 x] g) :
    complexLoweringIterate k f =ᶠ[𝓝 x] complexLoweringIterate k g := by
  induction k with
  | zero => exact h
  | succ k ih => exact complexLowering_eventuallyEq ih

@[simp] theorem complexLowering_zero :
    complexLowering (fun _ : Plane => (0 : ℂ)) = fun _ => 0 := by
  funext x
  have hd : fderiv ℝ (fun _ : Plane => (0 : ℂ)) x = 0 := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x).fderiv using 1 <;> rfl
  change (fderiv ℝ (fun _ : Plane => (0 : ℂ)) x) distributionAxis0 -
    Complex.I * (fderiv ℝ (fun _ : Plane => (0 : ℂ)) x) distributionAxis1 = 0
  rw [hd]
  simp

@[simp] theorem complexLoweringIterate_zero (k : ℕ) :
    complexLoweringIterate k (fun _ : Plane => (0 : ℂ)) = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [complexLoweringIterate, ih, complexLowering_zero]

theorem complexLoweringIterate_eq_zero_of_eventuallyEq_zero {f : Plane → ℂ} {x : Plane}
    (k : ℕ) (h : f =ᶠ[𝓝 x] fun _ => (0 : ℂ)) :
    complexLoweringIterate k f x = 0 := by
  have hh := (complexLoweringIterate_eventuallyEq k h).eq_of_nhds
  simpa only [complexLoweringIterate_zero] using hh

theorem complexLoweringIterate_eqOn_zero_of_eqOn_open {f : Plane → ℂ} {U : Set Plane}
    (hU : IsOpen U) (hf : EqOn f (fun _ => (0 : ℂ)) U) (k : ℕ) :
    EqOn (complexLoweringIterate k f) (fun _ => (0 : ℂ)) U := by
  intro x hx
  apply complexLoweringIterate_eq_zero_of_eventuallyEq_zero k
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hf hy

theorem laplacian_eqOn_of_eqOn_open {f g : Plane → ℂ} {U : Set Plane}
    (hU : IsOpen U) (hfg : EqOn f g U) : EqOn (laplacian f) (laplacian g) U := by
  intro x hx
  have he : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hfg hy
  exact (InnerProductSpace.laplacian_congr_nhds he).eq_of_nhds

/-- Equality on an open set transfers a vanishing Laplacian and all of its
lowering derivatives. This is a germ argument and uses no ordinary IVP at 0. -/
theorem complexLoweringIterate_laplacian_eqOn_zero_of_local_eq
    {f g : Plane → ℂ} {U : Set Plane} (hU : IsOpen U) (hfg : EqOn f g U)
    (hf : EqOn (laplacian f) (fun _ => (0 : ℂ)) U) (k : ℕ) :
    EqOn (complexLoweringIterate k (laplacian g)) (fun _ => (0 : ℂ)) U := by
  apply complexLoweringIterate_eqOn_zero_of_eqOn_open hU _ k
  intro x hx
  rw [← laplacian_eqOn_of_eqOn_open hU hfg hx]
  exact hf hx

/-- The polynomial spectral factor produced by lowering preserves weighted
absolute summability for the actual root set. -/
theorem loweringLaplacianCoefficient_weight_summable {a : RightOnePoint → ℂ}
    (ha : ∀ b : ℝ, Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖ ^ b))
    (k : ℕ) :
    Summable (fun ν : RightOnePoint =>
      ‖(-(ν : ℂ) ^ 2 * (Complex.I * (ν : ℂ)) ^ k) * a ν‖ * ‖(ν : ℂ)‖) := by
  have hsum := ha ((k + 3 : ℕ) : ℝ)
  apply hsum.congr
  intro ν
  rw [Real.rpow_natCast]
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_I, one_mul]
  rw [pow_add]
  ring

theorem loweringLaplacianCoefficient_ne_zero {a : RightOnePoint → ℂ}
    (k : ℕ) (σ : RightOnePoint) (ha : a σ ≠ 0) :
    (-(σ : ℂ) ^ 2 * (Complex.I * (σ : ℂ)) ^ k) * a σ ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 σ.val.property.1))
      (pow_ne_zero k (mul_ne_zero Complex.I_ne_zero σ.val.property.1))) ha

theorem norm_distributionAxis0_eq_one : ‖distributionAxis0‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.norm_eq_one 0

theorem unit_interval_axis_mem_ball {R t : ℝ} (hR : 1 < R)
    (ht : t ∈ Icc (0 : ℝ) 1) : t • distributionAxis0 ∈ planeBall R := by
  rw [planeBall, Metric.mem_ball, dist_zero_right, norm_smul,
    norm_distributionAxis0_eq_one, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_one]
  exact ht.2.trans_lt hR

/-- Every even projection of the actual critical residue-series extension is
nonharmonic on every centered ball whose radius exceeds the smaller radius.
The smoothing radius is chosen inside the strict excess, and its actual
support radius is twice the scale parameter. -/
theorem unitCritical_projected_not_distributionHarmonicOn
    (M : ℕ) (hM : 2 ≤ M) {τ : ℝ} (hτ : 1 < τ)
    (hMT : 1 + τ < 2 * M - 1) {F : Plane → ℂ} (hF : Continuous F)
    (hEq : EqOn F (scaledBesselCosinePlane M τ 1) (planeBall (1 + τ)))
    (k : ℕ) (hk : Even k) {δ : ℝ} (hδ : 1 < δ) (hδR : δ ≤ 1 + τ) :
    ¬ DistributionHarmonicOn (angularProjection F (k : ℤ)) (planeBall δ) := by
  intro hweak
  obtain ⟨σ⟩ := rightOnePoint_nonempty
  obtain ⟨ε, hε, hsmall, hγ⟩ :=
    exists_small_scaledWeylRadialKernel_multiplier_ne_zero (σ : ℂ)
      (by linarith : 0 < δ - 1)
  let ψ : Plane → ℝ := scaledWeylRadialKernel ε
  let η : ℝ := 2 * ε
  have hψ : ContDiff ℝ ∞ ψ := scaledWeylRadialKernel_contDiff ε
  have hc : HasCompactSupport ψ := scaledWeylRadialKernel_hasCompactSupport hε
  have hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z :=
    scaledWeylRadialKernel_radial ε
  have hs : tsupport ψ ⊆ Metric.closedBall (0 : Plane) η :=
    scaledWeylRadialKernel_tsupport_subset hε
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hinner : 1 < δ - η := by dsimp only [η]; linarith
  let a : RightOnePoint → ℂ := fun ν => smoothedBesselResidueCoefficient M τ ψ ν
  have ha : RapidRootCoefficients a := by
    intro b
    exact (smoothedBesselResidueCoefficient_weight_summable M (by omega) hτ hψ hc hη hs b).subtype
      (fun ν : onePoints => 0 < (ν : ℂ).re)
  have hloc : LocallyIntegrable (angularProjection F (k : ℤ)) :=
    (angularProjection_continuous hF (k : ℤ)).locallyIntegrable
  have hLap : EqOn (laplacian (mollified (angularProjection F (k : ℤ)) ψ))
      (fun _ => (0 : ℂ)) (planeBall (δ - η)) := by
    intro x hx
    exact mollified_laplacian_eq_zero_on_inner_ball hloc hweak hc hψ hs hx
  have hEqBig := mollified_angularProjection_eq_smoothed_residue_projection
    M hτ hMT hF hEq hψ.continuous hc hrad hs (k : ℤ)
  have hEqSmall : EqOn (mollified (angularProjection F (k : ℤ)) ψ)
      (angularProjection (rootCosinePlane a 1) (k : ℤ)) (planeBall (δ - η)) := by
    intro x hx
    exact hEqBig (Metric.ball_subset_ball (by linarith : δ - η ≤ (1 + τ) - η) hx)
  have hLower := complexLoweringIterate_laplacian_eqOn_zero_of_local_eq
    (show IsOpen (planeBall (δ - η)) from Metric.isOpen_ball) hEqSmall hLap k
  let b : RightOnePoint → ℂ := fun ν =>
    -(ν : ℂ) ^ 2 * (Complex.I * (ν : ℂ)) ^ k * a ν
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, rootBesselSeries b t = 0 := by
    intro t ht
    have hz := hLower (unit_interval_axis_mem_ball hinner ht)
    rw [rapidRootCosinePlane_laplacian_lowering_projection_axis ha k hk t] at hz
    have hpi : 2 * (Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    exact (mul_eq_zero.mp hz).resolve_left hpi
  have hb : Summable (fun ν : RightOnePoint => ‖b ν‖ * ‖(ν : ℂ)‖) :=
    loweringLaplacianCoefficient_weight_summable ha k
  have hcoeff := rootBesselSeries_coefficients_eq_zero hb hzero σ
  have haσ : a σ ≠ 0 := smoothedBesselResidueCoefficient_ne_zero M hτ
    σ.val.property.1 σ.val.property.2 hγ
  exact loweringLaplacianCoefficient_ne_zero k σ haσ hcoeff

/-- The genuine finite-smooth critical-radius witness, strengthened to be
nonharmonic on every centered subball of radius greater than the small radius.
This extra locality is needed for the later subcritical smoothing argument. -/
theorem exists_unitCriticalNonharmonic {τ : ℝ} (hτ : 1 < τ)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ f : Plane → ℂ,
      ContDiff ℝ (n : ℕ∞ω) f ∧
      MeanIdentityOn f 1 (planeBall ((1 + τ) - 1)) ∧
      MeanIdentityOn f τ (planeBall ((1 + τ) - τ)) ∧
      ∀ δ : ℝ, 1 < δ → δ ≤ 1 + τ → ¬ DistributionHarmonicOn f (planeBall δ) := by
  obtain ⟨M, hM, hMreg, F, hFn, _hFc, hEq, hprojected⟩ :=
    exists_unitCriticalProjectedCandidate hτ n hn
  let k : ℕ := 2 * ((besselCentralPolynomial M).natDegree + 1)
  have hk : Even k := even_two_mul _
  have hdegree : (besselCentralPolynomial M).natDegree < (k : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    dsimp only [k]
    omega
  obtain ⟨hGn, _hMfirst, _hMsecond, hMeanFirst, hMeanSecond⟩ := hprojected (k : ℤ) hdegree
  refine ⟨angularProjection F (k : ℤ), hGn, hMeanFirst, hMeanSecond, ?_⟩
  intro δ hδ hδR
  have hMT : 1 + τ < 2 * M - 1 := by
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  exact unitCritical_projected_not_distributionHarmonicOn M hM hτ hMT
    hFn.continuous hEq k hk hδ hδR

end J0RadialUniqueness
