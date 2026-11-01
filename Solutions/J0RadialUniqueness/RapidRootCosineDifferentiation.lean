import Solutions.J0RadialUniqueness.ComplexLoweringProjection
import Solutions.J0RadialUniqueness.RootCosineMeanIdentities
import Solutions.J0RadialUniqueness.RootBesselSeriesIsolation

/-! Actual derivatives of rapidly summable root cosine series. All real
power weights are explicit intermediate coefficient conditions. Derivatives
come from the proved real exponential-series derivative theorem, and angular
integrals are exchanged with sums only after an actual summable majorant. -/

noncomputable section

open MeasureTheory Set Filter Laplacian
open scoped Topology ContDiff Interval

set_option maxHeartbeats 1000000

namespace J0RadialUniqueness

def RapidRootCoefficients (a : RightOnePoint → ℂ) : Prop :=
  ∀ b : ℝ, Summable (fun ν : RightOnePoint => ‖a ν‖ * ‖(ν : ℂ)‖ ^ b)

def rootFrequencyPowerCoefficient (k : ℕ) (a : RightOnePoint → ℂ) (ν : RightOnePoint) : ℂ :=
  (Complex.I * (ν : ℂ)) ^ k * a ν

theorem rapidRootCoefficients_frequencyPower {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) :
    RapidRootCoefficients (rootFrequencyPowerCoefficient k a) := by
  intro b
  apply (ha (b + k)).congr
  intro ν
  have hρ : 0 < ‖(ν : ℂ)‖ := norm_pos_iff.mpr ν.val.property.1
  simp only [rootFrequencyPowerCoefficient, norm_mul, norm_pow, Complex.norm_I, one_mul]
  rw [Real.rpow_add hρ, Real.rpow_natCast]
  ring

def rapidRootCosineDerivativeReal (a : RightOnePoint → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (rootExponentialDerivativeSeries a Complex.I k t +
    rootExponentialDerivativeSeries a (-Complex.I) k t) / 2

def rapidRootCosineDerivativePlane (a : RightOnePoint → ℂ) (k : ℕ) (x : Plane) : ℂ :=
  rapidRootCosineDerivativeReal a k (x 0)

theorem rapidRootExponentialSeries_hasDerivAt {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I)
    (k : ℕ) (t : ℝ) :
    HasDerivAt (rootExponentialDerivativeSeries a σ k)
      (rootExponentialDerivativeSeries a σ (k + 1) t) t := by
  let T : ℝ := |t| + 1
  have hT : 0 < T := by dsimp only [T]; positivity
  have ht : t ∈ Ioo (-T) T := by
    dsimp only [T]
    constructor <;> linarith [le_abs_self t, neg_abs_le t]
  exact rootExponentialDerivativeSeries_hasDerivAt a hσ k hT
    (ha (T + k)) (ha (T + (k + 1 : ℕ))) ht

theorem rapidRootExponentialSeries_contDiff {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I)
    (k : ℕ) : ContDiff ℝ ∞ (rootExponentialDerivativeSeries a σ k) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  apply contDiff_iff_contDiffAt.mpr
  intro t
  let T : ℝ := |t| + 1
  have hT : 0 < T := by dsimp only [T]; positivity
  have ht : t ∈ Ioo (-T) T := by
    dsimp only [T]
    constructor <;> linarith [le_abs_self t, neg_abs_le t]
  exact (rootExponentialDerivativeSeries_contDiffOn a hσ hT n k
    (fun j _ => ha (T + (k + j : ℕ)))).contDiffAt (Ioo_mem_nhds ht.1 ht.2)

theorem rapidRootCosineDerivativeReal_hasDerivAt {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) (t : ℝ) :
    HasDerivAt (rapidRootCosineDerivativeReal a k)
      (rapidRootCosineDerivativeReal a (k + 1) t) t := by
  exact ((rapidRootExponentialSeries_hasDerivAt ha (Or.inl rfl) k t).add
    (rapidRootExponentialSeries_hasDerivAt ha (Or.inr rfl) k t)).div_const 2

theorem rapidRootCosineDerivativeReal_contDiff {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) :
    ContDiff ℝ ∞ (rapidRootCosineDerivativeReal a k) :=
  ((rapidRootExponentialSeries_contDiff ha (Or.inl rfl) k).add
    (rapidRootExponentialSeries_contDiff ha (Or.inr rfl) k)).div_const 2

theorem rapidRootCosineDerivativePlane_contDiff {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) :
    ContDiff ℝ ∞ (rapidRootCosineDerivativePlane a k) := by
  let p : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  have hp : ContDiff ℝ ∞ (fun x : Plane => x 0) := by
    convert! p.contDiff using 1 <;> rfl
  exact (rapidRootCosineDerivativeReal_contDiff ha k).comp hp

theorem rapidRootCosineDerivativeReal_zero {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (t : ℝ) :
    rapidRootCosineDerivativeReal a 0 t = rootCosineSeries a t := by
  exact (rootCosineSeries_eq_exponential_average a (abs_nonneg t) (ha |t|) le_rfl).symm

theorem rapidRootCosineDerivativePlane_zero {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) :
    rapidRootCosineDerivativePlane a 0 = rootCosinePlane a 1 := by
  funext x
  simp only [rapidRootCosineDerivativePlane, rootCosinePlane, div_one,
    rapidRootCosineDerivativeReal_zero ha]

theorem rapidRootCosinePlane_contDiff {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) : ContDiff ℝ ∞ (rootCosinePlane a 1) := by
  rw [← rapidRootCosineDerivativePlane_zero ha]
  exact rapidRootCosineDerivativePlane_contDiff ha 0

/-- Evaluation of the full real Fréchet chain rule on an arbitrary plane
direction. In particular, the second coordinate contributes zero. -/
theorem directionalKernel_coordinate_of_hasDerivAt {h : ℝ → ℂ} {d : ℂ}
    {x : Plane} (hh : HasDerivAt h d (x 0)) (v : Plane) :
    directionalKernel (fun y : Plane => h (y 0)) v x = (v 0 : ℂ) * d := by
  let p : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  have hd := hh.hasFDerivAt.comp x p.hasFDerivAt
  have hd' : HasFDerivAt (fun y : Plane => h (y 0))
      ((ContinuousLinearMap.toSpanSingleton ℝ d).comp p) x := by
    convert! hd using 1 <;> rfl
  change fderiv ℝ (fun y : Plane => h (y 0)) x v = _
  rw [hd'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.real_smul]
  rfl

theorem directionalKernel_rapidRootCosineDerivativePlane {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) (v x : Plane) :
    directionalKernel (rapidRootCosineDerivativePlane a k) v x =
      (v 0 : ℂ) * rapidRootCosineDerivativePlane a (k + 1) x :=
  directionalKernel_coordinate_of_hasDerivAt
    (rapidRootCosineDerivativeReal_hasDerivAt ha k (x 0)) v

theorem complexLowering_rapidRootCosineDerivativePlane {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) (x : Plane) :
    complexLowering (rapidRootCosineDerivativePlane a k) x =
      rapidRootCosineDerivativePlane a (k + 1) x := by
  unfold complexLowering
  rw [directionalKernel_rapidRootCosineDerivativePlane ha,
    directionalKernel_rapidRootCosineDerivativePlane ha]
  simp [distributionAxis0, distributionAxis1, EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem complexLoweringIterate_rapidRootCosineDerivativePlane {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (j k : ℕ) (x : Plane) :
    complexLoweringIterate k (rapidRootCosineDerivativePlane a j) x =
      rapidRootCosineDerivativePlane a (j + k) x := by
  induction k generalizing x with
  | zero => simp only [complexLoweringIterate, Nat.add_zero]
  | succ k ih =>
      have he : complexLoweringIterate k (rapidRootCosineDerivativePlane a j) =
          rapidRootCosineDerivativePlane a (j + k) := funext ih
      rw [complexLoweringIterate, he, complexLowering_rapidRootCosineDerivativePlane ha]
      congr 1

theorem laplacian_rapidRootCosineDerivativePlane {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) (x : Plane) :
    laplacian (rapidRootCosineDerivativePlane a k) x =
      rapidRootCosineDerivativePlane a (k + 2) x := by
  have hf₂ : ContDiff ℝ 2 (rapidRootCosineDerivativePlane a k) :=
    (contDiff_infty.mp (rapidRootCosineDerivativePlane_contDiff ha k)) 2
  have he₀ : directionalKernel (rapidRootCosineDerivativePlane a k) distributionAxis0 =
      rapidRootCosineDerivativePlane a (k + 1) := by
    funext y
    rw [directionalKernel_rapidRootCosineDerivativePlane ha]
    simp [distributionAxis0, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have he₁ : directionalKernel (rapidRootCosineDerivativePlane a k) distributionAxis1 =
      fun _ : Plane => (0 : ℂ) := by
    funext y
    rw [directionalKernel_rapidRootCosineDerivativePlane ha]
    simp [distributionAxis1, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  rw [laplacian_eq_directionalSecond_on isOpen_univ hf₂.contDiffOn (mem_univ x)]
  unfold directionalSecond
  rw [he₀, he₁, directionalKernel_rapidRootCosineDerivativePlane ha]
  simp [directionalKernel, distributionAxis0, EuclideanSpace.basisFun_apply,
    PiLp.single_apply, Nat.add_assoc]

/-- For even orders both exponential branches have the same power, hence
the actual differentiated sum is again a cosine sum. -/
theorem rapidRootCosineDerivativeReal_even {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) (hk : Even k) (t : ℝ) :
    rapidRootCosineDerivativeReal a k t =
      rootCosineSeries (rootFrequencyPowerCoefficient k a) t := by
  rw [rootCosineSeries_eq_exponential_average _ (abs_nonneg t)
    (rapidRootCoefficients_frequencyPower ha k |t|) le_rfl]
  have hp : rootExponentialDerivativeSeries a Complex.I k t =
      rootExponentialDerivativeSeries (rootFrequencyPowerCoefficient k a) Complex.I 0 t := by
    unfold rootExponentialDerivativeSeries
    apply tsum_congr
    intro ν
    unfold rootExponentialDerivativeTerm rootFrequencyPowerCoefficient
    simp only [pow_zero, mul_one]
    ring
  have hm : rootExponentialDerivativeSeries a (-Complex.I) k t =
      rootExponentialDerivativeSeries (rootFrequencyPowerCoefficient k a) (-Complex.I) 0 t := by
    unfold rootExponentialDerivativeSeries
    apply tsum_congr
    intro ν
    have he : (-Complex.I * (ν : ℂ)) ^ k = (Complex.I * (ν : ℂ)) ^ k := by
      rw [show -Complex.I * (ν : ℂ) = -(Complex.I * (ν : ℂ)) by ring, hk.neg_pow]
    unfold rootExponentialDerivativeTerm rootFrequencyPowerCoefficient
    simp only [pow_zero, mul_one]
    rw [he]
    ring
  exact congrArg₂ (fun u v : ℂ => (u + v) / 2) hp hm

theorem complexLoweringIterate_rapidRootCosinePlane_even {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (k : ℕ) (hk : Even k) (x : Plane) :
    complexLoweringIterate k (rootCosinePlane a 1) x =
      rootCosinePlane (rootFrequencyPowerCoefficient k a) 1 x := by
  rw [← rapidRootCosineDerivativePlane_zero ha,
    complexLoweringIterate_rapidRootCosineDerivativePlane ha]
  simp only [Nat.zero_add, rapidRootCosineDerivativePlane, rootCosinePlane, div_one]
  exact rapidRootCosineDerivativeReal_even ha k hk (x 0)

theorem laplacian_rapidRootCosinePlane {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (x : Plane) :
    laplacian (rootCosinePlane a 1) x =
      rootCosinePlane (fun ν => -(ν : ℂ) ^ 2 * a ν) 1 x := by
  rw [← rapidRootCosineDerivativePlane_zero ha, laplacian_rapidRootCosineDerivativePlane ha]
  change rapidRootCosineDerivativeReal a 2 (x 0) = _
  rw [rapidRootCosineDerivativeReal_even ha 2 (by norm_num)]
  have he : rootFrequencyPowerCoefficient 2 a =
      fun ν : RightOnePoint => -(ν : ℂ) ^ 2 * a ν := by
    funext ν
    unfold rootFrequencyPowerCoefficient
    rw [mul_pow, Complex.I_sq]
    ring
  rw [he]
  simp only [rootCosinePlane, div_one]

theorem complexLoweringIterate_angularProjection {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (m : ℤ) (k : ℕ) (x : Plane) :
    complexLoweringIterate k (angularProjection f m) x =
      angularProjection (complexLoweringIterate k f) (m - (k : ℤ)) x := by
  induction k generalizing x with
  | zero => simp only [complexLoweringIterate, Nat.cast_zero, sub_zero]
  | succ k ih =>
      have he : complexLoweringIterate k (angularProjection f m) =
          angularProjection (complexLoweringIterate k f) (m - (k : ℤ)) := funext ih
      rw [complexLoweringIterate, he,
        complexLowering_angularProjection (complexLoweringIterate_contDiff hf k)]
      have hind : m - (k : ℤ) - 1 = m - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hind]
      rfl

/-- A real-angle dominated-convergence argument proves the actual zero-mode
Bessel series formula. Compact angular sampling supplies a power majorant at
every real radius, including negative radii and the origin. -/
theorem angularProjection_zero_rapidRootCosinePlane_axis {a : RightOnePoint → ℂ}
    (ha : RapidRootCoefficients a) (t : ℝ) :
    angularProjection (rootCosinePlane a 1) 0 (t • distributionAxis0) =
      (2 * (Real.pi : ℂ)) * rootBesselSeries a t := by
  let T : ℝ := |t|
  let B : RightOnePoint → ℝ := fun ν => (4 : ℝ) ^ T * (‖a ν‖ * ‖(ν : ℂ)‖ ^ T)
  have hT : 0 ≤ T := abs_nonneg t
  have hB : Summable B := (ha T).mul_left _
  have hcoord (θ : ℝ) : |(planeRotation θ (t • distributionAxis0)) 0| ≤ T := by
    calc
      _ ≤ ‖planeRotation θ (t • distributionAxis0)‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le (planeRotation θ (t • distributionAxis0)) 0
      _ = T := by
        rw [(planeRotation θ).norm_map, norm_smul, Real.norm_eq_abs]
        simp only [distributionAxis0, OrthonormalBasis.norm_eq_one, mul_one, T]
  have hsum : HasSum
      (fun ν : RightOnePoint => ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        helmholtzAngularWeight 0 θ *
          (a ν * spectralCosine (ν : ℂ) (planeRotation θ (t • distributionAxis0))))
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        helmholtzAngularWeight 0 θ * rootCosinePlane a 1
          (planeRotation θ (t • distributionAxis0))) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun ν (_ : ℝ) => B ν)
    · intro ν
      have hfν : Continuous (fun y : Plane => a ν * spectralCosine (ν : ℂ) y) :=
        continuous_const.mul (spectralCosine_contDiff (ν : ℂ)).continuous
      have hc := continuous_angularProjection_integrand hfν 0
      exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro ν
      exact Eventually.of_forall fun θ _ => by
        simp only [helmholtzAngularWeight, Int.cast_zero, mul_zero, zero_mul,
          Complex.exp_zero, one_mul]
        exact rootCosineSeries_norm_majorant a hT (hcoord θ) ν
    · exact Eventually.of_forall fun _ _ => hB
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ _ => by
        have hs := (rootCosineSeries_summable a hT (ha T) (hcoord θ)).hasSum
        simpa only [rootCosinePlane, div_one, rootCosineSeries, spectralCosine,
          helmholtzAngularWeight, Int.cast_zero, mul_zero, zero_mul,
          Complex.exp_zero, one_mul] using hs
  have heach (ν : RightOnePoint) :
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        helmholtzAngularWeight 0 θ *
          (a ν * spectralCosine (ν : ℂ) (planeRotation θ (t • distributionAxis0)))) =
        a ν * ((2 * (Real.pi : ℂ)) * J0 ((t : ℂ) * (ν : ℂ))) := by
    calc
      _ = angularProjection (fun y : Plane => a ν * spectralCosine (ν : ℂ) y)
          0 (t • distributionAxis0) :=
        (angularProjection_eq_integral (fun y : Plane => a ν * spectralCosine (ν : ℂ) y)
          0 (t • distributionAxis0)).symm
      _ = _ := by
        rw [loweringAngularProjection_const_mul, angularProjection_zero_spectralCosine_axis]
  simp_rw [heach] at hsum
  have hval : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight 0 θ * rootCosinePlane a 1
        (planeRotation θ (t • distributionAxis0))) =
      angularProjection (rootCosinePlane a 1) 0 (t • distributionAxis0) :=
    (angularProjection_eq_integral (rootCosinePlane a 1) 0 (t • distributionAxis0)).symm
  rw [hval] at hsum
  calc
    _ = ∑' ν : RightOnePoint, a ν * ((2 * (Real.pi : ℂ)) * J0 ((t : ℂ) * (ν : ℂ))) :=
      hsum.tsum_eq.symm
    _ = _ := by
      unfold rootBesselSeries
      rw [← tsum_mul_left]
      apply tsum_congr
      intro ν
      ring

/-- The final axis identity is derived from actual series derivatives,
the actual Laplacian/projection commutation, and the proved lowering phase.
No infinite derivative exchange remains as a premise. -/
theorem rapidRootCosinePlane_laplacian_lowering_projection_axis
    {a : RightOnePoint → ℂ} (ha : RapidRootCoefficients a)
    (k : ℕ) (hk : Even k) (t : ℝ) :
    complexLoweringIterate k
        (laplacian (angularProjection (rootCosinePlane a 1) (k : ℤ)))
        (t • distributionAxis0) =
      (2 * (Real.pi : ℂ)) * rootBesselSeries
        (fun ν : RightOnePoint => -(ν : ℂ) ^ 2 * (Complex.I * (ν : ℂ)) ^ k * a ν) t := by
  let b : RightOnePoint → ℂ := fun ν => -(ν : ℂ) ^ 2 * a ν
  have hb_eq : b = rootFrequencyPowerCoefficient 2 a := by
    funext ν
    dsimp only [b, rootFrequencyPowerCoefficient]
    rw [mul_pow, Complex.I_sq]
    ring
  have hb : RapidRootCoefficients b := by
    rw [hb_eq]
    exact rapidRootCoefficients_frequencyPower ha 2
  have hΔ : laplacian (rootCosinePlane a 1) = rootCosinePlane b 1 :=
    funext (laplacian_rapidRootCosinePlane ha)
  have hp : laplacian (angularProjection (rootCosinePlane a 1) (k : ℤ)) =
      angularProjection (rootCosinePlane b 1) (k : ℤ) := by
    funext x
    rw [laplacian_angularProjection
      ((contDiff_infty.mp (rapidRootCosinePlane_contDiff ha)) 2), hΔ]
  rw [hp, complexLoweringIterate_angularProjection (rapidRootCosinePlane_contDiff hb)]
  simp only [sub_self]
  have hd : complexLoweringIterate k (rootCosinePlane b 1) =
      rootCosinePlane (rootFrequencyPowerCoefficient k b) 1 :=
    funext (complexLoweringIterate_rapidRootCosinePlane_even hb k hk)
  rw [hd, angularProjection_zero_rapidRootCosinePlane_axis
    (rapidRootCoefficients_frequencyPower hb k)]
  have hc : rootFrequencyPowerCoefficient k b = fun ν : RightOnePoint =>
      -(ν : ℂ) ^ 2 * (Complex.I * (ν : ℂ)) ^ k * a ν := by
    funext ν
    dsimp only [rootFrequencyPowerCoefficient, b]
    ring
  rw [hc]

end J0RadialUniqueness
