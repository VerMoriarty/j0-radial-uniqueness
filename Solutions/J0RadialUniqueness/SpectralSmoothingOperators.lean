import Solutions.J0RadialUniqueness.SpectralSmoothingMultiplier
import Solutions.J0RadialUniqueness.SpectralCosine
import Solutions.J0RadialUniqueness.AngularProjectionOperators
import Solutions.J0RadialUniqueness.LocalConvolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Actual smoothing of the spectral modes and of their angular projections.
The evenness of the multiplier is proved by the measure-preserving negation
map. Rotation of a radial convolution is proved by the actual linear isometry
change of variables. The final exchange of the plane and angular integrals
uses an explicit product-L1 bound before Fubini is applied. -/

noncomputable section
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

namespace J0RadialUniqueness

theorem localConvolution_integrable_of_continuous {ψ : Plane → ℝ} {f : Plane → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hf : Continuous f) (x : Plane) :
    Integrable (fun y : Plane => ψ y • f (x - y)) := by
  exact integrable_compact_test_smul_of_continuousOn
    (hf.comp (continuous_const.sub continuous_id)).continuousOn hψ hc (Set.subset_univ _)

theorem spectralExponential_sub (lam : ℂ) (x y : Plane) :
    spectralExponential lam (x - y) =
      spectralExponential lam x * spectralExponential (-lam) y := by
  unfold spectralExponential
  rw [← Complex.exp_add]
  congr 1
  simp only [PiLp.sub_apply, Complex.ofReal_sub]
  ring

/-- Before radial symmetry is used, the convolution has the multiplier with
the opposite frequency to that of the exponential in its right factor. -/
theorem localConvolution_spectralExponential_general (ψ : Plane → ℝ) (lam : ℂ) (x : Plane) :
    localConvolution ψ (spectralExponential lam) x =
      (∫ y : Plane, ψ y • spectralExponential (-lam) y) * spectralExponential lam x := by
  unfold localConvolution
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [spectralExponential_sub]
    simp only [Complex.real_smul]
    ring

/-- Radiality includes evenness. The equality is obtained from the actual
Lebesgue integral under the negation isometry, not from a Fourier premise. -/
theorem spectralSmoothingMultiplier_neg {ψ : Plane → ℝ}
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z) (ν : ℂ) :
    spectralSmoothingMultiplier ψ (-ν) = spectralSmoothingMultiplier ψ ν := by
  let e : Plane ≃ₗᵢ[ℝ] Plane := LinearIsometryEquiv.neg ℝ
  calc
    _ = ∫ y : Plane, ψ (e y) • spectralExponential (-Complex.I * (-ν)) (e y) :=
      (e.measurePreserving.integral_comp
        e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun y : Plane =>
        ψ y • spectralExponential (-Complex.I * (-ν)) y)).symm
    _ = _ := by
      unfold spectralSmoothingMultiplier
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        have hψy : ψ (e y) = ψ y := hrad _ _ (e.norm_map y)
        rw [hψy]
        congr 1
        change spectralExponential (-Complex.I * (-ν)) (-y) =
          spectralExponential (-Complex.I * ν) y
        unfold spectralExponential
        congr 1
        simp only [PiLp.neg_apply, Complex.ofReal_neg]
        ring

theorem localConvolution_spectralExponential_pos (ψ : Plane → ℝ) (ν : ℂ) (x : Plane) :
    localConvolution ψ (spectralExponential (Complex.I * ν)) x =
      spectralSmoothingMultiplier ψ ν * spectralExponential (Complex.I * ν) x := by
  rw [localConvolution_spectralExponential_general]
  have hfreq : -(Complex.I * ν) = -Complex.I * ν := by ring
  rw [hfreq]
  rfl

theorem localConvolution_spectralExponential {ψ : Plane → ℝ}
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z) (ν : ℂ) (x : Plane) :
    localConvolution ψ (spectralExponential (-Complex.I * ν)) x =
      spectralSmoothingMultiplier ψ ν * spectralExponential (-Complex.I * ν) x := by
  rw [localConvolution_spectralExponential_general]
  have hfreq : -(-Complex.I * ν) = -Complex.I * (-ν) := by ring
  rw [hfreq]
  change spectralSmoothingMultiplier ψ (-ν) * spectralExponential (-Complex.I * ν) x = _
  rw [spectralSmoothingMultiplier_neg hrad]

/-- The genuine cosine mode is an eigenfunction of every compact continuous
radial smoothing kernel, including the kernels used for rapid decay. -/
theorem localConvolution_spectralCosine {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z) (ν : ℂ) (x : Plane) :
    localConvolution ψ (spectralCosine ν) x =
      spectralSmoothingMultiplier ψ ν * spectralCosine ν x := by
  have h₁ := localConvolution_integrable_of_continuous hψ hc
    (spectralExponential_contDiff (Complex.I * ν)).continuous x
  have h₂ := localConvolution_integrable_of_continuous hψ hc
    (spectralExponential_contDiff (-Complex.I * ν)).continuous x
  have hfun : (fun y : Plane => ψ y • spectralCosine ν (x - y)) =
      fun y : Plane => (1 / 2 : ℂ) *
        (ψ y • spectralExponential (Complex.I * ν) (x - y) +
          ψ y • spectralExponential (-Complex.I * ν) (x - y)) := by
    funext y
    rw [spectralCosine_eq_exponential_combination]
    simp only [Complex.real_smul]
    ring
  unfold localConvolution
  rw [hfun, integral_const_mul, integral_add h₁ h₂]
  change (1 / 2 : ℂ) *
    (localConvolution ψ (spectralExponential (Complex.I * ν)) x +
      localConvolution ψ (spectralExponential (-Complex.I * ν)) x) = _
  rw [localConvolution_spectralExponential_pos,
    localConvolution_spectralExponential hrad,
    spectralCosine_eq_exponential_combination]
  ring

/-- The change of variables is a measure-preserving linear isometry. No
smoothness of the right factor is needed for this identity of integrals. -/
theorem localConvolution_comp_planeRotation {ψ : Plane → ℝ}
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z)
    (f : Plane → ℂ) (θ : ℝ) (x : Plane) :
    localConvolution ψ (fun y => f (planeRotation θ y)) x =
      localConvolution ψ f (planeRotation θ x) := by
  let e := planeRotation θ
  calc
    _ = ∫ y : Plane, ψ (e y) • f (e x - e y) := by
      unfold localConvolution
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [hrad (e y) y (e.norm_map y), ← e.map_sub]
    _ = _ := e.measurePreserving.integral_comp
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun y : Plane => ψ y • f (e x - y))

theorem norm_helmholtzAngularWeight (m : ℤ) (θ : ℝ) :
    ‖helmholtzAngularWeight m θ‖ = 1 := by
  have hre : ((-Complex.I * (m : ℂ)) * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [helmholtzAngularWeight, Complex.norm_exp, hre, Real.exp_zero]

/-- The actual unsmoothed angular integrand, before multiplication by the
compact real kernel. Naming it keeps each analytic proof local. -/
def smoothingAngularCore (f : Plane → ℂ) (m : ℤ) (x : Plane) (p : ℝ × Plane) : ℂ :=
  helmholtzAngularWeight m p.1 * f (planeRotation p.1 (x - p.2))

theorem continuous_smoothingAngularCore {f : Plane → ℂ} (hf : Continuous f)
    (m : ℤ) (x : Plane) : Continuous (smoothingAngularCore f m x) := by
  have harg : Continuous (fun p : ℝ × Plane => (x - p.2, p.1)) :=
    (continuous_const.sub continuous_snd).prodMk continuous_fst
  have hh : Continuous ((fun q : Plane × ℝ => planeRotation q.2 q.1) ∘
      (fun p : ℝ × Plane => (x - p.2, p.1))) :=
    continuous_planeRotation_joint.comp harg
  have hR : Continuous (fun p : ℝ × Plane => planeRotation p.1 (x - p.2)) := by
    simpa only [Function.comp_def] using hh
  have hw : Continuous (fun p : ℝ × Plane => helmholtzAngularWeight m p.1) :=
    (continuous_helmholtzAngularWeight m).comp continuous_fst
  have hv : Continuous (fun p : ℝ × Plane => f (planeRotation p.1 (x - p.2))) :=
    hf.comp hR
  change Continuous (fun p : ℝ × Plane =>
    helmholtzAngularWeight m p.1 * f (planeRotation p.1 (x - p.2)))
  apply Continuous.mul
  · exact hw
  · exact hv

/-- A compact sampling ball gives an actual uniform norm bound on the
support of the smoothing kernel, independently of the angle. -/
theorem smoothingAngularCore_bound_on_kernel_support {ψ : Plane → ℝ} {f : Plane → ℂ}
    (hc : HasCompactSupport ψ) (hf : Continuous f) (m : ℤ) (x : Plane) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × Plane, ψ p.2 ≠ 0 → ‖smoothingAngularCore f m x p‖ ≤ C := by
  obtain ⟨r, _, hs⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : Plane) (‖x‖ + r)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C₀ 0, le_max_right _ _, fun p hy => ?_⟩
  have hyr : ‖p.2‖ ≤ r := by
    exact (show ‖p.2‖ < r by
      simpa only [Metric.mem_ball, dist_zero_right] using hs (subset_tsupport ψ hy)).le
  have hinside : planeRotation p.1 (x - p.2) ∈ closedBall (0 : Plane) (‖x‖ + r) := by
    rw [mem_closedBall, dist_zero_right, (planeRotation p.1).norm_map]
    exact (norm_sub_le _ _).trans (add_le_add (le_refl ‖x‖) hyr)
  have hb : ‖f (planeRotation p.1 (x - p.2))‖ ≤ max C₀ 0 :=
    (hC₀ _ hinside).trans (le_max_left _ _)
  simpa only [smoothingAngularCore, norm_mul, norm_helmholtzAngularWeight, one_mul] using hb

/-- A compact L1 kernel times a continuous core that is uniformly bounded
on its support is jointly L1 on the actual finite angular interval. -/
theorem compactKernel_angular_smul_integrable {ψ : Plane → ℝ} {v : ℝ × Plane → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hv : Continuous v)
    (C : ℝ) (hbound : ∀ p : ℝ × Plane, ψ p.2 ≠ 0 → ‖v p‖ ≤ C) :
    Integrable (fun p : ℝ × Plane => ψ p.2 • v p)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let ρ : Measure (ℝ × Plane) := μ.prod (volume : Measure Plane)
  have hψI : Integrable ψ (volume : Measure Plane) :=
    hψ.integrable_of_hasCompactSupport hc
  have hθI : Integrable (fun _θ : ℝ => (1 : ℝ)) μ :=
    (continuous_const : Continuous (fun _θ : ℝ => (1 : ℝ))).integrableOn_Ioc
  have hprod : Integrable (fun p : ℝ × Plane => (1 : ℝ) * ‖ψ p.2‖) ρ :=
    hθI.mul_prod hψI.norm
  have hbase : Integrable (fun p : ℝ × Plane => ‖ψ p.2‖ * C) ρ := by
    convert! hprod.mul_const C using 1 <;> simp only [one_mul]
  have hG : Continuous (fun p : ℝ × Plane => ψ p.2 • v p) :=
    (hψ.comp continuous_snd).smul hv
  have hmeas : AEStronglyMeasurable (fun p : ℝ × Plane => ψ p.2 • v p) ρ :=
    hG.aestronglyMeasurable
  change Integrable (fun p : ℝ × Plane => ψ p.2 • v p) ρ
  apply hbase.mono' hmeas
  exact Eventually.of_forall fun p => by
    change ‖ψ p.2 • v p‖ ≤ ‖ψ p.2‖ * C
    by_cases hy : ψ p.2 = 0
    · simp only [hy, zero_smul, norm_zero, zero_mul, le_refl]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound p hy) (norm_nonneg _)

/-- The compact kernel and the bounded sampled ball give joint L1 on the
finite angular interval. This supplies the integrability needed by Fubini. -/
theorem angularProjection_localConvolution_integrand_integrable
    {ψ : Plane → ℝ} {f : Plane → ℂ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hf : Continuous f) (m : ℤ) (x : Plane) :
    Integrable (fun p : ℝ × Plane => ψ p.2 •
      (helmholtzAngularWeight m p.1 * f (planeRotation p.1 (x - p.2))))
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod volume) := by
  obtain ⟨C, _, hC⟩ := smoothingAngularCore_bound_on_kernel_support hc hf m x
  exact compactKernel_angular_smul_integrable hψ hc
    (continuous_smoothingAngularCore hf m x) C hC

/-- Radial compact smoothing commutes with the actual angular Fourier
projection. The plane change of variables and the double-integral L1 estimate
are both proved above; neither is an additional premise of this theorem. -/
theorem angularProjection_localConvolution_comm
    {ψ : Plane → ℝ} {f : Plane → ℂ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hf : Continuous f)
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z) (m : ℤ) (x : Plane) :
    angularProjection (localConvolution ψ f) m x =
      localConvolution ψ (angularProjection f m) x := by
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hI := angularProjection_localConvolution_integrand_integrable hψ hc hf m x
  have hswap := integral_integral_swap
    (f := fun θ : ℝ => fun y : Plane => ψ y •
      (helmholtzAngularWeight m θ * f (planeRotation θ (x - y)))) hI
  calc
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ∫ y : Plane, ψ y •
        (helmholtzAngularWeight m θ * f (planeRotation θ (x - y))) := by
      rw [angularProjection_eq_integral]
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [← localConvolution_comp_planeRotation hrad f θ x]
      unfold localConvolution
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp only [Complex.real_smul]
        ring
    _ = ∫ y : Plane, ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ψ y •
        (helmholtzAngularWeight m θ * f (planeRotation θ (x - y))) := by
      rw [intervalIntegral.integral_of_le hle, hswap]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => (intervalIntegral.integral_of_le hle).symm
    _ = _ := by
      unfold localConvolution
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [angularProjection_eq_integral, intervalIntegral.integral_smul]

theorem angularProjection_const_mul (c : ℂ) (f : Plane → ℂ) (m : ℤ) (x : Plane) :
    angularProjection (fun y => c * f y) m x = c * angularProjection f m x := by
  simp only [angularProjection_eq_integral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  ring

/-- The same actual multiplier therefore acts on every projected cosine
mode. This is the smoothing bridge used before spectral uniqueness. -/
theorem localConvolution_angularProjection_spectralCosine
    {ψ : Plane → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hrad : ∀ y z : Plane, ‖y‖ = ‖z‖ → ψ y = ψ z)
    (ν : ℂ) (m : ℤ) (x : Plane) :
    localConvolution ψ (angularProjection (spectralCosine ν) m) x =
      spectralSmoothingMultiplier ψ ν * angularProjection (spectralCosine ν) m x := by
  rw [← angularProjection_localConvolution_comm hψ hc (spectralCosine_contDiff ν).continuous hrad]
  have hfun : localConvolution ψ (spectralCosine ν) =
      fun y => spectralSmoothingMultiplier ψ ν * spectralCosine ν y :=
    funext (localConvolution_spectralCosine hψ hc hrad ν)
  rw [hfun, angularProjection_const_mul]

end J0RadialUniqueness
