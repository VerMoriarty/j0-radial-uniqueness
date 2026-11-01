import Solutions.J0RadialUniqueness.ClassicalWeakHarmonic
import Solutions.J0RadialUniqueness.GlobalWeyl
import Solutions.J0RadialUniqueness.BesselCosineSeries
import Solutions.J0RadialUniqueness.SpectralExponential
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual smoothing multipliers. Repeated integration by parts is carried
out on genuine compact smooth tests. It proves rapid spectral decay, rather
than adding that decay as a premise. A concrete family of scaled normalized
radial kernels also has multiplier tending to one at every fixed frequency. -/

noncomputable section
open MeasureTheory Set Filter Laplacian Metric
open scoped Topology ContDiff Convolution

namespace J0RadialUniqueness

def spectralSmoothingMultiplier (ψ : Plane → ℝ) (ν : ℂ) : ℂ :=
  ∫ y : Plane, ψ y • spectralExponential (-Complex.I * ν) y

theorem spectralSmoothingMultiplier_integrable {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (ν : ℂ) :
    Integrable (fun y : Plane => ψ y • spectralExponential (-Complex.I * ν) y) :=
  integrable_compact_test_smul_of_continuousOn
    (spectralExponential_contDiff (-Complex.I * ν)).continuous.continuousOn hψ hc
    (Set.subset_univ _)

theorem norm_spectralExponential_on_support {ψ : Plane → ℝ} {η : ℝ}
    (hs : tsupport ψ ⊆ closedBall (0 : Plane) η) (ν : ℂ) {y : Plane} (hy : ψ y ≠ 0) :
    ‖spectralExponential (-Complex.I * ν) y‖ ≤ Real.exp (η * |ν.im|) := by
  have hyn : ‖y‖ ≤ η := by
    simpa only [mem_closedBall, dist_zero_right] using hs (subset_tsupport ψ hy)
  have hy₀ : |y 0| ≤ η := by
    have hy₀' : ‖y 0‖ ≤ ‖y‖ := PiLp.norm_apply_le y 0
    have hy₀'' : |y 0| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using hy₀'
    exact hy₀''.trans hyn
  unfold spectralExponential
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : ((-Complex.I * ν) * (y 0 : ℂ)).re = ν.im * y 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  calc
    ν.im * y 0 ≤ |ν.im * y 0| := le_abs_self _
    _ = |ν.im| * |y 0| := abs_mul _ _
    _ ≤ η * |ν.im| := by nlinarith [abs_nonneg ν.im]

theorem spectralSmoothingMultiplier_norm_le {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) {η : ℝ}
    (hs : tsupport ψ ⊆ closedBall (0 : Plane) η) (ν : ℂ) :
    ‖spectralSmoothingMultiplier ψ ν‖ ≤
      (∫ y : Plane, ‖ψ y‖) * Real.exp (η * |ν.im|) := by
  have hi : Integrable (fun y : Plane => ‖ψ y‖ * Real.exp (η * |ν.im|)) :=
    (hψ.integrable_of_hasCompactSupport hc).norm.mul_const _
  have hb : ∀ᵐ y : Plane,
      ‖ψ y • spectralExponential (-Complex.I * ν) y‖ ≤
        ‖ψ y‖ * Real.exp (η * |ν.im|) := by
    filter_upwards [] with y
    by_cases hy : ψ y = 0
    · simp only [hy, zero_smul, norm_zero, zero_mul, le_refl]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_spectralExponential_on_support hs ν hy)
        (norm_nonneg _)
  have hh := norm_integral_le_of_norm_le hi hb
  simpa only [spectralSmoothingMultiplier, integral_mul_const] using hh

abbrev SpectralRealTest := TestFunction (⊤ : TopologicalSpace.Opens Plane) ℝ (⊤ : ℕ∞)

def spectralTestLaplacianIterate : ℕ → SpectralRealTest → SpectralRealTest
  | 0, ψ => ψ
  | k + 1, ψ => testLaplacianCLM ⊤ (spectralTestLaplacianIterate k ψ)

theorem spectralTestLaplacian_tsupport_subset (ψ : SpectralRealTest) :
    tsupport (testLaplacianCLM ⊤ ψ : Plane → ℝ) ⊆ tsupport (ψ : Plane → ℝ) := by
  have he : (testLaplacianCLM ⊤ ψ : Plane → ℝ) =
      directionalSecond (ψ : Plane → ℝ) distributionAxis0 distributionAxis0 +
        directionalSecond (ψ : Plane → ℝ) distributionAxis1 distributionAxis1 := by
    funext x
    change testLaplacianCLM ⊤ ψ x =
      directionalSecond (ψ : Plane → ℝ) distributionAxis0 distributionAxis0 x +
        directionalSecond (ψ : Plane → ℝ) distributionAxis1 distributionAxis1 x
    rw [testLaplacianCLM_apply, directionalSecond_eq_fderiv ψ.contDiff,
      directionalSecond_eq_fderiv ψ.contDiff, real_laplacian_eq_distributionAxes]
  rw [he]
  exact (tsupport_add _ _).trans (union_subset
    ((tsupport_fderiv_apply_subset ℝ distributionAxis0).trans
      (tsupport_fderiv_apply_subset ℝ distributionAxis0))
    ((tsupport_fderiv_apply_subset ℝ distributionAxis1).trans
      (tsupport_fderiv_apply_subset ℝ distributionAxis1)))

theorem spectralTestLaplacianIterate_tsupport_subset (k : ℕ) (ψ : SpectralRealTest) :
    tsupport (spectralTestLaplacianIterate k ψ : Plane → ℝ) ⊆ tsupport (ψ : Plane → ℝ) := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih => exact (spectralTestLaplacian_tsupport_subset _).trans ih

/-- This is the genuine compact-test Green identity, specialized to the
actual exponential eigenfunction of the Laplacian. -/
theorem spectralSmoothingMultiplier_testLaplacian (ψ : SpectralRealTest) (ν : ℂ) :
    spectralSmoothingMultiplier (testLaplacianCLM ⊤ ψ) ν =
      -(ν ^ 2) * spectralSmoothingMultiplier ψ ν := by
  have hf : ContDiffOn ℝ 2 (spectralExponential (-Complex.I * ν)) Set.univ :=
    ((contDiff_infty.mp (spectralExponential_contDiff (-Complex.I * ν))) 2).contDiffOn
  have hh := integral_laplacian_test_smul isOpen_univ hf ψ.contDiff ψ.hasCompactSupport
    (Set.subset_univ _)
  have heigen (y : Plane) : laplacian (spectralExponential (-Complex.I * ν)) y =
      -(ν ^ 2) * spectralExponential (-Complex.I * ν) y := by
    rw [laplacian_spectralExponential]
    congr 1
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  unfold spectralSmoothingMultiplier
  simp_rw [testLaplacianCLM_apply]
  rw [hh, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [heigen]
  simp only [Complex.real_smul]
  ring

theorem spectralSmoothingMultiplier_iterated_testLaplacian (k : ℕ)
    (ψ : SpectralRealTest) (ν : ℂ) :
    spectralSmoothingMultiplier (spectralTestLaplacianIterate k ψ) ν =
      (-(ν ^ 2)) ^ k * spectralSmoothingMultiplier ψ ν := by
  induction k with
  | zero => simp only [spectralTestLaplacianIterate, pow_zero, one_mul]
  | succ k ih =>
    rw [spectralTestLaplacianIterate, spectralSmoothingMultiplier_testLaplacian, ih, pow_succ]
    ring

theorem spectralSmoothingMultiplier_laplacian_power_identity (k : ℕ)
    (ψ : SpectralRealTest) (ν : ℂ) :
    ν ^ (2 * k) * spectralSmoothingMultiplier ψ ν =
      (-1 : ℂ) ^ k * spectralSmoothingMultiplier (spectralTestLaplacianIterate k ψ) ν := by
  have hsign : (-1 : ℂ) ^ k * (-(ν ^ 2)) ^ k = ν ^ (2 * k) := by
    rw [← mul_pow, show (-1 : ℂ) * -(ν ^ 2) = ν ^ 2 by ring, ← pow_mul]
  rw [spectralSmoothingMultiplier_iterated_testLaplacian, ← mul_assoc, hsign]

/-- Rapid decay is proved by repeated actual integration by parts. -/
theorem spectralSmoothingMultiplier_rapid_decay {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) {η : ℝ}
    (hs : tsupport ψ ⊆ closedBall (0 : Plane) η) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℂ, ν ≠ 0 →
      ‖spectralSmoothingMultiplier ψ ν‖ ≤
        C * Real.exp (η * |ν.im|) / ‖ν‖ ^ (2 * k) := by
  let φ : SpectralRealTest := ⟨ψ, hψ, hc, Set.subset_univ _⟩
  let φk : SpectralRealTest := spectralTestLaplacianIterate k φ
  let A : ℝ := ∫ y : Plane, ‖φk y‖
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨1 + A, by positivity, fun ν hν => ?_⟩
  have hkSupp : tsupport (φk : Plane → ℝ) ⊆ closedBall (0 : Plane) η :=
    (spectralTestLaplacianIterate_tsupport_subset k φ).trans hs
  have hb := spectralSmoothingMultiplier_norm_le φk.contDiff.continuous φk.hasCompactSupport hkSupp ν
  have hnorm : ‖spectralSmoothingMultiplier (φk : Plane → ℝ) ν‖ =
      ‖ν‖ ^ (2 * k) * ‖spectralSmoothingMultiplier ψ ν‖ := by
    have he := congrArg norm (spectralSmoothingMultiplier_iterated_testLaplacian k φ ν)
    have he' : ‖spectralSmoothingMultiplier (spectralTestLaplacianIterate k φ) ν‖ =
        ‖ν‖ ^ (2 * k) * ‖spectralSmoothingMultiplier (φ : Plane → ℝ) ν‖ := by
      simpa only [norm_mul, norm_pow, norm_neg, ← pow_mul] using he
    convert! he' using 1 <;> rfl
  apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hν) _)).mpr
  calc
    _ = ‖spectralSmoothingMultiplier (φk : Plane → ℝ) ν‖ := by rw [hnorm]; ring
    _ ≤ A * Real.exp (η * |ν.im|) := hb
    _ ≤ (1 + A) * Real.exp (η * |ν.im|) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem spectralSmoothingMultiplier_one_point_rapid_decay {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) {η : ℝ} (hη : 0 ≤ η)
    (hs : tsupport ψ ⊆ closedBall (0 : Plane) η) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℂ, ν ≠ 0 → J0 ν = 1 →
      ‖spectralSmoothingMultiplier ψ ν‖ ≤
        C * (4 : ℝ) ^ η * ‖ν‖ ^ (η - (2 * k : ℕ)) := by
  obtain ⟨C, hC, hb⟩ := spectralSmoothingMultiplier_rapid_decay hψ hc hs k
  refine ⟨C, hC, fun ν hν hJ => ?_⟩
  have hρ : 0 < ‖ν‖ := norm_pos_iff.mpr hν
  have he : Real.exp (η * |ν.im|) ≤ (4 : ℝ) ^ η * ‖ν‖ ^ η := by
    have he' : Real.exp (η * |ν.im|) ≤ (4 * ‖ν‖) ^ η := by
      rw [mul_comm η, Real.exp_mul]
      exact Real.rpow_le_rpow (Real.exp_pos _).le (one_point_exp_abs_im_bound hν hJ).le hη
    exact he'.trans_eq (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg _))
  calc
    _ ≤ C * Real.exp (η * |ν.im|) / ‖ν‖ ^ (2 * k) := hb ν hν
    _ ≤ C * ((4 : ℝ) ^ η * ‖ν‖ ^ η) / ‖ν‖ ^ (2 * k) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hρ, Real.rpow_natCast]
      ring

def scaledWeylRadialKernel (δ : ℝ) (y : Plane) : ℝ :=
  (δ ^ 2)⁻¹ * weylRadialKernel (δ⁻¹ • y)

theorem scaledWeylRadialKernel_contDiff (δ : ℝ) :
    ContDiff ℝ ∞ (scaledWeylRadialKernel δ) := by
  have hs : ContDiff ℝ ∞ (fun y : Plane => δ⁻¹ • y) :=
    by
      have hc : ContDiff ℝ ∞ (fun _ : Plane => δ⁻¹) := contDiff_const
      have hi : ContDiff ℝ ∞ (fun y : Plane => y) := contDiff_id
      convert! hc.smul hi using 1 <;> rfl
  exact contDiff_const.mul (weylRadialKernel_contDiff.comp hs)

theorem scaledWeylRadialKernel_nonneg (δ : ℝ) (y : Plane) :
    0 ≤ scaledWeylRadialKernel δ y := by
  unfold scaledWeylRadialKernel weylRadialKernel
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
    (div_nonneg (weylRawKernel_nonneg _) weylRawKernel_integral_pos.le)

theorem weylRadialKernel_norm_lt_two {y : Plane} (hy : weylRadialKernel y ≠ 0) : ‖y‖ < 2 := by
  have hn : weylRawKernel y ≠ 0 := by
    intro hz
    exact hy (by simp only [weylRadialKernel, hz, zero_div])
  have hm : y ∈ Metric.ball (0 : Plane) 2 := by
    rw [← weylRawKernel_support]
    exact hn
  simpa only [mem_ball, dist_zero_right] using hm

theorem scaledWeylRadialKernel_support_radius {δ : ℝ} (hδ : 0 < δ)
    {y : Plane} (hy : scaledWeylRadialKernel δ y ≠ 0) : ‖y‖ < 2 * δ := by
  have hn : weylRadialKernel (δ⁻¹ • y) ≠ 0 := by
    intro hz
    exact hy (by simp only [scaledWeylRadialKernel, hz, mul_zero])
  have hb := weylRadialKernel_norm_lt_two hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)] at hb
  have hh := mul_lt_mul_of_pos_left hb hδ
  rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at hh
  nlinarith

theorem scaledWeylRadialKernel_tsupport_subset {δ : ℝ} (hδ : 0 < δ) :
    tsupport (scaledWeylRadialKernel δ) ⊆ closedBall (0 : Plane) (2 * δ) := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  simpa only [mem_closedBall, dist_zero_right] using
    (scaledWeylRadialKernel_support_radius hδ hy).le

theorem scaledWeylRadialKernel_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (scaledWeylRadialKernel δ) :=
  (isCompact_closedBall (0 : Plane) (2 * δ)).of_isClosed_subset
    (isClosed_tsupport _) (scaledWeylRadialKernel_tsupport_subset hδ)

theorem scaledWeylRadialKernel_radial (δ : ℝ) (y z : Plane) (h : ‖y‖ = ‖z‖) :
    scaledWeylRadialKernel δ y = scaledWeylRadialKernel δ z := by
  unfold scaledWeylRadialKernel
  rw [weylRadialKernel_radial (δ⁻¹ • y) (δ⁻¹ • z) (by simp only [norm_smul, h])]

theorem scaledWeylRadialKernel_integral_one {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : Plane, scaledWeylRadialKernel δ y) = 1 := by
  unfold scaledWeylRadialKernel
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure Plane) weylRadialKernel hδ.le, weylRadialKernel_integral_one]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hδ.ne')

theorem scaledWeylRadialKernel_support_tendsto :
    Tendsto (fun δ : ℝ => Function.support (scaledWeylRadialKernel δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : Plane)).smallSets := by
  rw [Metric.nhds_basis_ball.smallSets.tendsto_right_iff]
  intro ε hε
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < ε / 2 :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  filter_upwards [hpos, hsmall] with δ hδ hsmall
  intro y hy
  change dist y 0 < ε
  rw [dist_zero_right]
  exact (scaledWeylRadialKernel_support_radius hδ hy).trans (by linarith)

theorem spectralSmoothingMultiplier_eq_convolution (ψ : Plane → ℝ) (ν : ℂ) :
    spectralSmoothingMultiplier ψ ν =
      (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] spectralExponential (Complex.I * ν)) 0 := by
  unfold spectralSmoothingMultiplier
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply]
  congr 1
  unfold spectralExponential
  congr 1
  simp only [zero_sub, PiLp.neg_apply, Complex.ofReal_neg]
  ring

/-- At every fixed frequency the multiplier tends to one for the concrete
normalized radial kernels. The approximate-identity theorem has its actual
nonnegativity, mass and shrinking-support inputs supplied above. -/
theorem scaledWeylRadialKernel_multiplier_tendsto (ν : ℂ) :
    Tendsto (fun δ : ℝ => spectralSmoothingMultiplier (scaledWeylRadialKernel δ) ν)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hg := (spectralExponential_contDiff (Complex.I * ν)).continuous
  have hn : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), ∀ y : Plane, 0 ≤ scaledWeylRadialKernel δ y :=
    Eventually.of_forall (fun δ => scaledWeylRadialKernel_nonneg δ)
  have hm : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), (∫ y : Plane, scaledWeylRadialKernel δ y) = 1 := by
    have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    filter_upwards [hpos] with δ hδ
    exact scaledWeylRadialKernel_integral_one hδ
  have hh := MeasureTheory.convolution_tendsto_right
    (μ := (volume : Measure Plane)) (φ := scaledWeylRadialKernel)
    (g := fun _ : ℝ => spectralExponential (Complex.I * ν)) (k := fun _ : ℝ => (0 : Plane))
    hn hm scaledWeylRadialKernel_support_tendsto
    (Eventually.of_forall (fun _ => hg.aestronglyMeasurable))
    ((hg.tendsto 0).comp tendsto_snd) tendsto_const_nhds
  simpa only [← spectralSmoothingMultiplier_eq_convolution, spectralExponential_zero] using hh

theorem exists_small_scaledWeylRadialKernel_multiplier_ne_zero (ν : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ < ε ∧
      spectralSmoothingMultiplier (scaledWeylRadialKernel δ) ν ≠ 0 := by
  have hn := (scaledWeylRadialKernel_multiplier_tendsto ν).eventually_ne (by norm_num : (1 : ℂ) ≠ 0)
  have he : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < ε / 2 :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hsmall, hnonzero⟩ := (hpos.and (he.and hn)).exists
  exact ⟨δ, hδ, by linarith, hnonzero⟩

end J0RadialUniqueness
