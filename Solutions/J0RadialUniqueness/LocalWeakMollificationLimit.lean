import Solutions.J0RadialUniqueness.GlobalWeyl
import Solutions.J0RadialUniqueness.LocalMeanMollification
import Solutions.J0RadialUniqueness.WeakRepresentative
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Weak equations pass back from the actual normalized bump smoothings.
The pairing exchange has a product L1 proof before Fubini. A bounded test and
the nonnegative unit-mass kernels then give one fixed integrable majorant,
so that the final limiting step is genuine dominated convergence. -/

noncomputable section
open MeasureTheory Set Filter Laplacian
open scoped ContDiff Convolution Topology

namespace J0RadialUniqueness

def dualKernelAverage (ψ h : Plane → ℝ) (y : Plane) : ℝ :=
  ∫ x : Plane, ψ (x - y) * h x

/-- The joint test/smoothing pairing is L1. Boundedness of the test is combined
with the actual product convolution-integrand L1 theorem. -/
theorem mollified_pairing_integrand_integrable {f : Plane → ℂ} {ψ h : Plane → ℝ}
    (hf : Integrable f) (hψ : Integrable ψ) (hcψ : Continuous ψ)
    (hh : Continuous h) {M : ℝ} (hM : ∀ x : Plane, ‖h x‖ ≤ M) :
    Integrable (fun p : Plane × Plane =>
      (h p.1 : ℂ) * (ψ (p.1 - p.2) • f p.2)) (volume.prod volume) := by
  have hbase : Integrable (fun p : Plane × Plane =>
      M * (‖f p.2‖ * ‖ψ (p.1 - p.2)‖)) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      (hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hψ.norm).const_mul M
  have hm : AEStronglyMeasurable (fun p : Plane × Plane =>
      (h p.1 : ℂ) * (ψ (p.1 - p.2) • f p.2)) (volume.prod volume) :=
    (Complex.continuous_ofReal.comp (hh.comp continuous_fst)).aestronglyMeasurable.mul
      ((hcψ.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.smul
        hf.aestronglyMeasurable.comp_snd)
  apply hbase.mono' hm
  filter_upwards [] with p
  simp only [norm_mul, norm_smul, Complex.norm_real]
  calc
    ‖h p.1‖ * (‖ψ (p.1 - p.2)‖ * ‖f p.2‖) ≤
        M * (‖ψ (p.1 - p.2)‖ * ‖f p.2‖) :=
      mul_le_mul_of_nonneg_right (hM p.1) (by positivity)
    _ = _ := by ring

/-- Fubini for the actual weak pairing, with the genuine joint L1 certificate
constructed above. The right side is the test averaged against the reflected
kernel, rather than an unproved pairing-limit premise. -/
theorem mollified_pairing_eq_dualKernelAverage {f : Plane → ℂ} {ψ h : Plane → ℝ}
    (hf : Integrable f) (hψ : Integrable ψ) (hcψ : Continuous ψ)
    (hh : Continuous h) {M : ℝ} (hM : ∀ x : Plane, ‖h x‖ ≤ M) :
    (∫ x : Plane, (h x : ℂ) * mollified f ψ x) =
      ∫ y : Plane, (dualKernelAverage ψ h y : ℂ) * f y := by
  have hF := mollified_pairing_integrand_integrable hf hψ hcψ hh hM
  have hswap := integral_integral_swap
    (f := fun x : Plane => fun y : Plane => (h x : ℂ) * (ψ (x - y) • f y)) hF
  have hfiber (y : Plane) :
      (∫ x : Plane, (h x : ℂ) * (ψ (x - y) • f y)) =
        (dualKernelAverage ψ h y : ℂ) * f y := by
    have he : (fun x : Plane => (h x : ℂ) * (ψ (x - y) • f y)) =
        fun x : Plane => (ψ (x - y) * h x) • f y := by
      funext x
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [he, integral_smul_const]
    rfl
  simp_rw [mollified_eq_integral, ← integral_const_mul]
  rw [hswap]
  exact integral_congr_ae (Eventually.of_forall hfiber)

theorem dualKernelAverage_eq_convolution_of_even (ψ h : Plane → ℝ)
    (heven : ∀ z : Plane, ψ (-z) = ψ z) (y : Plane) :
    dualKernelAverage ψ h y =
      (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) y := by
  unfold dualKernelAverage
  rw [convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have he : y - x = -(x - y) := by abel
  rw [he, heven]

theorem dualKernelAverage_weylBump_tendsto {h : Plane → ℝ} (hh : Continuous h)
    (y : Plane) :
    Tendsto (fun n : ℕ => dualKernelAverage ((weylApproximationBump n).normed volume) h y)
      atTop (𝓝 (h y)) := by
  have hc := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Plane)) (φ := weylApproximationBump)
    weylApproximationBump_rOut_tendsto hh y
  have heq (n : ℕ) :
      dualKernelAverage ((weylApproximationBump n).normed volume) h y =
        (((weylApproximationBump n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) y :=
    dualKernelAverage_eq_convolution_of_even _ _
      (fun z => (weylApproximationBump n).normed_neg z) y
  exact (tendsto_congr heq).mpr hc

/-- Nonnegativity and unit mass give a bound independent of the bump index. -/
theorem dualKernelAverage_weylBump_norm_le {h : Plane → ℝ} {M : ℝ}
    (hM : ∀ x : Plane, ‖h x‖ ≤ M) (n : ℕ) (y : Plane) :
    ‖dualKernelAverage ((weylApproximationBump n).normed volume) h y‖ ≤ M := by
  rw [dualKernelAverage_eq_convolution_of_even _ _
    (fun z => (weylApproximationBump n).normed_neg z), convolution_def]
  have hbound : ∀ᵐ z : Plane,
      ‖ContinuousLinearMap.lsmul ℝ ℝ ((weylApproximationBump n).normed volume z)
        (h (y - z))‖ ≤ (weylApproximationBump n).normed volume z * M := by
    filter_upwards [] with z
    simp only [ContinuousLinearMap.lsmul_apply, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ((weylApproximationBump n).nonneg_normed z)]
    exact mul_le_mul_of_nonneg_left (hM (y - z))
      ((weylApproximationBump n).nonneg_normed z)
  have hi := norm_integral_le_of_norm_le
    ((weylApproximationBump n).integrable_normed.mul_const M) hbound
  simpa only [integral_mul_const, (weylApproximationBump n).integral_normed,
    one_mul] using hi

/-- Dominated convergence for every continuous compact test, established from
the actual approximate identity and the fixed L1 bound M‖f‖. -/
theorem mollified_weylBump_pairing_tendsto {f : Plane → ℂ} (hf : Integrable f)
    {h : Plane → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Tendsto (fun n : ℕ => ∫ x : Plane, (h x : ℂ) *
      mollified f ((weylApproximationBump n).normed volume) x) atTop
      (𝓝 (∫ x : Plane, (h x : ℂ) * f x)) := by
  obtain ⟨M, _, hM⟩ := compactKernel_uniform_bound hhc hh
  have hcont (n : ℕ) : Continuous
      (dualKernelAverage ((weylApproximationBump n).normed volume) h) := by
    have hc := hhc.continuous_convolution_right (μ := (volume : Measure Plane))
      (ContinuousLinearMap.lsmul ℝ ℝ)
      ((weylApproximationBump n).continuous_normed
        (μ := (volume : Measure Plane))).locallyIntegrable hh
    have heq : dualKernelAverage ((weylApproximationBump n).normed volume) h =
        (((weylApproximationBump n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) := by
      funext y
      exact dualKernelAverage_eq_convolution_of_even _ _
        (fun z => (weylApproximationBump n).normed_neg z) y
    rw [heq]
    exact hc
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun n : ℕ => fun y : Plane =>
      (dualKernelAverage ((weylApproximationBump n).normed volume) h y : ℂ) * f y)
    (f := fun y : Plane => (h y : ℂ) * f y) (fun y : Plane => M * ‖f y‖)
    (fun n => (Complex.continuous_ofReal.comp (hcont n)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
    (hf.norm.const_mul M)
    (fun n => Eventually.of_forall fun y => by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (dualKernelAverage_weylBump_norm_le hM n y)
        (norm_nonneg _))
    (Eventually.of_forall fun y =>
      ((Complex.continuous_ofReal.tendsto (h y)).comp
        (dualKernelAverage_weylBump_tendsto hh y)).mul_const (f y))
  have heq (n : ℕ) :
      (∫ x : Plane, (h x : ℂ) *
        mollified f ((weylApproximationBump n).normed volume) x) =
      ∫ y : Plane,
        (dualKernelAverage ((weylApproximationBump n).normed volume) h y : ℂ) * f y :=
    mollified_pairing_eq_dualKernelAverage hf (weylApproximationBump n).integrable_normed
      (weylApproximationBump n).continuous_normed hh hM
  exact (tendsto_congr heq).mpr hlim

/-- An eventually weakly harmonic sequence of the specified actual normalized
smoothings forces the original ambient L1 function to be weakly harmonic on U. -/
theorem distributionHarmonicOn_of_eventually_mollified_weylBump
    {f : Plane → ℂ} (hf : Integrable f) {U : Set Plane} (hU : IsOpen U)
    (hweak : ∀ᶠ n : ℕ in atTop,
      DistributionHarmonicOn (mollified f ((weylApproximationBump n).normed volume)) U) :
    DistributionHarmonicOn f U := by
  intro φ hφ hcφ hsφ
  let Uo : TopologicalSpace.Opens Plane := ⟨U, hU⟩
  let φo : TestFunction Uo ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hcφ, hsφ⟩
  let h : Plane → ℝ := testLaplacianCLM Uo φo
  have he : h = laplacian φ := by
    funext x
    exact testLaplacianCLM_apply Uo φo x
  have hlim := mollified_weylBump_pairing_tendsto hf
    (testLaplacianCLM Uo φo).contDiff.continuous
    (testLaplacianCLM Uo φo).hasCompactSupport
  change Tendsto (fun n : ℕ => ∫ x : Plane, (h x : ℂ) *
    mollified f ((weylApproximationBump n).normed volume) x) atTop
    (𝓝 (∫ x : Plane, (h x : ℂ) * f x)) at hlim
  rw [he] at hlim
  have hz : (fun n : ℕ => ∫ x : Plane, (laplacian φ x : ℂ) *
      mollified f ((weylApproximationBump n).normed volume) x) =ᶠ[atTop]
      fun _ => (0 : ℂ) := hweak.mono fun n hn => hn φ hφ hcφ hsφ
  have hzero : Tendsto (fun n : ℕ => ∫ x : Plane, (laplacian φ x : ℂ) *
      mollified f ((weylApproximationBump n).normed volume) x) atTop (𝓝 (0 : ℂ)) :=
    (tendsto_congr' hz).mpr tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzero

theorem distributionHarmonicOn_ballCutoff_iff (f : Plane → ℂ) (Q : ℝ)
    (U : TopologicalSpace.Opens Plane) (hUQ : (U : Set Plane) ⊆ planeBall Q) :
    DistributionHarmonicOn (ballCutoff Q f) (U : Set Plane) ↔
      DistributionHarmonicOn f (U : Set Plane) :=
  distributionHarmonicOn_congr_ae U
    (((ballCutoff_eq_on_ball Q f).mono hUQ).aeEq_restrict U.isOpen.measurableSet)

/-- The original locally integrable representative is recovered only on an
inner ball contained in the cutoff ball, using the local a.e. weak bridge. -/
theorem distributionHarmonicOn_of_eventually_mollified_ballCutoff
    {f : Plane → ℂ} {R Q S : ℝ} (hf : LocallyIntegrableOn f (planeBall R))
    (hQ : 0 < Q) (hQR : Q < R) (hSQ : S ≤ Q)
    (hweak : ∀ᶠ n : ℕ in atTop,
      DistributionHarmonicOn
        (mollified (ballCutoff Q f) ((weylApproximationBump n).normed volume)) (planeBall S)) :
    DistributionHarmonicOn f (planeBall S) := by
  have hw := distributionHarmonicOn_of_eventually_mollified_weylBump
    (ballCutoff_integrable hf hQ hQR) Metric.isOpen_ball hweak
  exact (distributionHarmonicOn_ballCutoff_iff f Q
    ⟨planeBall S, Metric.isOpen_ball⟩ (Metric.ball_subset_ball hSQ)).mp hw

end J0RadialUniqueness
