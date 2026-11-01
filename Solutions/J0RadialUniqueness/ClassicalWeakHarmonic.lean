import Solutions.J0RadialUniqueness.DistributionLaplacian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! The local C² classical/distributional harmonicity bridge.

No zero extension is used. The integration-by-parts theorem only asks for the
second factor's differentiability on the support of the first factor. Here the
first factor is a compact test or its derivative, and those supports lie inside
the actual open regularity domain. Compact-support integrability is established
on that domain before either integration by parts is invoked.
-/

noncomputable section

open MeasureTheory Set Laplacian
open scoped ContDiff Topology

namespace J0RadialUniqueness

/-- A test pairing is integrable even if the second factor is regular only on
the open domain containing the test's support. -/
theorem integrable_compact_test_smul_of_continuousOn
    {U : Set Plane} {g : Plane → ℂ} {ψ : Plane → ℝ}
    (hg : ContinuousOn g U) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) : Integrable (fun x : Plane => ψ x • g x) := by
  have hcont : ContinuousOn (fun x : Plane => ψ x • g x) (tsupport ψ) :=
    hψ.continuousOn.smul (hg.mono hs)
  have hi : IntegrableOn (fun x : Plane => ψ x • g x) (tsupport ψ) volume :=
    hcont.integrableOn_compact (μ := volume) hc
  have hsupport : Function.support (fun x : Plane => ψ x • g x) ⊆ tsupport ψ := by
    intro x hx
    by_contra hn
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hn])
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hi

theorem directionalKernel_contDiffOn_one {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U) (v : Plane) :
    ContDiffOn ℝ 1 (directionalKernel f v) U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  exact hd.clm_apply contDiffOn_const

theorem directionalSecond_continuousOn {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U) (v w : Plane) :
    ContinuousOn (directionalSecond f v w) U := by
  have hd := directionalKernel_contDiffOn_one hU hf v
  have hc := hd.continuousOn_fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) ≤ 1)
  exact hc.clm_apply continuousOn_const

theorem directionalSecond_eq_fderiv_on {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U) (v w : Plane) {x : Plane} (hx : x ∈ U) :
    directionalSecond f v w x = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hd.differentiableOn_one.differentiableAt (hU.mem_nhds hx)
  have h := fderiv_clm_apply hdiff (differentiableAt_const (c := v) (x := x))
  change fderiv ℝ (fun y => fderiv ℝ f y v) x w = _
  rw [h]
  simp

/-- Two actual integrations by parts with a test supported inside U. -/
theorem integral_directionalSecond_test_smul
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) (v : Plane) :
    (∫ x : Plane, directionalSecond ψ v v x • f x) =
      ∫ x : Plane, ψ x • directionalSecond f v v x := by
  have hψd := directionalKernel_contDiff hψ v
  have hψdd := directionalSecond_contDiff hψ v v
  have hcd := directionalKernel_hasCompactSupport hc v
  have hcdd := directionalSecond_hasCompactSupport hc v v
  have hsd : tsupport (directionalKernel ψ v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hs
  have hsdd : tsupport (directionalSecond ψ v v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsd
  have hfd := directionalKernel_contDiffOn_one hU hf v
  have hfdd := directionalSecond_continuousOn hU hf v v
  have hi_ddψ_f := integrable_compact_test_smul_of_continuousOn hf.continuousOn
    hψdd.continuous hcdd hsdd
  have hi_dψ_df := integrable_compact_test_smul_of_continuousOn hfd.continuousOn
    hψd.continuous hcd hsd
  have hi_dψ_f := integrable_compact_test_smul_of_continuousOn hf.continuousOn
    hψd.continuous hcd hsd
  have hi_ψ_ddf := integrable_compact_test_smul_of_continuousOn hfdd hψ.continuous hc hs
  have hi_ψ_df := integrable_compact_test_smul_of_continuousOn hfd.continuousOn hψ.continuous hc hs
  have h1 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := directionalKernel ψ v) (g := f) (v := v)
    hi_ddψ_f hi_dψ_df hi_dψ_f
    (fun x _ => ((hψd.differentiable (by simp)).differentiableAt (x := x)))
    (fun x hx => (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hsd hx)))
  have h2 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := ψ) (g := directionalKernel f v) (v := v)
    hi_dψ_df hi_ψ_ddf hi_ψ_df
    (fun x _ => ((hψ.differentiable (by simp)).differentiableAt (x := x)))
    (fun x hx => hfd.differentiableOn_one.differentiableAt (hU.mem_nhds (hs hx)))
  have hfirst : (∫ x : Plane, directionalSecond ψ v v x • f x) =
      -(∫ x : Plane, directionalKernel ψ v x • directionalKernel f v x) := by
    have h := congrArg (fun z : ℂ => -z) h1
    have heq : (∫ x : Plane, directionalSecond ψ v v x • f x) =
        ∫ x : Plane, fderiv ℝ (directionalKernel ψ v) x v • f x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by rfl)
    have hraw : (∫ x : Plane, fderiv ℝ (directionalKernel ψ v) x v • f x) =
        -(∫ x : Plane, directionalKernel ψ v x • fderiv ℝ f x v) := by
      simpa only [neg_neg] using h.symm
    have hcross : (∫ x : Plane, directionalKernel ψ v x • fderiv ℝ f x v) =
        ∫ x : Plane, directionalKernel ψ v x • directionalKernel f v x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by rfl)
    exact heq.trans (hraw.trans (congrArg (fun z : ℂ => -z) hcross))
  have hsecond : (∫ x : Plane, ψ x • directionalSecond f v v x) =
      -(∫ x : Plane, directionalKernel ψ v x • directionalKernel f v x) := by
    have heq : (∫ x : Plane, ψ x • directionalSecond f v v x) =
        ∫ x : Plane, ψ x • fderiv ℝ (directionalKernel f v) x v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by rfl)
    have hcross : (∫ x : Plane, fderiv ℝ ψ x v • directionalKernel f v x) =
        ∫ x : Plane, directionalKernel ψ v x • directionalKernel f v x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by rfl)
    exact heq.trans (h2.trans (congrArg (fun z : ℂ => -z) hcross))
  exact hfirst.trans hsecond.symm

theorem laplacian_eq_directionalSecond_on {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U) {x : Plane} (hx : x ∈ U) :
    laplacian f x = directionalSecond f distributionAxis0 distributionAxis0 x +
      directionalSecond f distributionAxis1 distributionAxis1 x := by
  rw [directionalSecond_eq_fderiv_on hU hf _ _ hx,
    directionalSecond_eq_fderiv_on hU hf _ _ hx]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, distributionAxis0, distributionAxis1]

theorem laplacian_continuousOn_of_contDiffOn_two {U : Set Plane} (hU : IsOpen U)
    {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U) : ContinuousOn (laplacian f) U := by
  have heq : EqOn (laplacian f)
      (fun x : Plane => directionalSecond f distributionAxis0 distributionAxis0 x +
        directionalSecond f distributionAxis1 distributionAxis1 x) U :=
    fun _ hx => laplacian_eq_directionalSecond_on hU hf hx
  exact ((directionalSecond_continuousOn hU hf distributionAxis0 distributionAxis0).add
    (directionalSecond_continuousOn hU hf distributionAxis1 distributionAxis1)).congr
      (fun x hx => by simpa only [Pi.add_apply] using heq hx)

/-- Local Green pairing for C² f and a compact C∞ test, with both sides genuinely integrable. -/
theorem integral_laplacian_test_smul
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) :
    (∫ x : Plane, laplacian ψ x • f x) = ∫ x : Plane, ψ x • laplacian f x := by
  let v0 := distributionAxis0
  let v1 := distributionAxis1
  have hψeq (x : Plane) : laplacian ψ x =
      directionalSecond ψ v0 v0 x + directionalSecond ψ v1 v1 x := by
    rw [directionalSecond_eq_fderiv hψ, directionalSecond_eq_fderiv hψ,
      real_laplacian_eq_distributionAxes]
  have hfeq (x : Plane) : ψ x • laplacian f x =
      ψ x • (directionalSecond f v0 v0 x + directionalSecond f v1 v1 x) := by
    by_cases hx : x ∈ U
    · rw [laplacian_eq_directionalSecond_on hU hf hx]
    · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      simp only [hz, zero_smul]
  have hl (v : Plane) : Integrable (fun x : Plane => directionalSecond ψ v v x • f x) :=
    integrable_compact_test_smul_of_continuousOn hf.continuousOn
      (directionalSecond_contDiff hψ v v).continuous
      (directionalSecond_hasCompactSupport hc v v)
      ((tsupport_fderiv_apply_subset ℝ v).trans ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  have hr (v : Plane) : Integrable (fun x : Plane => ψ x • directionalSecond f v v x) :=
    integrable_compact_test_smul_of_continuousOn (directionalSecond_continuousOn hU hf v v)
      hψ.continuous hc hs
  calc
    _ = (∫ x : Plane, directionalSecond ψ v0 v0 x • f x) +
        (∫ x : Plane, directionalSecond ψ v1 v1 x • f x) := by
      rw [← integral_add (hl v0) (hl v1)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change laplacian ψ x • f x = directionalSecond ψ v0 v0 x • f x +
          directionalSecond ψ v1 v1 x • f x
        rw [hψeq, add_smul])
    _ = (∫ x : Plane, ψ x • directionalSecond f v0 v0 x) +
        (∫ x : Plane, ψ x • directionalSecond f v1 v1 x) := by
      rw [integral_directionalSecond_test_smul hU hf hψ hc hs v0,
        integral_directionalSecond_test_smul hU hf hψ hc hs v1]
    _ = _ := by
      rw [← integral_add (hr v0) (hr v1)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change ψ x • directionalSecond f v0 v0 x + ψ x • directionalSecond f v1 v1 x =
          ψ x • laplacian f x
        rw [hfeq, smul_add])

/-- On an actual open regularity domain, distributional harmonicity of a C²
function is equivalent to vanishing of its classical Laplacian at every point. -/
theorem distributionHarmonicOn_iff_laplacian_eq_zero
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U) :
    DistributionHarmonicOn f U ↔ ∀ x ∈ U, laplacian f x = 0 := by
  have hcont := laplacian_continuousOn_of_contDiffOn_two hU hf
  constructor
  · intro hw
    have hae : ∀ᵐ x : Plane, x ∈ U → laplacian f x = 0 := by
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hcont.locallyIntegrableOn hU.measurableSet)
      intro ψ hψ hc hs
      rw [← integral_laplacian_test_smul hU hf hψ hc hs]
      simpa only [Complex.real_smul] using hw ψ hψ hc hs
    have hr : laplacian f =ᵐ[volume.restrict U] (fun _ : Plane => (0 : ℂ)) :=
      (ae_restrict_iff' hU.measurableSet).mpr hae
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hr hU hcont continuousOn_const
  · intro hzero ψ hψ hc hs
    have h : (∫ x : Plane, laplacian ψ x • f x) = 0 := by
      rw [integral_laplacian_test_smul hU hf hψ hc hs]
      have heq : (fun x : Plane => ψ x • laplacian f x) = 0 := by
        funext x
        by_cases hx : x ∈ U
        · simp only [hzero x hx, smul_zero, Pi.zero_apply]
        · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
          simp only [hz, zero_smul, Pi.zero_apply]
      rw [heq]
      change (∫ _x : Plane, (0 : ℂ)) = 0
      exact integral_zero _ _
    simpa only [Complex.real_smul] using h

theorem not_distributionHarmonicOn_of_laplacian_ne_zero
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U)
    {x : Plane} (hx : x ∈ U) (hn : laplacian f x ≠ 0) : ¬ DistributionHarmonicOn f U := by
  intro hw
  exact hn ((distributionHarmonicOn_iff_laplacian_eq_zero hU hf).mp hw x hx)

theorem harmonicOnNhd_of_distributionHarmonicOn
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U)
    (hw : DistributionHarmonicOn f U) : InnerProductSpace.HarmonicOnNhd f U := by
  have hzero := (distributionHarmonicOn_iff_laplacian_eq_zero hU hf).mp hw
  intro x hx
  constructor
  · exact (hf x hx).contDiffAt (hU.mem_nhds hx)
  · filter_upwards [hU.mem_nhds hx] with y hy using hzero y hy

/-- In particular, a genuinely classical nonharmonic C² counterexample remains
nonharmonic for the paper's distributional notion, on the same open domain. -/
theorem not_distributionHarmonicOn_of_not_harmonicOnNhd
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℂ} (hf : ContDiffOn ℝ 2 f U)
    (hn : ¬ InnerProductSpace.HarmonicOnNhd f U) : ¬ DistributionHarmonicOn f U :=
  fun hw => hn (harmonicOnNhd_of_distributionHarmonicOn hU hf hw)

end J0RadialUniqueness
