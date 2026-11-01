import Solutions.J0RadialUniqueness.CompactRadialComplexKernel
import Solutions.J0RadialUniqueness.HelmholtzResolventRadialIdentity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Actual compact planar Helmholtz resolvents. All integrals below are the
Lebesgue integrals of the explicitly defined kernels. -/

noncomputable section
open MeasureTheory Filter Laplacian Set
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

def planarHelmholtzResolventB (r : ℝ) (lam : ℂ) : Plane → ℂ :=
  compactRadialComplexKernel r (helmholtzResolventB r lam)

def planarHelmholtzResolventT (r : ℝ) (lam : ℂ) : Plane → ℂ :=
  compactRadialComplexKernel r (helmholtzResolventT r lam)

theorem measurable_helmholtzLogRatio (r : ℝ) : Measurable (helmholtzLogRatio r) :=
  Complex.measurable_ofReal.comp (Real.measurable_log.comp (measurable_id.div_const r))

theorem measurable_helmholtzResolventB (r : ℝ) (lam : ℂ) : Measurable (helmholtzResolventB r lam) :=
  (((((measurable_helmholtzLogRatio r).neg.mul measurable_const).mul
    (continuous_helmholtzP lam).measurable).add
      (measurable_const.mul (continuous_helmholtzH lam).measurable)).sub
        (measurable_const.mul (continuous_helmholtzP lam).measurable)).div_const _

theorem intervalIntegrable_weighted_helmholtzResolventB {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    IntervalIntegrable (fun s : ℝ => (s : ℂ) * helmholtzResolventB r lam s) volume 0 r := by
  have he : (fun s : ℝ => (s : ℂ) * helmholtzResolventB r lam s) =
      helmholtzResolventWeightedB r lam := (funext (helmholtzResolventWeightedB_eq r lam)).symm
  rw [he]
  exact (continuous_helmholtzResolventWeightedB hr lam).intervalIntegrable 0 r

theorem measurable_planarHelmholtzResolventB (r : ℝ) (lam : ℂ) :
    Measurable (planarHelmholtzResolventB r lam) :=
  measurable_compactRadialComplexKernel r (measurable_helmholtzResolventB r lam)

theorem planarHelmholtzResolventB_hasCompactSupport (r : ℝ) (lam : ℂ) :
    HasCompactSupport (planarHelmholtzResolventB r lam) :=
  compactRadialComplexKernel_hasCompactSupport r _

theorem planarHelmholtzResolventB_integrable {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Integrable (planarHelmholtzResolventB r lam) :=
  compactRadialComplexKernel_integrable hr (measurable_helmholtzResolventB r lam)
    (intervalIntegrable_weighted_helmholtzResolventB hr lam)

theorem planarHelmholtzResolventB_integrable_mul {r : ℝ} (hr : 0 < r) (lam : ℂ)
    {f : Plane → ℂ} (hf : Continuous f) (x : Plane) :
    Integrable (fun y => planarHelmholtzResolventB r lam y * f (x - y)) :=
  compactRadialComplexKernel_integrable_mul hr (measurable_helmholtzResolventB r lam)
    (intervalIntegrable_weighted_helmholtzResolventB hr lam) hf x

theorem circularMean_add_const_mul_of_continuous {f g : Plane → ℂ}
    (hf : Continuous f) (hg : Continuous g) (c : ℂ) (r : ℝ) (x : Plane) :
    circularMean (fun y => f y + c * g y) r x = circularMean f r x + c * circularMean g r x := by
  have hp : Continuous (fun θ : ℝ => x + r • circleDirection θ) :=
    continuous_const.add (continuous_circleDirection.const_smul r)
  have hi : IntervalIntegrable (fun θ : ℝ => f (x + r • circleDirection θ))
      volume 0 (2 * Real.pi) := (hf.comp hp).intervalIntegrable 0 (2 * Real.pi)
  have hj : IntervalIntegrable (fun θ : ℝ => c * g (x + r • circleDirection θ))
      volume 0 (2 * Real.pi) := ((hg.comp hp).const_mul c).intervalIntegrable 0 (2 * Real.pi)
  unfold circularMean
  dsimp only
  rw [intervalIntegral.integral_add hi hj, intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  ring

/-- The planar B identity has no root or nonzero-parameter restriction. -/
theorem planarHelmholtzResolventB_weak {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    (∫ y : Plane, planarHelmholtzResolventB r lam y *
      (laplacian f (x - y) + lam ^ 2 * f (x - y))) =
        circularMean f r x - helmholtzP lam r * f x := by
  have hΔ := (laplacian_contDiff_infty hf).continuous
  have hL : Continuous (fun y => laplacian f y + lam ^ 2 * f y) :=
    hΔ.add (hf.continuous.const_mul _)
  rw [show (fun y : Plane => planarHelmholtzResolventB r lam y *
      (laplacian f (x - y) + lam ^ 2 * f (x - y))) =
      (fun y : Plane => compactRadialComplexKernel r (helmholtzResolventB r lam) y *
        (fun z => laplacian f z + lam ^ 2 * f z) (x - y)) from rfl,
    compactRadialComplexKernel_integral_eq_radial hr (measurable_helmholtzResolventB r lam)
      (intervalIntegrable_weighted_helmholtzResolventB hr lam) hL x]
  simp_rw [circularMean_add_const_mul_of_continuous hΔ hf.continuous]
  exact integral_helmholtzResolventB_circle_laplacian hf x hr lam

def helmholtzResolventWeightedT (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  ((greenRadialWeight r s : ℂ) *
      (((r : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam r) * helmholtzP lam s +
        ((s : ℂ) ^ 2 / 4) * Q (helmholtzResolventArg lam s)) +
    (s : ℂ) * (((s : ℂ) ^ 2 / 4) * helmholtzP lam r *
      harmonicDividedDifference (helmholtzResolventArg lam s) -
        ((r : ℂ) ^ 2 / 4) * harmonicDividedDifference (helmholtzResolventArg lam r) * helmholtzP lam s)) /
      (2 * (Real.pi : ℂ))

theorem helmholtzResolventWeightedT_eq (r : ℝ) (lam : ℂ) (s : ℝ) :
    helmholtzResolventWeightedT r lam s = (s : ℂ) * helmholtzResolventT r lam s := by
  unfold helmholtzResolventWeightedT helmholtzResolventT
  simp only [greenRadialWeight, Complex.ofReal_mul]
  ring

theorem continuous_helmholtzResolventArg_joint :
    Continuous (fun p : ℂ × ℝ => helmholtzResolventArg p.1 p.2) := by
  unfold helmholtzResolventArg
  fun_prop

theorem continuous_helmholtzP_joint : Continuous (fun p : ℂ × ℝ => helmholtzP p.1 p.2) := by
  simp_rw [helmholtzP_eq_F_arg]
  exact F_differentiable.continuous.comp continuous_helmholtzResolventArg_joint

set_option maxHeartbeats 1000000 in
/-- Joint continuity of sT in its complex parameter and real radius closes the
parameter-zero limit without division by lam. -/
theorem continuous_helmholtzResolventWeightedT_joint {r : ℝ} (hr : 0 < r) :
    Continuous (fun p : ℂ × ℝ => helmholtzResolventWeightedT r p.1 p.2) := by
  have har : Continuous (fun p : ℂ × ℝ => helmholtzResolventArg p.1 r) := by
    unfold helmholtzResolventArg
    fun_prop
  have hpr : Continuous (fun p : ℂ × ℝ => helmholtzP p.1 r) := by
    have he : (fun p : ℂ × ℝ => helmholtzP p.1 r) =
        (fun p : ℂ × ℝ => F (helmholtzResolventArg p.1 r)) :=
      funext (fun p => helmholtzP_eq_F_arg p.1 r)
    rw [he]
    exact F_differentiable.continuous.comp har
  have hqr := Q_continuous.comp har
  have hqs := Q_continuous.comp continuous_helmholtzResolventArg_joint
  have hdr := harmonicDividedDifference_differentiable.continuous.comp har
  have hds := harmonicDividedDifference_differentiable.continuous.comp continuous_helmholtzResolventArg_joint
  have hw : Continuous (fun p : ℂ × ℝ => (greenRadialWeight r p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_greenRadialWeight hr).comp continuous_snd)
  have hs : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ)) := Complex.continuous_ofReal.comp continuous_snd
  unfold helmholtzResolventWeightedT
  exact ((hw.mul (((continuous_const.mul hqr).mul continuous_helmholtzP_joint).add
    (((hs.pow 2).div_const _).mul hqs))).add
      (hs.mul (((((hs.pow 2).div_const _).mul hpr).mul hds).sub
        ((continuous_const.mul hdr).mul continuous_helmholtzP_joint)))).div_const _

theorem continuous_helmholtzResolventWeightedT {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Continuous (helmholtzResolventWeightedT r lam) :=
  (continuous_helmholtzResolventWeightedT_joint hr).comp (continuous_const.prodMk continuous_id)

theorem measurable_helmholtzResolventT (r : ℝ) (lam : ℂ) : Measurable (helmholtzResolventT r lam) := by
  have har : Continuous (helmholtzResolventArg lam) := by unfold helmholtzResolventArg; fun_prop
  have hq := (Q_continuous.comp har).measurable
  have hd := (harmonicDividedDifference_differentiable.continuous.comp har).measurable
  have hs : Measurable (fun s : ℝ => (s : ℂ)) := Complex.measurable_ofReal
  have hl : Measurable (fun s : ℝ => (Real.log (r / s) : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp (measurable_const.div measurable_id))
  unfold helmholtzResolventT
  exact (((hl.mul (((measurable_const.mul measurable_const).mul (continuous_helmholtzP lam).measurable).add
    (((hs.pow_const 2).div_const _).mul hq))).add
      ((((hs.pow_const 2).div_const _).mul measurable_const).mul hd)).sub
        ((measurable_const.mul measurable_const).mul (continuous_helmholtzP lam).measurable)).div_const _

theorem intervalIntegrable_weighted_helmholtzResolventT {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    IntervalIntegrable (fun s : ℝ => (s : ℂ) * helmholtzResolventT r lam s) volume 0 r := by
  have he : (fun s : ℝ => (s : ℂ) * helmholtzResolventT r lam s) =
      helmholtzResolventWeightedT r lam := (funext (helmholtzResolventWeightedT_eq r lam)).symm
  rw [he]
  exact (continuous_helmholtzResolventWeightedT hr lam).intervalIntegrable 0 r

theorem measurable_planarHelmholtzResolventT (r : ℝ) (lam : ℂ) :
    Measurable (planarHelmholtzResolventT r lam) :=
  measurable_compactRadialComplexKernel r (measurable_helmholtzResolventT r lam)

theorem planarHelmholtzResolventT_hasCompactSupport (r : ℝ) (lam : ℂ) :
    HasCompactSupport (planarHelmholtzResolventT r lam) := compactRadialComplexKernel_hasCompactSupport r _

theorem planarHelmholtzResolventT_integrable {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    Integrable (planarHelmholtzResolventT r lam) :=
  compactRadialComplexKernel_integrable hr (measurable_helmholtzResolventT r lam)
    (intervalIntegrable_weighted_helmholtzResolventT hr lam)

theorem planarHelmholtzResolventT_integrable_mul {r : ℝ} (hr : 0 < r) (lam : ℂ)
    {f : Plane → ℂ} (hf : Continuous f) (x : Plane) :
    Integrable (fun y => planarHelmholtzResolventT r lam y * f (x - y)) :=
  compactRadialComplexKernel_integrable_mul hr (measurable_helmholtzResolventT r lam)
    (intervalIntegrable_weighted_helmholtzResolventT hr lam) hf x

theorem helmholtzResolventT_mul_parameter_sq_all (r : ℝ) (lam : ℂ) (s : ℝ) :
    lam ^ 2 * helmholtzResolventT r lam s = helmholtzResolventG r s - helmholtzResolventB r lam s := by
  have hpR : helmholtzP lam r = 1 + helmholtzResolventArg lam r * Q (helmholtzResolventArg lam r) := by
    linear_combination helmholtzP_sub_one lam r
  have hpS : helmholtzP lam s = 1 + helmholtzResolventArg lam s * Q (helmholtzResolventArg lam s) := by
    linear_combination helmholtzP_sub_one lam s
  unfold helmholtzResolventT helmholtzResolventG helmholtzResolventB
  rw [helmholtzLogRatio_inverse_all,
    helmholtzH_factor_dividedDifference lam r, helmholtzH_factor_dividedDifference lam s, hpR, hpS]
  unfold helmholtzResolventArg
  ring

theorem planarHelmholtzResolventT_mul_parameter_sq (r : ℝ) (lam : ℂ) (y : Plane) :
    lam ^ 2 * planarHelmholtzResolventT r lam y =
      (planarGreenKernel r y : ℂ) - planarHelmholtzResolventB r lam y := by
  unfold planarHelmholtzResolventT planarHelmholtzResolventB compactRadialComplexKernel planarGreenKernel
  by_cases hy : ‖y‖ < r
  · simp only [if_pos hy]
    rw [helmholtzResolventT_mul_parameter_sq_all]
    simp only [helmholtzResolventG, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  · simp only [if_neg hy, mul_zero, Complex.ofReal_zero, sub_zero]

theorem planarHelmholtzResolventT_weak_of_ne_zero {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) (lam : ℂ) (hlam : lam ≠ 0) :
    (∫ y : Plane, planarHelmholtzResolventT r lam y *
      (laplacian f (x - y) + lam ^ 2 * f (x - y))) =
        (∫ y : Plane, planarGreenKernel r y • f (x - y)) - helmholtzResolventMass r lam * f x := by
  let L : Plane → ℂ := fun z => laplacian f z + lam ^ 2 * f z
  have hΔ := (laplacian_contDiff_infty hf).continuous
  have hL : Continuous L := hΔ.add (hf.continuous.const_mul _)
  have hiG := planarGreen_integrable_mul hL x hr
  have hiB := planarHelmholtzResolventB_integrable_mul hr lam hL x
  have hiGΔ := planarGreen_integrable_mul hΔ x hr
  have hiGf := planarGreen_integrable_mul hf.continuous x hr
  have hmul : lam ^ 2 * (∫ y : Plane, planarHelmholtzResolventT r lam y * L (x - y)) =
      (∫ y : Plane, (planarGreenKernel r y : ℂ) * L (x - y)) -
        ∫ y : Plane, planarHelmholtzResolventB r lam y * L (x - y) := by
    calc
      _ = ∫ y : Plane, lam ^ 2 * (planarHelmholtzResolventT r lam y * L (x - y)) :=
        (integral_const_mul _ _).symm
      _ = ∫ y : Plane, (planarGreenKernel r y : ℂ) * L (x - y) -
          planarHelmholtzResolventB r lam y * L (x - y) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by
          dsimp only
          rw [← sub_mul, ← planarHelmholtzResolventT_mul_parameter_sq]
          ring)
      _ = _ := integral_sub (by simpa only [Complex.real_smul] using hiG) hiB
  have hsplit : (∫ y : Plane, (planarGreenKernel r y : ℂ) * L (x - y)) =
      (∫ y : Plane, planarGreenKernel r y • laplacian f (x - y)) +
        lam ^ 2 * ∫ y : Plane, planarGreenKernel r y • f (x - y) := by
    rw [← integral_const_mul, ← integral_add hiGΔ (hiGf.const_mul (lam ^ 2))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by simp only [L, Complex.real_smul]; ring)
  have hgreen : (∫ y : Plane, planarGreenKernel r y • laplacian f (x - y)) =
      circularMean f r x - f x := localConvolution_planarGreen_laplacian hf x hr
  have hB : (∫ y : Plane, planarHelmholtzResolventB r lam y * L (x - y)) =
      circularMean f r x - helmholtzP lam r * f x := planarHelmholtzResolventB_weak hf x hr lam
  rw [hsplit, hB, hgreen] at hmul
  have hmass := helmholtzResolventMass_mul_parameter_sq r lam
  rw [← helmholtzP_eq_J0] at hmass
  apply mul_left_cancel₀ (pow_ne_zero 2 hlam)
  change lam ^ 2 * (∫ y : Plane, planarHelmholtzResolventT r lam y * L (x - y)) = _
  linear_combination hmul + (f x) * hmass

theorem continuous_planarHelmholtzResolventT_action {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    Continuous (fun lam : ℂ => ∫ y : Plane, planarHelmholtzResolventT r lam y *
      (laplacian f (x - y) + lam ^ 2 * f (x - y))) := by
  have hΔ := (laplacian_contDiff_infty hf).continuous
  have hmΔ : Continuous (fun p : ℂ × ℝ => circleProfile (laplacian f) x p.2) :=
    (circleProfile_differentiable (laplacian_contDiff_infty hf) x).continuous.comp continuous_snd
  have hmf : Continuous (fun p : ℂ × ℝ => circleProfile f x p.2) :=
    (circleProfile_differentiable hf x).continuous.comp continuous_snd
  have hjoint : Continuous (fun p : ℂ × ℝ =>
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r p.1 p.2 *
        (circleProfile (laplacian f) x p.2 + p.1 ^ 2 * circleProfile f x p.2)) :=
    (continuous_const.mul (continuous_helmholtzResolventWeightedT_joint hr)).mul
      (hmΔ.add ((continuous_fst.pow 2).mul hmf))
  have hi : Continuous (fun lam : ℂ => ∫ s : ℝ in (0 : ℝ)..r,
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r lam s *
        (circleProfile (laplacian f) x s + lam ^ 2 * circleProfile f x s)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (lam : ℂ) (s : ℝ) =>
        (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r lam s *
          (circleProfile (laplacian f) x s + lam ^ 2 * circleProfile f x s)) ?_ 0 r
    convert! hjoint using 1 <;> rfl
  have he : (fun lam : ℂ => ∫ y : Plane, planarHelmholtzResolventT r lam y *
      (laplacian f (x - y) + lam ^ 2 * f (x - y))) =
      (fun lam : ℂ => ∫ s : ℝ in (0 : ℝ)..r,
        (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r lam s *
          (circleProfile (laplacian f) x s + lam ^ 2 * circleProfile f x s)) := by
    funext lam
    have hL : Continuous (fun z => laplacian f z + lam ^ 2 * f z) :=
      hΔ.add (hf.continuous.const_mul _)
    change (∫ y : Plane, compactRadialComplexKernel r (helmholtzResolventT r lam) y *
      (fun z => laplacian f z + lam ^ 2 * f z) (x - y)) = _
    rw [compactRadialComplexKernel_integral_eq_radial hr (measurable_helmholtzResolventT r lam)
      (intervalIntegrable_weighted_helmholtzResolventT hr lam) hL x]
    simp_rw [circularMean_add_const_mul_of_continuous hΔ hf.continuous]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [helmholtzResolventWeightedT_eq]
    simp only [circleProfile]
    ring
  rw [he]
  exact hi

/-- The full T identity, including parameter zero. The zero case follows from
joint continuity of the genuine radial integral and density of nonzero complex
parameters; it is not an assumed limiting identity. -/
theorem planarHelmholtzResolventT_weak {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : Plane) {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    (∫ y : Plane, planarHelmholtzResolventT r lam y *
      (laplacian f (x - y) + lam ^ 2 * f (x - y))) =
        (∫ y : Plane, planarGreenKernel r y • f (x - y)) - helmholtzResolventMass r lam * f x := by
  have hmass : Continuous (helmholtzResolventMass r) :=
    continuous_iff_continuousAt.mpr (fun z => (helmholtzResolventMass_parameter_analyticAt r z).continuousAt)
  have hright : Continuous (fun z : ℂ =>
      (∫ y : Plane, planarGreenKernel r y • f (x - y)) - helmholtzResolventMass r z * f x) :=
    continuous_const.sub (hmass.mul continuous_const)
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (continuous_planarHelmholtzResolventT_action hf x hr) hright (fun z hz =>
      planarHelmholtzResolventT_weak_of_ne_zero hf x hr z (by
        simpa only [mem_compl_iff, mem_singleton_iff] using hz))
  exact congrFun heq lam

end J0RadialUniqueness
