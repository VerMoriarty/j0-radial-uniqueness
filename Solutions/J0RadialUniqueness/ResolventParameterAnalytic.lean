import Solutions.J0RadialUniqueness.ResolventEntireGrowth
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! The actual compact resolvent convolution is entire in its parameter.

The proof differentiates its explicit weighted radial kernel. All parameter
derivatives are jointly continuous, so a compact complex parameter disk times
the finite radial interval supplies an integrable derivative majorant. The
planar integral is identified only through the already proved integrable polar
formula. Continuity is not substituted for complex differentiability.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Interval

namespace J0RadialUniqueness

def resolventParameterSlope (g : ℂ → ℂ) (lam : ℂ) (s : ℝ) : ℂ :=
  deriv g (helmholtzResolventArg lam s) * (-lam * (s : ℂ) ^ 2 / 2)

theorem helmholtzResolventArg_parameter_hasDerivAt (lam : ℂ) (s : ℝ) :
    HasDerivAt (fun z : ℂ => helmholtzResolventArg z s)
      (-lam * (s : ℂ) ^ 2 / 2) lam := by
  have h := ((((hasDerivAt_id lam).pow 2).neg).mul_const ((s : ℂ) ^ 2)).div_const 4
  convert! h using 1 <;> simp only [helmholtzResolventArg, id_eq] <;> ring

theorem series_resolventArg_parameter_hasDerivAt (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (lam : ℂ) (s : ℝ) :
    HasDerivAt (fun z : ℂ => g (helmholtzResolventArg z s))
      (resolventParameterSlope g lam s) lam := by
  exact (hg (helmholtzResolventArg lam s)).hasDerivAt.comp lam
    (helmholtzResolventArg_parameter_hasDerivAt lam s)

theorem helmholtzP_parameter_hasDerivAt (lam : ℂ) (s : ℝ) :
    HasDerivAt (fun z : ℂ => helmholtzP z s)
      (resolventParameterSlope F lam s) lam := by
  have he : (fun z : ℂ => helmholtzP z s) =
      fun z : ℂ => F (helmholtzResolventArg z s) :=
    funext (fun z => helmholtzP_eq_F_arg z s)
  rw [he]
  exact series_resolventArg_parameter_hasDerivAt F F_differentiable lam s

theorem continuous_deriv_entire_function {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Continuous (deriv g) := by
  have ha : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  exact continuous_iff_continuousAt.mpr (fun z => (ha.deriv z (Set.mem_univ z)).continuousAt)

theorem continuous_resolventParameterSlope_joint (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) :
    Continuous (fun p : ℂ × ℝ => resolventParameterSlope g p.1 p.2) := by
  have hc : Continuous (fun p : ℂ × ℝ => -p.1 * (p.2 : ℂ) ^ 2 / 2) := by fun_prop
  exact ((continuous_deriv_entire_function hg).comp continuous_helmholtzResolventArg_joint).mul hc

def helmholtzResolventWeightedTParameterSlope (r : ℝ) (lam : ℂ) (s : ℝ) : ℂ :=
  ((greenRadialWeight r s : ℂ) *
      (((r : ℂ) ^ 2 / 4) *
        (resolventParameterSlope Q lam r * helmholtzP lam s +
          Q (helmholtzResolventArg lam r) * resolventParameterSlope F lam s) +
        ((s : ℂ) ^ 2 / 4) * resolventParameterSlope Q lam s) +
    (s : ℂ) *
      (((s : ℂ) ^ 2 / 4) *
        (resolventParameterSlope F lam r * harmonicDividedDifference (helmholtzResolventArg lam s) +
          helmholtzP lam r * resolventParameterSlope harmonicDividedDifference lam s) -
        ((r : ℂ) ^ 2 / 4) *
          (resolventParameterSlope harmonicDividedDifference lam r * helmholtzP lam s +
            harmonicDividedDifference (helmholtzResolventArg lam r) * resolventParameterSlope F lam s))) /
      (2 * (Real.pi : ℂ))

theorem helmholtzResolventWeightedT_parameter_hasDerivAt (r s : ℝ) (lam : ℂ) :
    HasDerivAt (fun z : ℂ => helmholtzResolventWeightedT r z s)
      (helmholtzResolventWeightedTParameterSlope r lam s) lam := by
  have hQr := series_resolventArg_parameter_hasDerivAt Q Q_differentiable lam r
  have hQs := series_resolventArg_parameter_hasDerivAt Q Q_differentiable lam s
  have hDr := series_resolventArg_parameter_hasDerivAt harmonicDividedDifference
    harmonicDividedDifference_differentiable lam r
  have hDs := series_resolventArg_parameter_hasDerivAt harmonicDividedDifference
    harmonicDividedDifference_differentiable lam s
  have hPr := helmholtzP_parameter_hasDerivAt lam r
  have hPs := helmholtzP_parameter_hasDerivAt lam s
  have h :=
    (((((hQr.mul hPs).const_mul ((r : ℂ) ^ 2 / 4)).add
        (hQs.const_mul ((s : ℂ) ^ 2 / 4))).const_mul (greenRadialWeight r s : ℂ)).add
      ((((hPr.mul hDs).const_mul ((s : ℂ) ^ 2 / 4)).sub
        ((hDr.mul hPs).const_mul ((r : ℂ) ^ 2 / 4))).const_mul (s : ℂ))).div_const
          (2 * (Real.pi : ℂ))
  convert! h using 1 <;>
    simp only [helmholtzResolventWeightedT, helmholtzResolventWeightedTParameterSlope,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply] <;>
    first | (funext z; ring) | ring

theorem continuous_helmholtzResolventWeightedTParameterSlope_joint {r : ℝ} (hr : 0 < r) :
    Continuous (fun p : ℂ × ℝ => helmholtzResolventWeightedTParameterSlope r p.1 p.2) := by
  have hfix : Continuous (fun p : ℂ × ℝ => (p.1, r)) := continuous_fst.prodMk continuous_const
  have har : Continuous (fun p : ℂ × ℝ => helmholtzResolventArg p.1 r) :=
    continuous_helmholtzResolventArg_joint.comp hfix
  have hqr := Q_continuous.comp har
  have hdr := harmonicDividedDifference_differentiable.continuous.comp har
  have hds := harmonicDividedDifference_differentiable.continuous.comp continuous_helmholtzResolventArg_joint
  have hpr := continuous_helmholtzP_joint.comp hfix
  have hps := continuous_helmholtzP_joint
  have hQr := (continuous_resolventParameterSlope_joint Q Q_differentiable).comp hfix
  have hQs := continuous_resolventParameterSlope_joint Q Q_differentiable
  have hDr := (continuous_resolventParameterSlope_joint harmonicDividedDifference
    harmonicDividedDifference_differentiable).comp hfix
  have hDs := continuous_resolventParameterSlope_joint harmonicDividedDifference
    harmonicDividedDifference_differentiable
  have hPr := (continuous_resolventParameterSlope_joint F F_differentiable).comp hfix
  have hPs := continuous_resolventParameterSlope_joint F F_differentiable
  have hw : Continuous (fun p : ℂ × ℝ => (greenRadialWeight r p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_greenRadialWeight hr).comp continuous_snd)
  have hs : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ)) := Complex.continuous_ofReal.comp continuous_snd
  unfold helmholtzResolventWeightedTParameterSlope
  exact ((hw.mul ((continuous_const.mul ((hQr.mul hps).add (hqr.mul hPs))).add
    (((hs.pow 2).div_const _).mul hQs))).add
      (hs.mul (((((hs.pow 2).div_const _).mul ((hPr.mul hds).add (hpr.mul hDs))).sub
        (continuous_const.mul ((hDr.mul hps).add (hdr.mul hPs))))))).div_const _

/-- A finite-interval complex-parameter differentiation theorem. Its derivative
majorant is derived from compactness of a complex disk times the interval. -/
theorem hasDerivAt_complex_intervalIntegral_of_joint_continuous
    {G H : ℂ → ℝ → ℂ}
    (hG : Continuous (Function.uncurry G)) (hH : Continuous (Function.uncurry H))
    (hd : ∀ z : ℂ, ∀ s : ℝ, HasDerivAt (fun w : ℂ => G w s) (H z s) z)
    (a b : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ s : ℝ in a..b, G w s) (∫ s : ℝ in a..b, H z s) z := by
  have hcompact : IsCompact (Metric.closedBall z (1 : ℝ) ×ˢ uIcc a b) :=
    (isCompact_closedBall z 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hH.continuousOn
  have hGc : ∀ w : ℂ, Continuous (G w) := fun w =>
    hG.comp (continuous_const.prodMk continuous_id)
  have hHc : Continuous (H z) := hH.comp (continuous_const.prodMk continuous_id)
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := H) (μ := volume) (bound := fun _ : ℝ => C)
    (s := Metric.closedBall z 1)
    (Metric.closedBall_mem_nhds z (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun w => (hGc w).aestronglyMeasurable))
    ((hGc z).intervalIntegrable a b) hHc.aestronglyMeasurable
    (Eventually.of_forall (fun s hs w hw => hC (w, s) ⟨hw, uIoc_subset_uIcc hs⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun s _ w _ => hd w s))
  exact hi.2

theorem continuous_circularMean_radius_of_continuous {u : Plane → ℂ}
    (hu : Continuous u) (x : Plane) : Continuous (fun s : ℝ => circularMean u s x) := by
  have hG : Continuous (fun p : ℝ × ℝ => u (x + p.1 • circleDirection p.2)) :=
    hu.comp (continuous_circleParameterMap x)
  have hi : Continuous (fun s : ℝ => ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      u (x + s • circleDirection θ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (s θ : ℝ) => u (x + s • circleDirection θ)) ?_ 0 (2 * Real.pi)
    convert! hG using 1 <;> rfl
  unfold circularMean
  exact hi.const_smul ((2 * Real.pi)⁻¹ : ℝ)

def planarResolventTConvolution (r : ℝ) (u : Plane → ℂ) (x : Plane) (lam : ℂ) : ℂ :=
  ∫ y : Plane, planarHelmholtzResolventT r lam y * u (x - y)

theorem planarResolventTConvolution_eq_radial {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane) (lam : ℂ) :
    planarResolventTConvolution r u x lam = ∫ s : ℝ in (0 : ℝ)..r,
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r lam s * circularMean u s x := by
  unfold planarResolventTConvolution planarHelmholtzResolventT
  rw [compactRadialComplexKernel_integral_eq_radial hr (measurable_helmholtzResolventT r lam)
    (intervalIntegrable_weighted_helmholtzResolventT hr lam) hu x]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [helmholtzResolventWeightedT_eq]
  ring

theorem planarResolventTConvolution_hasDerivAt {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane) (lam : ℂ) :
    HasDerivAt (planarResolventTConvolution r u x)
      (∫ s : ℝ in (0 : ℝ)..r,
        (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedTParameterSlope r lam s * circularMean u s x) lam := by
  have hmean : Continuous (fun p : ℂ × ℝ => circularMean u p.2 x) :=
    (continuous_circularMean_radius_of_continuous hu x).comp continuous_snd
  have hG : Continuous (fun p : ℂ × ℝ =>
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r p.1 p.2 * circularMean u p.2 x) :=
    (continuous_const.mul (continuous_helmholtzResolventWeightedT_joint hr)).mul hmean
  have hH : Continuous (fun p : ℂ × ℝ =>
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedTParameterSlope r p.1 p.2 * circularMean u p.2 x) :=
    (continuous_const.mul (continuous_helmholtzResolventWeightedTParameterSlope_joint hr)).mul hmean
  have hi := hasDerivAt_complex_intervalIntegral_of_joint_continuous
    (G := fun z s => (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r z s * circularMean u s x)
    (H := fun z s => (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedTParameterSlope r z s * circularMean u s x)
    hG hH
    (fun z s => ((helmholtzResolventWeightedT_parameter_hasDerivAt r s z).const_mul
      (2 * (Real.pi : ℂ))).mul_const (circularMean u s x))
    0 r lam
  have he : planarResolventTConvolution r u x = fun z : ℂ => ∫ s : ℝ in (0 : ℝ)..r,
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r z s * circularMean u s x :=
    funext (planarResolventTConvolution_eq_radial hr hu x)
  rw [he]
  exact hi

theorem planarResolventTConvolution_differentiable {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane) :
    Differentiable ℂ (planarResolventTConvolution r u x) :=
  fun lam => (planarResolventTConvolution_hasDerivAt hr hu x lam).differentiableAt

/-- Entire dependence of the genuine planar convolution, including parameter zero. -/
theorem planarResolventTConvolution_analyticAt {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane) (lam : ℂ) :
    AnalyticAt ℂ (planarResolventTConvolution r u x) lam :=
  ((planarResolventTConvolution_differentiable hr hu x).differentiableOn.analyticOnNhd isOpen_univ)
    lam (Set.mem_univ lam)

theorem planarResolventTConvolution_uniform_exp_bound {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ,
      ‖planarResolventTConvolution r u x lam‖ ≤ C * Real.exp (2 * r * ‖lam‖) := by
  obtain ⟨A, hA, hkernel⟩ := helmholtzResolventWeightedT_uniform_exp_bound hr
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) r)).exists_bound_of_continuousOn
    (continuous_circularMean_radius_of_continuous hu x).continuousOn
  let M : ℝ := 1 + |K|
  have hM : 0 < M := by dsimp [M]; positivity
  have hmean (s : ℝ) (hs : s ∈ Icc (0 : ℝ) r) : ‖circularMean u s x‖ ≤ M :=
    (hK s hs).trans (by dsimp [M]; linarith [le_abs_self K])
  refine ⟨r * (2 * Real.pi) * A * M, by positivity, ?_⟩
  intro lam
  rw [planarResolventTConvolution_eq_radial hr hu x lam]
  have hb : ∀ s ∈ Ι (0 : ℝ) r,
      ‖(2 * (Real.pi : ℂ)) * helmholtzResolventWeightedT r lam s * circularMean u s x‖ ≤
        (2 * Real.pi) * (A * Real.exp (2 * r * ‖lam‖)) * M := by
    intro s hs
    have hsC : s ∈ Icc (0 : ℝ) r := by
      simpa only [uIcc_of_le hr.le] using uIoc_subset_uIcc hs
    have hpiNorm : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      simp [norm_mul, abs_of_pos Real.pi_pos]
    rw [norm_mul, norm_mul, hpiNorm]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hkernel lam s hsC) Real.two_pi_pos.le)
      (hmean s hsC) (norm_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_pos hr] at hi
  calc
    _ ≤ ((2 * Real.pi) * (A * Real.exp (2 * r * ‖lam‖)) * M) * r := hi
    _ = (r * (2 * Real.pi) * A * M) * Real.exp (2 * r * ‖lam‖) := by ring

end J0RadialUniqueness
