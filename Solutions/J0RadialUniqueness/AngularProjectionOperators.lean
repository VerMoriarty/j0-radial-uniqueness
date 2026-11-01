import Solutions.J0RadialUniqueness.AngularPolynomialProjection
import Solutions.J0RadialUniqueness.ClassicalWeakHarmonic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Isometry

/-! The actual plane angular Fourier operators. Finite smoothness is proved
by differentiation of the compact angular integral, with its derivative bound
obtained on a genuine compact product. Circular averaging commutes with the
operator by rotation covariance and the proved compact-square Fubini theorem. -/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Filter Set Laplacian
open scoped Topology Interval ContDiff ComplexConjugate

namespace J0RadialUniqueness

section CompactParameter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A compact-interval parameter derivative. Its domination is supplied by
continuity on a compact product, not by an extra analytic premise. -/
theorem hasFDerivAt_plane_intervalIntegral_of_joint_continuous
    {G : Plane → ℝ → V} {H : Plane → ℝ → Plane →L[ℝ] V}
    (hG : Continuous (Function.uncurry G)) (hH : Continuous (Function.uncurry H))
    (hd : ∀ x : Plane, ∀ t : ℝ, HasFDerivAt (fun y : Plane => G y t) (H x t) x)
    (a b : ℝ) (x : Plane) :
    HasFDerivAt (fun y : Plane => ∫ t : ℝ in a..b, G y t)
      (∫ t : ℝ in a..b, H x t) x := by
  have hc : IsCompact (Metric.closedBall x (1 : ℝ) ×ˢ uIcc a b) :=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hH.continuousOn
  have hGc (y : Plane) : Continuous (G y) := hG.comp (continuous_const.prodMk continuous_id)
  have hHc : Continuous (H x) := hH.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := H) (μ := volume) (bound := fun _ : ℝ => C)
    (s := Metric.closedBall x 1)
    (Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun y => (hGc y).aestronglyMeasurable))
    ((hGc x).intervalIntegrable a b) hHc.aestronglyMeasurable
    (Eventually.of_forall (fun t ht y hy => hC (y, t) ⟨hy, uIoc_subset_uIcc ht⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun t _ y _ => hd y t))

end CompactParameter

/-- Every finite order is preserved by integration over a fixed compact
interval. The codomain is quantified so the induction applies to CLM-valued
derivatives as well as the original complex integrand. -/
theorem contDiff_nat_plane_intervalIntegral (n : ℕ) :
    ∀ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (G : Plane × ℝ → V), ContDiff ℝ n G → ∀ a b : ℝ,
        ContDiff ℝ n (fun x : Plane => ∫ t : ℝ in a..b, G (x, t)) := by
  induction n with
  | zero =>
      intro V _ _ _ G hG a b
      apply contDiff_zero.mpr
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x : Plane => fun t : ℝ => G (x, t))
      convert! hG.continuous using 1 <;> rfl
  | succ n ih =>
      intro V _ _ _ G hG a b
      let H : Plane × ℝ → Plane →L[ℝ] V := fun p =>
        (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ Plane ℝ)
      have hH : ContDiff ℝ n H :=
        (hG.fderiv_right (by exact_mod_cast (le_refl (n + 1)))).clm_comp contDiff_const
      have hd (x : Plane) (t : ℝ) : HasFDerivAt (fun y : Plane => G (y, t)) (H (x, t)) x := by
        have hh := ((hG.differentiable (by simp)).differentiableAt (x := (x, t))).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
        simpa only [Function.comp_def, H] using hh
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x : Plane => ∫ t : ℝ in a..b, H (x, t), ih _ H hH a b, ?_⟩
      intro x
      exact hasFDerivAt_plane_intervalIntegral_of_joint_continuous
        (G := fun y t => G (y, t)) (H := fun y t => H (y, t))
        (by convert! hG.continuous using 1 <;> rfl)
        (by convert! hH.continuous using 1 <;> rfl) hd a b x

theorem contDiff_plane_intervalIntegral {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {n : ℕ∞} {G : Plane × ℝ → V}
    (hG : ContDiff ℝ n G) (a b : ℝ) :
    ContDiff ℝ n (fun x : Plane => ∫ t : ℝ in a..b, G (x, t)) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro k hk
  exact contDiff_nat_plane_intervalIntegral k V G ((contDiff_iff_forall_nat_le.mp hG) k hk) a b

def planeParameterDirectional (G : Plane × ℝ → ℂ) (v : Plane) (p : Plane × ℝ) : ℂ :=
  fderiv ℝ G p (v, 0)

theorem planeParameterDirectional_contDiff {n : ℕ∞} {G : Plane × ℝ → ℂ}
    (hG : ContDiff ℝ (n + 1) G) (v : Plane) :
    ContDiff ℝ n (planeParameterDirectional G v) :=
  (hG.fderiv_right le_rfl).clm_apply contDiff_const

theorem directionalKernel_plane_parameter {G : Plane × ℝ → ℂ} (hG : ContDiff ℝ 1 G)
    (v x : Plane) (t : ℝ) :
    directionalKernel (fun y : Plane => G (y, t)) v x = planeParameterDirectional G v (x, t) := by
  have hh := ((hG.differentiable one_ne_zero).differentiableAt (x := (x, t))).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  simp only [Function.comp_def] at hh
  change fderiv ℝ (fun y : Plane => G (y, t)) x v = _
  rw [hh.fderiv]
  simp only [planeParameterDirectional, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

theorem directionalKernel_plane_intervalIntegral {G : Plane × ℝ → ℂ} (hG : ContDiff ℝ 1 G)
    (a b : ℝ) (v x : Plane) :
    directionalKernel (fun y : Plane => ∫ t : ℝ in a..b, G (y, t)) v x =
      ∫ t : ℝ in a..b, planeParameterDirectional G v (x, t) := by
  let H : Plane × ℝ → Plane →L[ℝ] ℂ := fun p =>
    (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ Plane ℝ)
  have hH : Continuous H :=
    ((hG.continuous_fderiv one_ne_zero).clm_comp continuous_const)
  have hd (y : Plane) (t : ℝ) : HasFDerivAt (fun w : Plane => G (w, t)) (H (y, t)) y := by
    have hh := ((hG.differentiable one_ne_zero).differentiableAt (x := (y, t))).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
    simpa only [Function.comp_def, H] using hh
  have hh := hasFDerivAt_plane_intervalIntegral_of_joint_continuous
    (G := fun y t => G (y, t)) (H := fun y t => H (y, t))
    (by convert! hG.continuous using 1 <;> rfl) (by convert! hH using 1 <;> rfl) hd a b x
  change fderiv ℝ (fun y : Plane => ∫ t : ℝ in a..b, G (y, t)) x v = _
  rw [hh.fderiv]
  have hHx : Continuous (fun t : ℝ => H (x, t)) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hi : IntervalIntegrable (fun t : ℝ => H (x, t)) volume a b := hHx.intervalIntegrable a b
  calc
    (∫ t : ℝ in a..b, H (x, t)) v = ∫ t : ℝ in a..b, H (x, t) v :=
      ContinuousLinearMap.intervalIntegral_apply hi v
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      rfl

theorem directionalSecond_plane_intervalIntegral {G : Plane × ℝ → ℂ} (hG : ContDiff ℝ 2 G)
    (a b : ℝ) (v w x : Plane) :
    directionalSecond (fun y : Plane => ∫ t : ℝ in a..b, G (y, t)) v w x =
      ∫ t : ℝ in a..b, planeParameterDirectional (planeParameterDirectional G v) w (x, t) := by
  have hG₁ : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hfun : directionalKernel (fun y : Plane => ∫ t : ℝ in a..b, G (y, t)) v =
      fun y : Plane => ∫ t : ℝ in a..b, planeParameterDirectional G v (y, t) :=
    funext (directionalKernel_plane_intervalIntegral hG₁ a b v)
  unfold directionalSecond
  rw [hfun]
  exact directionalKernel_plane_intervalIntegral (planeParameterDirectional_contDiff (n := 1) hG v) a b w x

theorem directionalSecond_plane_parameter {G : Plane × ℝ → ℂ} (hG : ContDiff ℝ 2 G)
    (v w x : Plane) (t : ℝ) :
    directionalSecond (fun y : Plane => G (y, t)) v w x =
      planeParameterDirectional (planeParameterDirectional G v) w (x, t) := by
  have hG₁ : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hfun : directionalKernel (fun y : Plane => G (y, t)) v =
      fun y : Plane => planeParameterDirectional G v (y, t) :=
    funext (fun y => directionalKernel_plane_parameter hG₁ v y t)
  unfold directionalSecond
  rw [hfun]
  exact directionalKernel_plane_parameter (planeParameterDirectional_contDiff (n := 1) hG v) w x t

/-- Two derivatives and the actual two-coordinate trace commute with the
compact parameter integral under joint C² regularity. -/
theorem laplacian_plane_intervalIntegral {G : Plane × ℝ → ℂ} (hG : ContDiff ℝ 2 G)
    (a b : ℝ) (x : Plane) :
    laplacian (fun y : Plane => ∫ t : ℝ in a..b, G (y, t)) x =
      ∫ t : ℝ in a..b, laplacian (fun y : Plane => G (y, t)) x := by
  have hI : ContDiff ℝ 2 (fun y : Plane => ∫ t : ℝ in a..b, G (y, t)) :=
    contDiff_plane_intervalIntegral hG a b
  have hslice (t : ℝ) : ContDiff ℝ 2 (fun y : Plane => G (y, t)) :=
    hG.comp (contDiff_id.prodMk contDiff_const)
  have hC (v : Plane) : Continuous (planeParameterDirectional (planeParameterDirectional G v) v) :=
    (planeParameterDirectional_contDiff (n := 0)
      (planeParameterDirectional_contDiff (n := 1) hG v) v).continuous
  have hi (v : Plane) : IntervalIntegrable
      (fun t : ℝ => planeParameterDirectional (planeParameterDirectional G v) v (x, t)) volume a b :=
    ((hC v).comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  rw [laplacian_eq_directionalSecond_on isOpen_univ hI.contDiffOn (Set.mem_univ x),
    directionalSecond_plane_intervalIntegral hG,
    directionalSecond_plane_intervalIntegral hG,
    ← intervalIntegral.integral_add (hi distributionAxis0) (hi distributionAxis1)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [laplacian_eq_directionalSecond_on isOpen_univ (hslice t).contDiffOn (Set.mem_univ x),
    directionalSecond_plane_parameter hG, directionalSecond_plane_parameter hG]

def planeRotation (θ : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  complexToPlane.symm.trans ((rotation (Circle.exp θ)).trans complexToPlane)

theorem planeRotation_apply (θ : ℝ) (x : Plane) :
    planeRotation θ x = complexToPlane (Complex.exp ((θ : ℂ) * Complex.I) * complexToPlane.symm x) := by
  simp only [planeRotation, LinearIsometryEquiv.trans_apply, rotation_apply, Circle.coe_exp]

theorem contDiff_planeRotation_joint {n : ℕ∞} :
    ContDiff ℝ n (fun p : Plane × ℝ => planeRotation p.2 p.1) := by
  have he : ContDiff ℝ n (fun p : Plane × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I)) :=
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const).cexp
  have hx : ContDiff ℝ n (fun p : Plane × ℝ => complexToPlane.symm p.1) :=
    complexToPlane.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp contDiff_fst
  have hh := complexToPlane.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp (he.mul hx)
  have hfun : (fun p : Plane × ℝ => planeRotation p.2 p.1) =
      fun p : Plane × ℝ => complexToPlane (Complex.exp ((p.2 : ℂ) * Complex.I) * complexToPlane.symm p.1) :=
    funext (fun p => planeRotation_apply p.2 p.1)
  rw [hfun]
  exact hh

theorem continuous_planeRotation_joint : Continuous (fun p : Plane × ℝ => planeRotation p.2 p.1) :=
  (contDiff_planeRotation_joint (n := 0)).continuous

def angularProjection (f : Plane → ℂ) (m : ℤ) (x : Plane) : ℂ :=
  angularFourierAt f m (complexToPlane.symm x)

theorem angularProjection_eq_integral (f : Plane → ℂ) (m : ℤ) (x : Plane) :
    angularProjection f m x = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      helmholtzAngularWeight m θ * f (planeRotation θ x) := by
  unfold angularProjection angularFourierAt
  simp only [planeRotation_apply]

theorem continuous_angularProjection_integrand {f : Plane → ℂ} (hf : Continuous f) (m : ℤ) :
    Continuous (fun p : Plane × ℝ => helmholtzAngularWeight m p.2 * f (planeRotation p.2 p.1)) :=
  ((continuous_helmholtzAngularWeight m).comp continuous_snd).mul
    (hf.comp continuous_planeRotation_joint)

theorem angularProjection_continuous {f : Plane → ℂ} (hf : Continuous f) (m : ℤ) :
    Continuous (angularProjection f m) := by
  have hfun : angularProjection f m = fun x : Plane => ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      helmholtzAngularWeight m θ * f (planeRotation θ x) := funext (angularProjection_eq_integral f m)
  rw [hfun]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x : Plane => fun θ : ℝ => helmholtzAngularWeight m θ * f (planeRotation θ x))
  convert! continuous_angularProjection_integrand hf m using 1 <;> rfl

/-- Finite as well as infinite smoothness is retained by the actual projection. -/
theorem angularProjection_contDiff {f : Plane → ℂ} {n : ℕ∞} (hf : ContDiff ℝ n f) (m : ℤ) :
    ContDiff ℝ n (angularProjection f m) := by
  have hw : ContDiff ℝ n (fun p : Plane × ℝ => helmholtzAngularWeight m p.2) := by
    unfold helmholtzAngularWeight
    have ht : ContDiff ℝ n (fun p : Plane × ℝ => (p.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_snd
    have hl : ContDiff ℝ n (fun p : Plane × ℝ => (-Complex.I * (m : ℂ)) * (p.2 : ℂ)) :=
      contDiff_const.mul ht
    exact hl.cexp
  have hG : ContDiff ℝ n (fun p : Plane × ℝ =>
      helmholtzAngularWeight m p.2 * f (planeRotation p.2 p.1)) :=
    hw.mul (hf.comp contDiff_planeRotation_joint)
  have hfun : angularProjection f m = fun x : Plane => ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      helmholtzAngularWeight m θ * f (planeRotation θ x) := funext (angularProjection_eq_integral f m)
  rw [hfun]
  exact contDiff_plane_intervalIntegral hG 0 (2 * Real.pi)

/-- The actual Laplacian commutes with the actual angular projection under
global C² regularity, so finite-order constructions are sufficient. -/
theorem laplacian_angularProjection {f : Plane → ℂ} (hf : ContDiff ℝ 2 f)
    (m : ℤ) (x : Plane) :
    laplacian (angularProjection f m) x = angularProjection (laplacian f) m x := by
  have hw : ContDiff ℝ 2 (fun p : Plane × ℝ => helmholtzAngularWeight m p.2) := by
    unfold helmholtzAngularWeight
    have ht : ContDiff ℝ 2 (fun p : Plane × ℝ => (p.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_snd
    have hl : ContDiff ℝ 2 (fun p : Plane × ℝ => (-Complex.I * (m : ℂ)) * (p.2 : ℂ)) :=
      contDiff_const.mul ht
    exact hl.cexp
  have hG : ContDiff ℝ 2 (fun p : Plane × ℝ =>
      helmholtzAngularWeight m p.2 * f (planeRotation p.2 p.1)) :=
    hw.mul (hf.comp contDiff_planeRotation_joint)
  have hfun : angularProjection f m = fun y : Plane => ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      helmholtzAngularWeight m θ * f (planeRotation θ y) := funext (angularProjection_eq_integral f m)
  rw [hfun, laplacian_plane_intervalIntegral hG, angularProjection_eq_integral]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  have hrot : ContDiff ℝ 2 (f ∘ planeRotation θ) :=
    hf.comp (planeRotation θ).toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  change laplacian (helmholtzAngularWeight m θ • (f ∘ planeRotation θ)) x = _
  rw [InnerProductSpace.laplacian_smul (helmholtzAngularWeight m θ) hrot.contDiffAt,
    laplacian_comp_linearIsometryEquiv]
  rfl

theorem planeRotation_circleDirection (θ α : ℝ) :
    planeRotation θ (circleDirection α) = circleDirection (α + θ) := by
  apply complexToPlane.symm.injective
  rw [planeRotation_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply, complexToPlane_symm_circleDirection,
    Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- Rotation covariance of the actual circular integral, proved by an actual
periodic change of angular variable. -/
theorem circularMean_comp_planeRotation {f : Plane → ℂ} (_hf : Continuous f)
    (θ r : ℝ) (x : Plane) :
    circularMean (fun y : Plane => f (planeRotation θ y)) r x = circularMean f r (planeRotation θ x) := by
  let F : ℝ → ℂ := fun α => f (planeRotation θ x + r • circleDirection α)
  have hp : Function.Periodic F (2 * Real.pi) := by
    intro α
    dsimp only [F]
    rw [circleDirection_periodic α]
  have hs := intervalIntegral_periodic_shift F hp θ
  unfold circularMean
  congr 1
  calc
    _ = ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), F (α + θ) := by
      apply intervalIntegral.integral_congr
      intro α _
      dsimp only [F]
      rw [map_add, map_smul, planeRotation_circleDirection]
    _ = ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), F α := by
      simpa only [add_comm] using hs

/-- The double angular integral is swapped by the actual compact-square
integrability theorem, after proving joint continuity of the geometric action. -/
theorem angularProjection_circularMean_comm {f : Plane → ℂ} (hf : Continuous f)
    (m : ℤ) (r : ℝ) (x : Plane) :
    angularProjection (circularMean f r) m x = circularMean (angularProjection f m) r x := by
  let G : ℝ → ℝ → ℂ := fun θ α =>
    helmholtzAngularWeight m θ * f (planeRotation θ (x + r • circleDirection α))
  have hG : Continuous (Function.uncurry G) := by
    have hA : Continuous (fun p : ℝ × ℝ => x + r • circleDirection p.2) :=
      continuous_const.add ((continuous_circleDirection.comp continuous_snd).const_smul r)
    have hR : Continuous (fun p : ℝ × ℝ => planeRotation p.1 (x + r • circleDirection p.2)) := by
      have hfun : (fun p : ℝ × ℝ => planeRotation p.1 (x + r • circleDirection p.2)) =
          fun p : ℝ × ℝ => complexToPlane (Complex.exp ((p.1 : ℂ) * Complex.I) *
            complexToPlane.symm (x + r • circleDirection p.2)) :=
        funext (fun p => planeRotation_apply p.1 (x + r • circleDirection p.2))
      rw [hfun]
      have he : Continuous (fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) * Complex.I)) := by fun_prop
      exact complexToPlane.continuous.comp
        (he.mul (complexToPlane.symm.continuous.comp hA))
    exact ((continuous_helmholtzAngularWeight m).comp continuous_fst).mul (hf.comp hR)
  have hright : circularMean (angularProjection f m) r x =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi),
        angularProjection f m (x + r • circleDirection α) :=
    circularMean_eq_complex_prefactor (angularProjection f m) r x
  rw [hright]
  rw [angularProjection_eq_integral]
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ * ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [G]
      rw [← circularMean_comp_planeRotation hf θ r x, circularMean_eq_complex_prefactor]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = (2 * (Real.pi : ℂ))⁻¹ * ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi),
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α := by
      rw [intervalIntegral_continuous_square_swap hG]
    _ = _ := by
      congr 1

theorem angularProjection_sub {f g : Plane → ℂ} (hf : Continuous f) (hg : Continuous g)
    (m : ℤ) (x : Plane) :
    angularProjection (fun y => f y - g y) m x = angularProjection f m x - angularProjection g m x := by
  simp only [angularProjection_eq_integral, mul_sub]
  have hi (h : Plane → ℂ) (hh : Continuous h) :
      IntervalIntegrable (fun θ : ℝ => helmholtzAngularWeight m θ * h (planeRotation θ x))
        volume 0 (2 * Real.pi) :=
    ((continuous_angularProjection_integrand hh m).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  exact intervalIntegral.integral_sub (hi f hf) (hi g hg)

theorem angularProjection_congr_on_ball {f g : Plane → ℂ} {S : ℝ}
    (hfg : EqOn f g (planeBall S)) (m : ℤ) {x : Plane} (hx : x ∈ planeBall S) :
    angularProjection f m x = angularProjection g m x := by
  simp only [angularProjection_eq_integral]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [hfg (by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right, (planeRotation θ).norm_map] using hx)]

/-- Low-degree coordinate-polynomial mean defects are annihilated on the
same rotation-invariant center ball, with no global defect identity required. -/
theorem angularProjection_meanIdentity_of_polynomial_defect {f : Plane → ℂ} (hf : Continuous f)
    (r : ℝ) (p : Polynomial ℂ) (m : ℤ) (hm : p.natDegree < m.natAbs) {S : ℝ}
    (hdefect : EqOn (fun y => circularMean f r y - f y)
      (fun y : Plane => p.eval (y 0 : ℂ)) (planeBall S)) :
    ∀ x ∈ planeBall S, circularMean (angularProjection f m) r x = angularProjection f m x := by
  intro x hx
  have he := angularProjection_congr_on_ball hdefect m hx
  rw [angularProjection_sub (continuous_circularMean_center_of_continuous hf r) hf,
    angularProjection_circularMean_comm hf] at he
  have hz : angularProjection (fun y : Plane => p.eval (y 0 : ℂ)) m x = 0 :=
    angularFourierAt_coordinate_polynomial_eq_zero p m hm (complexToPlane.symm x)
  rw [hz] at he
  exact sub_eq_zero.mp he

end J0RadialUniqueness
