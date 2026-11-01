import Solutions.J0RadialUniqueness.FEnergy
import Solutions.J0RadialUniqueness.FODE
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
The right-half-plane strict modulus inequality for the actual function F.
The energy argument is first presented with its ODE input visible.  The last
result discharges that input using the proved factorial-series differential
equation, so it is an unconditional theorem about F.
-/

noncomputable section

open scoped Topology

namespace J0RadialUniqueness

/-- A nonzero initial radial slope remains nonzero at a positive point before
any prescribed positive endpoint. -/
theorem FRaySlope_exists_nonzero (a : ℂ) (ha : a ≠ 0) (s : ℝ) (hs : 0 < s) :
    ∃ u : ℝ, 0 < u ∧ u ≤ s ∧ FRaySlope a u ≠ 0 := by
  have hzero : FRaySlope a 0 ≠ 0 := by simpa only [FRaySlope_zero] using ha
  have hnear : ∀ᶠ u : ℝ in 𝓝 0, FRaySlope a u ≠ 0 :=
    (FRaySlope_hasDerivAt a 0).continuousAt.eventually_ne hzero
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let u : ℝ := min (s / 2) (ε / 2)
  have hu : 0 < u := lt_min (half_pos hs) (half_pos hε)
  have hus : u ≤ s := (min_le_left _ _).trans (by linarith)
  have hue : u < ε := (min_le_right _ _).trans_lt (by linarith)
  have huball : u ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu] using hue
  exact ⟨u, hu, hus, hsub huball⟩

/-- The nonnegative energy integrand has strictly positive integral in every
nonzero direction in the closed right half-plane. -/
theorem FRay_energy_integral_pos (a : ℂ) (ha : a ≠ 0) (hare : 0 ≤ a.re)
    (s : ℝ) (hs : 0 < s) :
    0 < ∫ u in (0 : ℝ)..s,
      (u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2) := by
  have hRay : Continuous (FRay a) :=
    continuous_iff_continuousAt.mpr (fun u => (FRay_hasDerivAt a u).continuousAt)
  have hSlope : Continuous (FRaySlope a) :=
    continuous_iff_continuousAt.mpr (fun u => (FRaySlope_hasDerivAt a u).continuousAt)
  have hg : Continuous (fun u : ℝ =>
      u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2) :=
    (continuous_id.mul (hSlope.norm.pow 2)).add
      (continuous_const.mul (hRay.norm.pow 2))
  obtain ⟨u, hu, hus, hne⟩ := FRaySlope_exists_nonzero a ha s hs
  have hvalue : 0 < u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2 :=
    add_pos_of_pos_of_nonneg
      (mul_pos hu (pow_pos (norm_pos_iff.mpr hne) 2))
      (mul_nonneg hare (sq_nonneg _))
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => 0)
    (g := fun u : ℝ => u * ‖FRaySlope a u‖ ^ 2 + a.re * ‖FRay a u‖ ^ 2)
    hs continuous_const.continuousOn hg.continuousOn
    (fun x hx => add_nonneg (mul_nonneg hx.1.le (sq_nonneg _))
      (mul_nonneg hare (sq_nonneg _)))
    ⟨u, ⟨hu.le, hus⟩, hvalue⟩
  simpa only [intervalIntegral.integral_zero] using hlt

/-- Positive energy forces strict radial increase of the squared modulus. -/
theorem FRayNormSq_deriv_pos_of_ode (hode : FODEStatement) (a : ℂ)
    (ha : a ≠ 0) (hare : 0 ≤ a.re) (s : ℝ) (hs : 0 < s) :
    0 < deriv (FRayNormSq a) s := by
  have hi := FRay_energy_integral_pos a ha hare s hs
  have hprod : 0 < s * deriv (FRayNormSq a) s := by
    rw [FRay_energy hode a s]
    exact mul_pos (by norm_num) hi
  exact (mul_pos_iff_of_pos_left hs).mp hprod

/-- The squared modulus is strictly increasing from its value one at zero. -/
theorem FRayNormSq_strictMonoOn_of_ode (hode : FODEStatement) (a : ℂ)
    (ha : a ≠ 0) (hare : 0 ≤ a.re) :
    StrictMonoOn (FRayNormSq a) (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · intro s _
    exact (FRayNormSq_hasDerivAt a s).continuousAt.continuousWithinAt
  · intro s hs
    have hs0 : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
    exact FRayNormSq_deriv_pos_of_ode hode a ha hare s hs0

/-- Lemma 2.1 follows from the energy identity and the actual initial derivative. -/
theorem fRightHalfPlane_of_ode (hode : FODEStatement) : FRightHalfPlaneStatement := by
  intro w hw hwr
  have hmono := FRayNormSq_strictMonoOn_of_ode hode w hw hwr
  have hY : FRayNormSq w 0 < FRayNormSq w 1 :=
    hmono (by simp) (by simp) (by norm_num)
  have hnormsq : (1 : ℝ) < ‖F w‖ ^ 2 := by
    simpa [FRayNormSq, FRay] using hY
  exact (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg (F w))).mp
    (by simpa only [one_pow] using hnormsq)

/-- The closed right-half-plane lemma, with its ODE input completely discharged. -/
theorem F_rightHalfPlane : FRightHalfPlaneStatement :=
  fRightHalfPlane_of_ode F_ode_statement

end J0RadialUniqueness
