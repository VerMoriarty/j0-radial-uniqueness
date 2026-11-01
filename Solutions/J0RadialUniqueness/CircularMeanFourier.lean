import Solutions.J0RadialUniqueness.AngularFourierRotation
import Solutions.J0RadialUniqueness.SmoothMeanReduction

/-! The actual circular mean under angular Fourier projection. The angular
shift and the order of integration are justified for continuous inputs before
passing to the radial annular integral. -/

noncomputable section

open MeasureTheory Set

namespace J0RadialUniqueness

theorem circle_chord_rotation (ρ r θ α : ℝ) :
    ρ • circleDirection θ + r • circleDirection (θ + α) =
      complexToPlane (Complex.exp ((θ : ℂ) * Complex.I) *
        ((ρ : ℂ) + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I))) := by
  apply complexToPlane.symm.injective
  simp only [map_add, map_smul, complexToPlane_symm_circleDirection,
    Complex.real_smul, LinearIsometryEquiv.symm_apply_apply, Complex.ofReal_add,
    add_mul, Complex.exp_add]
  ring

theorem circularMean_eq_complex_prefactor (f : Plane → ℂ) (r : ℝ) (x : Plane) :
    circularMean f r x = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (x + r • circleDirection θ) := by
  simp only [circularMean, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

theorem intervalIntegral_periodic_shift (F : ℝ → ℂ)
    (hp : Function.Periodic F (2 * Real.pi)) (β : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F (θ + β)) =
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hp.intervalIntegral_add_eq β 0

theorem intervalIntegral_continuous_square_swap {G : ℝ → ℝ → ℂ}
    (hG : Continuous (Function.uncurry G)) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α) =
      ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α := by
  have hI : IntegrableOn (Function.uncurry G)
      (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) (2 * Real.pi))
      (volume.prod volume) :=
    hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hI.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact integral_integral_swap hi

theorem angularProjection_circularMean_eq_chord_integral {f : Plane → ℂ}
    (hf : Continuous f) (m : ℤ) (ρ r : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      helmholtzAngularWeight m θ * circularMean f r (ρ • circleDirection θ)) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi),
        angularFourierAt f m ((ρ : ℂ) + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) := by
  let G : ℝ → ℝ → ℂ := fun θ α =>
    helmholtzAngularWeight m θ * f (ρ • circleDirection θ + r • circleDirection (θ + α))
  have hG : Continuous (Function.uncurry G) := by
    have hdir₁ : Continuous (fun p : ℝ × ℝ => ρ • circleDirection p.1) := by
      convert! (continuous_circleDirection.comp continuous_fst).const_smul ρ using 1 <;> rfl
    have hdir₂ : Continuous (fun p : ℝ × ℝ => r • circleDirection (p.1 + p.2)) := by
      convert! (continuous_circleDirection.comp (continuous_fst.add continuous_snd)).const_smul r using 1 <;> rfl
    exact ((continuous_helmholtzAngularWeight m).comp continuous_fst).mul
      (hf.comp (hdir₁.add hdir₂))
  have hinner (θ : ℝ) : helmholtzAngularWeight m θ * circularMean f r (ρ • circleDirection θ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α := by
    let F : ℝ → ℂ := fun α => f (ρ • circleDirection θ + r • circleDirection α)
    have hp : Function.Periodic F (2 * Real.pi) := by
      intro α
      dsimp only [F]
      rw [circleDirection_periodic α]
    have hs : (∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), F α) =
        ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), F (θ + α) := by
      simpa only [add_comm] using (intervalIntegral_periodic_shift F hp θ).symm
    rw [circularMean_eq_complex_prefactor]
    change helmholtzAngularWeight m θ *
      ((2 * (Real.pi : ℂ))⁻¹ * ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), F α) = _
    rw [hs]
    dsimp only [G, F]
    rw [intervalIntegral.integral_const_mul]
    ring
  calc
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        (2 * (Real.pi : ℂ))⁻¹ * ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hinner θ
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α :=
      intervalIntegral.integral_const_mul _ _
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ α : ℝ in (0 : ℝ)..(2 * Real.pi), ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), G θ α := by
      rw [intervalIntegral_continuous_square_swap hG]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro α _
      unfold angularFourierAt
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [G]
      rw [circle_chord_rotation]

end J0RadialUniqueness
