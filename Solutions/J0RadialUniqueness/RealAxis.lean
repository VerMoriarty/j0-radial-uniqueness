import Solutions.J0RadialUniqueness.FODE
import Solutions.J0RadialUniqueness.FEnergy

/-! The strict bound on the real axis, proved directly from the closed F ODE.

This replaces the paper's appeal to Bessel's integral formula by a dissipative
energy identity on a negative-real direction. All coefficients, derivatives,
boundary values and the ODE refer to the actual factorial series F.
-/

noncomputable section

namespace J0RadialUniqueness

def negativeAxisEnergy (q s : ℝ) : ℝ :=
  ‖FRay (-(q : ℂ)) s‖ ^ 2 +
    (s / q) * ‖FRaySlope (-(q : ℂ)) s‖ ^ 2

@[simp] theorem negativeAxisEnergy_zero (q : ℝ) : negativeAxisEnergy q 0 = 1 := by
  simp [negativeAxisEnergy]

/-- Dissipation of the negative-axis radial energy, including the endpoint zero. -/
theorem negativeAxisEnergy_hasDerivAt {q : ℝ} (hq : 0 < q) (s : ℝ) :
    HasDerivAt (negativeAxisEnergy q)
      (-(1 / q) * ‖FRaySlope (-(q : ℂ)) s‖ ^ 2) s := by
  have hscalar :
      inner ℝ (FRaySlope (-(q : ℂ)) s) ((s : ℂ) * FRayAccel (-(q : ℂ)) s) =
        s * inner ℝ (FRaySlope (-(q : ℂ)) s) (FRayAccel (-(q : ℂ)) s) := by
    change inner ℝ (FRaySlope (-(q : ℂ)) s) (s • FRayAccel (-(q : ℂ)) s) = _
    exact real_inner_smul_right _ _ _
  have hscalarq :
      inner ℝ (FRaySlope (-(q : ℂ)) s) (-(q : ℂ) * FRay (-(q : ℂ)) s) =
        -q * inner ℝ (FRaySlope (-(q : ℂ)) s) (FRay (-(q : ℂ)) s) := by
    calc
      _ = inner ℝ (FRaySlope (-(q : ℂ)) s) ((-q) • FRay (-(q : ℂ)) s) := by
        simp only [Complex.real_smul, Complex.ofReal_neg]
      _ = _ := real_inner_smul_right _ _ _
  have he := congrArg (fun v : ℂ => inner ℝ (FRaySlope (-(q : ℂ)) s) v)
    (FRay_ode F_ode_statement (-(q : ℂ)) s)
  rw [inner_add_right, hscalar, hscalarq, real_inner_self_eq_norm_sq] at he
  rw [← real_inner_comm (FRaySlope (-(q : ℂ)) s) (FRay (-(q : ℂ)) s)] at he
  have hd := (FRay_hasDerivAt (-(q : ℂ)) s).norm_sq.add
    (((hasDerivAt_id s).div_const q).mul
      (FRaySlope_hasDerivAt (-(q : ℂ)) s).norm_sq)
  change HasDerivAt (negativeAxisEnergy q)
    (2 * inner ℝ (FRay (-(q : ℂ)) s) (FRaySlope (-(q : ℂ)) s) +
      (1 / q * ‖FRaySlope (-(q : ℂ)) s‖ ^ 2 +
        (s / q) * (2 * inner ℝ (FRaySlope (-(q : ℂ)) s) (FRayAccel (-(q : ℂ)) s)))) s at hd
  apply hd.congr_deriv
  field_simp [hq.ne']
  nlinarith only [he]

/-- The initial slope is nonzero, so the total energy has strictly decreased at time one. -/
theorem negativeAxisEnergy_one_lt_one {q : ℝ} (hq : 0 < q) :
    negativeAxisEnergy q 1 < 1 := by
  have hs : Continuous (FRaySlope (-(q : ℂ))) :=
    continuous_iff_continuousAt.mpr
      (fun s => (FRaySlope_hasDerivAt (-(q : ℂ)) s).continuousAt)
  have hc : Continuous (fun s : ℝ => ‖FRaySlope (-(q : ℂ)) s‖ ^ 2) := hs.norm.pow 2
  have hpos : 0 < ∫ s in (0 : ℝ)..1, ‖FRaySlope (-(q : ℂ)) s‖ ^ 2 := by
    apply intervalIntegral.integral_pos (by norm_num) hc.continuousOn
    · intro s _
      exact sq_nonneg _
    · refine ⟨0, by simp, ?_⟩
      rw [FRaySlope_zero]
      have hn : 0 < ‖-(q : ℂ)‖ :=
        norm_pos_iff.mpr (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hq.ne'))
      positivity
  have hdc : Continuous (fun s : ℝ =>
      -(1 / q) * ‖FRaySlope (-(q : ℂ)) s‖ ^ 2) := continuous_const.mul hc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := negativeAxisEnergy q)
    (f' := fun s => -(1 / q) * ‖FRaySlope (-(q : ℂ)) s‖ ^ 2)
    (fun s _ => negativeAxisEnergy_hasDerivAt hq s) (hdc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, negativeAxisEnergy_zero] at hftc
  have hneg : -(1 / q) *
      (∫ s in (0 : ℝ)..1, ‖FRaySlope (-(q : ℂ)) s‖ ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (by have := one_div_pos.mpr hq; linarith) hpos
  linarith

/-- The actual factorial series has modulus strictly below one on the negative real axis. -/
theorem F_negative_real_norm_lt_one {q : ℝ} (hq : 0 < q) : ‖F (-(q : ℂ))‖ < 1 := by
  have hE := negativeAxisEnergy_one_lt_one hq
  simp only [negativeAxisEnergy, FRay, Complex.ofReal_one, one_mul] at hE
  have hnonneg : 0 ≤ (1 / q) * ‖FRaySlope (-(q : ℂ)) 1‖ ^ 2 := by positivity
  have hn : 0 ≤ ‖F (-(q : ℂ))‖ := norm_nonneg _
  nlinarith

/-- Lemma 2.2, with its external Bessel-integral citation eliminated. -/
theorem noRealOnePoints : NoRealOnePointsStatement := by
  intro x hx
  have hq : 0 < x ^ 2 / 4 := div_pos (sq_pos_of_ne_zero hx) (by norm_num)
  have h := F_negative_real_norm_lt_one hq
  have hw : -((x ^ 2 / 4 : ℝ) : ℂ) = -(x : ℂ) ^ 2 / 4 := by
    push_cast
    ring
  rw [hw] at h
  exact h

end J0RadialUniqueness
