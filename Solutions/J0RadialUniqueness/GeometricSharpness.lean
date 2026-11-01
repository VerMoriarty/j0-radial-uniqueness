import Solutions.J0RadialUniqueness.SharpnessScaling
import Solutions.J0RadialUniqueness.SharpnessMollification
import Solutions.J0RadialUniqueness.OnePointExistence
import Solutions.J0RadialUniqueness.UnitCriticalNonharmonic

/-! Geometric assembly of the two sharpness statements.  The intermediate
theorems expose the unit construction as an input; the final theorems supply
it using the actual proved unit nonharmonic construction.  Positive dilation,
radius-order exchange, the equal-radius spectral branch, and actual local
mollification discharge the geometric steps. -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace J0RadialUniqueness

/-- The internal unit construction needed by the geometric assembly.
This is a specification of the remaining spectral leaf, not an axiom. -/
def UnitCriticalLocalCounterexampleStatement : Prop :=
  ∀ τ : ℝ, 1 < τ → ∀ n : ℕ, 2 ≤ n →
    ∃ f : Plane → ℂ,
      ContDiff ℝ (n : ℕ∞ω) f ∧
      MeanIdentityOn f 1 (planeBall ((1 + τ) - 1)) ∧
      MeanIdentityOn f τ (planeBall ((1 + τ) - τ)) ∧
      ∀ δ : ℝ, 1 < δ → δ ≤ 1 + τ →
        ¬ DistributionHarmonicOn f (planeBall δ)

theorem boundaryFiniteSmoothCounterexample_ordered_of_unit
    (hunit : UnitCriticalLocalCounterexampleStatement)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (_hr₂ : 0 < r₂) (hlt : r₁ < r₂) (k : ℕ) :
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ (k : ℕ∞ω) f (planeBall (r₁ + r₂)) ∧
      LocallyIntegrableOn f (planeBall (r₁ + r₂)) ∧
      MeanIdentityOn f r₁ (planeBall ((r₁ + r₂) - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall ((r₁ + r₂) - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall (r₁ + r₂)) := by
  let τ : ℝ := r₂ / r₁
  have hτ : 1 < τ := by
    apply (lt_div_iff₀ hr₁).mpr
    simpa only [one_mul] using hlt
  let n : ℕ := max k 2
  have hn : 2 ≤ n := le_max_right _ _
  have hk : k ≤ n := le_max_left _ _
  obtain ⟨f, hf, hm₁, hm₂, hnot⟩ := hunit τ hτ n hn
  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast hn)
  have hsum : r₁ * (1 + τ) = r₁ + r₂ := by
    dsimp only [τ]
    field_simp [hr₁.ne'] <;> ring
  have hsecond : r₁ * τ = r₂ := by
    dsimp only [τ]
    field_simp [hr₁.ne']
  have hscaled := sharpnessScale_contDiff hf r₁
  have hfirstMean : MeanIdentityOn (sharpnessScale f r₁) r₁
      (planeBall ((r₁ + r₂) - r₁)) := by
    simpa only [mul_one, hsum] using meanIdentityOn_sharpnessScale_natural hr₁ hm₁
  have hsecondMean : MeanIdentityOn (sharpnessScale f r₁) r₂
      (planeBall ((r₁ + r₂) - r₂)) := by
    simpa only [hsum, hsecond] using meanIdentityOn_sharpnessScale_natural hr₁ hm₂
  have hnon : ¬ DistributionHarmonicOn (sharpnessScale f r₁) (planeBall (r₁ + r₂)) := by
    have hh := not_distributionHarmonicOn_sharpnessScale hr₁ hf₂.contDiffOn
      (hnot (1 + τ) (by linarith) le_rfl)
    simpa only [hsum] using hh
  exact ⟨sharpnessScale f r₁, (hscaled.of_le (by exact_mod_cast hk)).contDiffOn,
    hscaled.continuous.locallyIntegrable.locallyIntegrableOn _, hfirstMean, hsecondMean, hnon⟩

theorem subcriticalSmoothCounterexample_ordered_of_unit
    (hunit : UnitCriticalLocalCounterexampleStatement)
    {r₁ r₂ R : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : r₁ < r₂)
    (hR : max r₁ r₂ < R) (hsub : R < r₁ + r₂) :
    ∃ f : Plane → ℂ,
      ContDiffOn ℝ ∞ f (planeBall R) ∧ LocallyIntegrableOn f (planeBall R) ∧
      MeanIdentityOn f r₁ (planeBall (R - r₁)) ∧
      MeanIdentityOn f r₂ (planeBall (R - r₂)) ∧
      ¬ DistributionHarmonicOn f (planeBall R) := by
  let τ : ℝ := r₂ / r₁
  have hτ : 1 < τ := by
    apply (lt_div_iff₀ hr₁).mpr
    simpa only [one_mul] using hlt
  obtain ⟨f, hf, hm₁, hm₂, hnot⟩ := hunit τ hτ 2 le_rfl
  have hsum : r₁ * (1 + τ) = r₁ + r₂ := by
    dsimp only [τ]
    field_simp [hr₁.ne'] <;> ring
  have hsecond : r₁ * τ = r₂ := by
    dsimp only [τ]
    field_simp [hr₁.ne']
  have hR₁ : r₁ < R := (le_max_left r₁ r₂).trans_lt hR
  have hδlow : 1 < R / r₁ := by
    apply (lt_div_iff₀ hr₁).mpr
    simpa only [one_mul] using hR₁
  have hδhigh : R / r₁ ≤ 1 + τ := by
    apply (div_le_iff₀ hr₁).mpr
    rw [mul_comm, hsum]
    exact hsub.le
  have htarget : r₁ * (R / r₁) = R := by
    field_simp [hr₁.ne']
  have hnon : ¬ DistributionHarmonicOn (sharpnessScale f r₁) (planeBall R) := by
    have hh := not_distributionHarmonicOn_sharpnessScale hr₁ hf.contDiffOn
      (hnot (R / r₁) hδlow hδhigh)
    simpa only [htarget] using hh
  apply subcriticalSmoothCounterexample_of_critical_local_nonharmonicity hr₁ hr₂ hR hsub
  refine ⟨sharpnessScale f r₁,
    (sharpnessScale_contDiff hf r₁).continuous.locallyIntegrable.locallyIntegrableOn _, ?_, ?_, hnon⟩
  · simpa only [mul_one, hsum] using meanIdentityOn_sharpnessScale_natural hr₁ hm₁
  · simpa only [hsum, hsecond] using meanIdentityOn_sharpnessScale_natural hr₁ hm₂

/-- Full radius-order assembly, retaining its single explicit internal
spectral-construction input until that construction is supplied. -/
theorem boundaryFiniteSmoothCounterexample_of_unit
    (hunit : UnitCriticalLocalCounterexampleStatement) :
    BoundaryFiniteSmoothCounterexampleStatement := by
  intro r₁ r₂ hr₁ hr₂ k
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  · exact boundaryFiniteSmoothCounterexample_ordered_of_unit hunit hr₁ hr₂ hlt k
  · subst r₂
    exact boundaryFiniteSmoothCounterexample_equal_radii r₁ hr₁ k
  · obtain ⟨f, hf, hL, hm₂, hm₁, hn⟩ :=
      boundaryFiniteSmoothCounterexample_ordered_of_unit hunit hr₂ hr₁ hgt k
    refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [add_comm r₂ r₁] using hf
    · simpa only [add_comm r₂ r₁] using hL
    · simpa only [add_comm r₂ r₁] using hm₁
    · simpa only [add_comm r₂ r₁] using hm₂
    · simpa only [add_comm r₂ r₁] using hn

theorem subcriticalSmoothCounterexample_of_unit
    (hunit : UnitCriticalLocalCounterexampleStatement) :
    SubcriticalSmoothCounterexampleStatement := by
  intro r₁ r₂ R hr₁ hr₂ hR hsub
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  · exact subcriticalSmoothCounterexample_ordered_of_unit hunit hr₁ hr₂ hlt hR hsub
  · subst r₂
    exact subcriticalSmoothCounterexample_equal_radii r₁ R hr₁
      (by simpa only [max_self] using hR) hsub
  · obtain ⟨f, hf, hL, hm₂, hm₁, hn⟩ :=
      subcriticalSmoothCounterexample_ordered_of_unit hunit hr₂ hr₁ hgt
        (by simpa only [max_comm] using hR) (by simpa only [add_comm] using hsub)
    exact ⟨f, hf, hL, hm₁, hm₂, hn⟩

/-- The internal unit-construction specification is discharged by the
actual convergent-series candidate and its proved local nonharmonicity. -/
theorem unitCriticalLocalCounterexample : UnitCriticalLocalCounterexampleStatement := by
  intro τ hτ n hn
  exact exists_unitCriticalNonharmonic hτ n hn

theorem paper_boundary_finite_smooth_counterexample :
    BoundaryFiniteSmoothCounterexampleStatement :=
  boundaryFiniteSmoothCounterexample_of_unit unitCriticalLocalCounterexample

theorem paper_subcritical_smooth_counterexample :
    SubcriticalSmoothCounterexampleStatement :=
  subcriticalSmoothCounterexample_of_unit unitCriticalLocalCounterexample

end J0RadialUniqueness
