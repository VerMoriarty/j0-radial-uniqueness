import Solutions.J0RadialUniqueness.FAnalytic

/-!
The differential equation of the actual factorial series F.  Derivatives are
obtained from its global power series, and the ODE is the factorial coefficient
recurrence, with no assumptions about the desired localization result.
-/

noncomputable section

namespace J0RadialUniqueness

/-- The scalar derivative of a formal power series, using evaluation at 1. -/
def scalarDerivSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries p.derivSeries

/-- Differentiating a scalar power series multiplies its next coefficient by n+1. -/
theorem scalarDerivSeries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (scalarDerivSeries p).coeff n = ((n + 1 : ℕ) : ℂ) * p.coeff (n + 1) := by
  change p.derivSeries.coeff n 1 = _
  simpa only [nsmul_eq_mul] using p.derivSeries_coeff_one n

/-- The entire power-series expansion passes to the scalar derivative. -/
theorem scalarDerivSeries_hasFPowerSeriesOnBall
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (h : HasFPowerSeriesOnBall f p 0 ⊤) :
    HasFPowerSeriesOnBall (deriv f) (scalarDerivSeries p) 0 ⊤ := by
  have hh := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv
  have he : ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) ∘ (fderiv ℂ f)) = deriv f := by
    funext x
    rfl
  rw [he] at hh
  exact hh

/-- Coefficients of the first complex derivative of F. -/
def FFirstCoefficient (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) / ((n + 1).factorial : ℂ) ^ 2

/-- Coefficients of the second complex derivative of F. -/
def FSecondCoefficient (n : ℕ) : ℂ :=
  (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)) / ((n + 2).factorial : ℂ) ^ 2

@[simp]
theorem FFirstCoefficient_zero : FFirstCoefficient 0 = 1 := by
  norm_num [FFirstCoefficient]

/-- The recurrence that gives the differential equation coefficient by coefficient. -/
theorem F_ode_coefficient (n : ℕ) :
    FSecondCoefficient n + FFirstCoefficient (n + 1) =
      1 / ((n + 1).factorial : ℂ) ^ 2 := by
  have hfac : ((n + 2).factorial : ℂ) =
      ((n + 2 : ℕ) : ℂ) * ((n + 1).factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have hf : ((n + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  have hn : (n : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show n + 2 ≠ 0 by omega)
  simp only [FFirstCoefficient, FSecondCoefficient, hfac]
  push_cast
  field_simp [hf, hn] <;> ring

/-- The full differentiated series, valid at every complex point. -/
theorem F_firstDerivative_hasSum (w : ℂ) :
    HasSum (fun n : ℕ => FFirstCoefficient n * w ^ n) (deriv F w) := by
  have h := scalarDerivSeries_hasFPowerSeriesOnBall F_hasFPowerSeriesOnBall
  have hs := h.hasSum (y := w) (by simp)
  have hfun : (fun n : ℕ => scalarDerivSeries FPowerSeries n (fun _ => w)) =
      (fun n : ℕ => FFirstCoefficient n * w ^ n) := by
    funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, scalarDerivSeries_coeff]
    simp [FPowerSeries, FormalMultilinearSeries.coeff_ofScalars, FFirstCoefficient,
      smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hfun, zero_add] at hs
  exact hs

/-- The second differentiated series, also valid at the regular singular point zero. -/
theorem F_secondDerivative_hasSum (w : ℂ) :
    HasSum (fun n : ℕ => FSecondCoefficient n * w ^ n) (deriv (deriv F) w) := by
  have h := scalarDerivSeries_hasFPowerSeriesOnBall
    (scalarDerivSeries_hasFPowerSeriesOnBall F_hasFPowerSeriesOnBall)
  have hs := h.hasSum (y := w) (by simp)
  have hfun :
      (fun n : ℕ => scalarDerivSeries (scalarDerivSeries FPowerSeries) n (fun _ => w)) =
      (fun n : ℕ => FSecondCoefficient n * w ^ n) := by
    funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      scalarDerivSeries_coeff, scalarDerivSeries_coeff]
    simp [FPowerSeries, FormalMultilinearSeries.coeff_ofScalars, FSecondCoefficient,
      smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Nat.add_assoc]
  rw [hfun, zero_add] at hs
  exact hs

/-- The exact order-zero hypergeometric ODE satisfied by F. -/
theorem F_ode (w : ℂ) : w * deriv (deriv F) w + deriv F w = F w := by
  have hfirst := F_firstDerivative_hasSum w
  have hsecond := F_secondDerivative_hasSum w
  have hfirstSplit := hfirst.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, mul_one,
    FFirstCoefficient_zero] at hfirstSplit
  rw [hfirst.tsum_eq] at hfirstSplit
  have htailEq :
      (∑' n : ℕ, FFirstCoefficient (n + 1) * w ^ (n + 1)) = deriv F w - 1 := by
    linear_combination hfirstSplit
  have htailSummable :
      Summable (fun n : ℕ => FFirstCoefficient (n + 1) * w ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hfirst.summable
  have htail : HasSum (fun n : ℕ => FFirstCoefficient (n + 1) * w ^ (n + 1))
      (deriv F w - 1) := by
    rw [← htailEq]
    exact htailSummable.hasSum
  have hcombined := (hsecond.mul_left w).add htail
  have hfun :
      (fun n : ℕ => w * (FSecondCoefficient n * w ^ n) +
        FFirstCoefficient (n + 1) * w ^ (n + 1)) =
      (fun n : ℕ => fTerm w (n + 1)) := by
    funext n
    calc
      w * (FSecondCoefficient n * w ^ n) +
          FFirstCoefficient (n + 1) * w ^ (n + 1) =
          (FSecondCoefficient n + FFirstCoefficient (n + 1)) * w ^ (n + 1) := by
        rw [pow_succ]
        ring
      _ = fTerm w (n + 1) := by
        rw [F_ode_coefficient]
        simp [fTerm, div_eq_mul_inv, mul_comm]
  rw [hfun] at hcombined
  have hcombinedEq := hcombined.tsum_eq
  have hFSplit := (fTerm_summable w).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, fTerm, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one] at hFSplit
  change (1 : ℂ) + (∑' n : ℕ, fTerm w (n + 1)) = F w at hFSplit
  linear_combination hFSplit - hcombinedEq

/-- The complete analytic/ODE assertion used in the paper's energy argument. -/
theorem F_ode_statement : FODEStatement :=
  ⟨F_differentiable, F_deriv_differentiable, F_ode⟩

end J0RadialUniqueness
