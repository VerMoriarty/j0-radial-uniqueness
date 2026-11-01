import Solutions.J0RadialUniqueness.K0SeriesAnalytic

/-! The inhomogeneous differential equation for the harmonic-number correction
to the independent principal-branch K₀ series. -/

noncomputable section

namespace J0RadialUniqueness

def harmonicFFirstCoefficient (n : ℕ) : ℂ :=
  (harmonic (n + 1) : ℂ) * FFirstCoefficient n

def harmonicFSecondCoefficient (n : ℕ) : ℂ :=
  (harmonic (n + 2) : ℂ) * FSecondCoefficient n

@[simp] theorem harmonicFFirstCoefficient_zero : harmonicFFirstCoefficient 0 = 1 := by
  norm_num [harmonicFFirstCoefficient, FFirstCoefficient, harmonic_succ]

theorem harmonicF_ode_coefficient (n : ℕ) :
    harmonicFSecondCoefficient n + harmonicFFirstCoefficient (n + 1) =
      (harmonic (n + 1) : ℂ) / ((n + 1).factorial : ℂ) ^ 2 +
        FFirstCoefficient (n + 1) := by
  have hH : (harmonic (n + 2) : ℂ) =
      (harmonic (n + 1) : ℂ) + (((n + 2 : ℕ) : ℂ))⁻¹ := by
    have h := congrArg (fun q : ℚ => (q : ℂ)) (harmonic_succ (n + 1))
    push_cast at h
    simpa [Nat.add_assoc, add_assoc] using h
  have hfac : ((n + 2).factorial : ℂ) =
      ((n + 2 : ℕ) : ℂ) * ((n + 1).factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have hf : ((n + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  have hn : (n : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show n + 2 ≠ 0 by omega)
  calc
    harmonicFSecondCoefficient n + harmonicFFirstCoefficient (n + 1) =
        (harmonic (n + 2) : ℂ) * (FSecondCoefficient n + FFirstCoefficient (n + 1)) := by
      simp only [harmonicFSecondCoefficient, harmonicFFirstCoefficient, Nat.add_assoc]
      ring
    _ = (harmonic (n + 2) : ℂ) / ((n + 1).factorial : ℂ) ^ 2 := by
      rw [F_ode_coefficient]
      ring
    _ = _ := by
      rw [hH]
      unfold FFirstCoefficient
      rw [hfac]
      push_cast
      field_simp [hf, hn] <;> ring

theorem harmonicF_firstDerivative_hasSum (w : ℂ) :
    HasSum (fun n : ℕ => harmonicFFirstCoefficient n * w ^ n) (deriv harmonicF w) := by
  have h := scalarDerivSeries_hasFPowerSeriesOnBall harmonicF_hasFPowerSeriesOnBall
  have hs := h.hasSum (y := w) (by simp)
  have hfun : (fun n : ℕ => scalarDerivSeries harmonicFPowerSeries n (fun _ => w)) =
      (fun n : ℕ => harmonicFFirstCoefficient n * w ^ n) := by
    funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, scalarDerivSeries_coeff]
    simp [harmonicFPowerSeries, FormalMultilinearSeries.coeff_ofScalars,
      harmonicFFirstCoefficient, FFirstCoefficient, smul_eq_mul,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hfun, zero_add] at hs
  exact hs

theorem harmonicF_secondDerivative_hasSum (w : ℂ) :
    HasSum (fun n : ℕ => harmonicFSecondCoefficient n * w ^ n)
      (deriv (deriv harmonicF) w) := by
  have h := scalarDerivSeries_hasFPowerSeriesOnBall
    (scalarDerivSeries_hasFPowerSeriesOnBall harmonicF_hasFPowerSeriesOnBall)
  have hs := h.hasSum (y := w) (by simp)
  have hfun :
      (fun n : ℕ => scalarDerivSeries (scalarDerivSeries harmonicFPowerSeries) n (fun _ => w)) =
      (fun n : ℕ => harmonicFSecondCoefficient n * w ^ n) := by
    funext n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      scalarDerivSeries_coeff, scalarDerivSeries_coeff]
    simp [harmonicFPowerSeries, FormalMultilinearSeries.coeff_ofScalars,
      harmonicFSecondCoefficient, FSecondCoefficient, smul_eq_mul,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Nat.add_assoc]
  rw [hfun, zero_add] at hs
  exact hs

/-- The exact source term is F′, including at the endpoint w = 0. -/
theorem harmonicF_ode (w : ℂ) :
    w * deriv (deriv harmonicF) w + deriv harmonicF w = harmonicF w + deriv F w := by
  have hfirst := harmonicF_firstDerivative_hasSum w
  have hsecond := harmonicF_secondDerivative_hasSum w
  have hfirstSplit := hfirst.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, mul_one,
    harmonicFFirstCoefficient_zero] at hfirstSplit
  rw [hfirst.tsum_eq] at hfirstSplit
  have htailEq :
      (∑' n : ℕ, harmonicFFirstCoefficient (n + 1) * w ^ (n + 1)) =
        deriv harmonicF w - 1 := by
    linear_combination hfirstSplit
  have htailSummable :
      Summable (fun n : ℕ => harmonicFFirstCoefficient (n + 1) * w ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hfirst.summable
  have htail : HasSum (fun n : ℕ => harmonicFFirstCoefficient (n + 1) * w ^ (n + 1))
      (deriv harmonicF w - 1) := by
    rw [← htailEq]
    exact htailSummable.hasSum
  have hcombined := (hsecond.mul_left w).add htail
  have hfun :
      (fun n : ℕ => w * (harmonicFSecondCoefficient n * w ^ n) +
        harmonicFFirstCoefficient (n + 1) * w ^ (n + 1)) =
      (fun n : ℕ => (harmonic (n + 1) : ℂ) * fTerm w (n + 1) +
        FFirstCoefficient (n + 1) * w ^ (n + 1)) := by
    funext n
    calc
      w * (harmonicFSecondCoefficient n * w ^ n) +
          harmonicFFirstCoefficient (n + 1) * w ^ (n + 1) =
          (harmonicFSecondCoefficient n + harmonicFFirstCoefficient (n + 1)) *
            w ^ (n + 1) := by rw [pow_succ]; ring
      _ = _ := by
        rw [harmonicF_ode_coefficient]
        simp only [fTerm]
        ring
  rw [hfun] at hcombined
  have hH := harmonic_fTerm_summable w
  have hHSplit := hH.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, harmonic_zero, Rat.cast_zero, zero_mul, zero_add] at hHSplit
  change (∑' n : ℕ, (harmonic (n + 1) : ℂ) * fTerm w (n + 1)) = harmonicF w at hHSplit
  have hHtail : HasSum (fun n : ℕ => (harmonic (n + 1) : ℂ) * fTerm w (n + 1))
      (harmonicF w) := by
    rw [← hHSplit]
    exact ((summable_nat_add_iff 1).mpr hH).hasSum
  have hF := F_firstDerivative_hasSum w
  have hFSplit := hF.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, FFirstCoefficient_zero, pow_zero, mul_one] at hFSplit
  rw [hF.tsum_eq] at hFSplit
  have hFtailEq : (∑' n : ℕ, FFirstCoefficient (n + 1) * w ^ (n + 1)) =
      deriv F w - 1 := by linear_combination hFSplit
  have hFtail : HasSum (fun n : ℕ => FFirstCoefficient (n + 1) * w ^ (n + 1))
      (deriv F w - 1) := by
    rw [← hFtailEq]
    exact ((summable_nat_add_iff 1).mpr hF.summable).hasSum
  have he := hcombined.unique (hHtail.add hFtail)
  linear_combination he

end J0RadialUniqueness
