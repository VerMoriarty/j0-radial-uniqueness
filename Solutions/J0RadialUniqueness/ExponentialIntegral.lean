import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! The exponential integral and its constant at the logarithmic singularity.

The constant is identified from the actual Gamma integral and Gamma'(1), rather
than assumed as a standard E1 asymptotic formula. Integrability is proved separately
from every use of a total Bochner integral.
-/

noncomputable section

open MeasureTheory Filter Set Asymptotics
open scoped Topology

namespace J0RadialUniqueness

def E1 (x : ℝ) : ℝ := ∫ t : ℝ in Ioi x, Real.exp (-t) / t

def expLogDensity (t : ℝ) : ℝ := Real.exp (-t) * Real.log t

/-- The E1 integral is absolutely convergent at every positive lower endpoint. -/
theorem E1_integrableOn {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi x) := by
  have hm : ContinuousOn (fun t : ℝ => Real.exp (-t) / t) (Ioi x) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      (fun t ht => (lt_trans hx ht).ne')
  apply ((integrableOn_exp_neg_Ioi x).div_const x).mono'
    (hm.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := lt_trans hx ht
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le htpos.le)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx ht.le

/-- The log-weighted Gamma integrand is genuinely integrable.
This uses the convergence component of Mellin differentiation, not just its
formula for the value of a possibly undefined integral. -/
theorem expLogDensity_integrableOn : IntegrableOn expLogDensity (Ioi (0 : ℝ)) := by
  have hfc : LocallyIntegrableOn (fun t : ℝ => (Real.exp (-t) : ℂ)) (Ioi 0) := by
    refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  have htop : (fun t : ℝ => (Real.exp (-t) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.rpow t (-2)) := by
    rw [← isBigO_norm_left]
    simp_rw [Complex.norm_real, isBigO_norm_left]
    simpa only [Real.rpow_eq_pow, neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop (a := (1 : ℝ)) zero_lt_one (-2)).isBigO
  have hbot : (fun t : ℝ => (Real.exp (-t) : ℂ)) =O[𝓝[>] 0]
      (fun t : ℝ => Real.rpow t (-0)) := by
    simp only [neg_zero, Real.rpow_eq_pow, Real.rpow_zero]
    apply isBigO_const_of_tendsto
      (?_ : Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ)) (𝓝[>] 0) (𝓝 (1 : ℂ)))
      (one_ne_zero : (1 : ℝ) ≠ 0)
    simpa only [Function.comp_def, neg_zero, Real.exp_zero, Complex.ofReal_one] using
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).tendsto
        (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hm := (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) (a := 2) (b := 0)
    (s := (1 : ℂ)) hfc htop (by norm_num) hbot (by norm_num)).1
  have hc : IntegrableOn (fun t : ℝ => (expLogDensity t : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul,
      Complex.real_smul, ← Complex.ofReal_mul, expLogDensity, mul_comm] using hm
  exact hc.re

/-- GammaIntegral'(1) is the real log integral, embedded into the complex numbers. -/
theorem GammaIntegral_hasDerivAt_one_expLogDensity :
    HasDerivAt Complex.GammaIntegral
      ((∫ t : ℝ in Ioi 0, expLogDensity t : ℝ) : ℂ) 1 := by
  have h := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  simpa only [sub_self, Complex.cpow_zero, one_mul, ← integral_complex_ofReal,
    expLogDensity, Complex.ofReal_mul, mul_comm] using h

/-- The actual log-weighted integral equals minus the Euler--Mascheroni constant. -/
theorem expLogDensity_integral :
    (∫ t : ℝ in Ioi 0, expLogDensity t) = -Real.eulerMascheroniConstant := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_Ioi.preimage Complex.continuous_re
  have heq : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    filter_upwards [hU.mem_nhds (show (1 : ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num)] with s hs
    exact Complex.Gamma_eq_integral hs
  have hGamma := GammaIntegral_hasDerivAt_one_expLogDensity.congr_of_eventuallyEq heq
  have h := hGamma.unique Complex.hasDerivAt_Gamma_one
  exact_mod_cast h

theorem expLogDensity_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt expLogDensity
      (-expLogDensity t + Real.exp (-t) / t) t := by
  have h := (((hasDerivAt_id t).neg).exp).mul (Real.hasDerivAt_log ht.ne')
  convert! h using 1 <;> simp only [expLogDensity, div_eq_mul_inv, Pi.mul_apply,
    Pi.neg_apply, id_eq, mul_neg, mul_one, neg_mul]

/-- The boundary term at infinity needed for the integration by parts. -/
theorem expLogDensity_tendsto_zero_atTop :
    Tendsto expLogDensity atTop (𝓝 (0 : ℝ)) := by
  have hmajor : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_one, neg_one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 1 zero_lt_one
  apply squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.log_nonneg ht)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hlog : Real.log t ≤ t := (Real.log_le_sub_one_of_pos htpos).trans (by linarith)
    calc
      expLogDensity t ≤ Real.exp (-t) * t :=
        mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
      _ = t * Real.exp (-t) := mul_comm _ _

/-- Integration by parts, with both improper-integral boundary terms established. -/
theorem E1_add_log_identity {x : ℝ} (hx : 0 < x) :
    E1 x + Real.log x =
      (∫ t : ℝ in Ioi x, expLogDensity t) +
        (1 - Real.exp (-x)) * Real.log x := by
  have hlogint : IntegrableOn expLogDensity (Ioi x) :=
    expLogDensity_integrableOn.mono_set (Ioi_subset_Ioi hx.le)
  have hE1int := E1_integrableOn hx
  have hderivint : IntegrableOn
      (fun t : ℝ => -expLogDensity t + Real.exp (-t) / t) (Ioi x) :=
    hlogint.neg.add hE1int
  have hcont : ContinuousWithinAt expLogDensity (Ici x) x :=
    ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      (Real.continuousAt_log hx.ne')).continuousWithinAt
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t ht => expLogDensity_hasDerivAt (lt_trans hx ht)) hderivint
    expLogDensity_tendsto_zero_atTop
  change (∫ t : ℝ in Ioi x, -expLogDensity t + Real.exp (-t) / t) =
    0 - expLogDensity x at hftc
  have hnegint : IntegrableOn (fun t => -expLogDensity t) (Ioi x) := hlogint.neg
  have hneg : (∫ t : ℝ in Ioi x, -expLogDensity t) =
      -(∫ t : ℝ in Ioi x, expLogDensity t) := integral_neg _
  rw [integral_add hnegint hE1int, hneg, zero_sub] at hftc
  change -(∫ t : ℝ in Ioi x, expLogDensity t) + E1 x =
    -(Real.exp (-x) * Real.log x) at hftc
  linear_combination hftc

/-- The small-endpoint boundary term vanishes by differentiability and x log x -> 0. -/
theorem E1_boundary_term_tendsto_zero :
    Tendsto (fun x : ℝ => (1 - Real.exp (-x)) * Real.log x)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
    simpa only [Pi.neg_apply, id_eq, neg_zero, Real.exp_zero, mul_neg,
      mul_one, neg_neg] using (((hasDerivAt_id (0 : ℝ)).neg).exp.const_sub (1 : ℝ))
  have hquot : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / x)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa only [zero_add, neg_zero, Real.exp_zero, sub_self, sub_zero,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have hxlog : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [Real.rpow_one, mul_comm] using
      tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one
  have hprod : Tendsto
      (fun x : ℝ => ((1 - Real.exp (-x)) / x) * (x * Real.log x))
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using hquot.mul hxlog
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  field_simp [ne_of_gt (show 0 < x from hx)] <;> ring

/-- The E1 logarithmic constant, proved from the actual Gamma derivative at one. -/
theorem E1_add_log_tendsto_neg_eulerMascheroni :
    Tendsto (fun x : ℝ => E1 x + Real.log x)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hI : Tendsto (fun x : ℝ => ∫ t : ℝ in Ioi x, expLogDensity t)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h := expLogDensity_integrableOn.continuousWithinAt_Ici_primitive_Ioi
    have h' := h.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from Ioi_subset_Ici_self)
    simpa only [expLogDensity_integral] using h'.tendsto
  have hsum := hI.add E1_boundary_term_tendsto_zero
  have hcongr : (fun x : ℝ => (∫ t : ℝ in Ioi x, expLogDensity t) +
      (1 - Real.exp (-x)) * Real.log x) =ᶠ[𝓝[>] 0]
      (fun x : ℝ => E1 x + Real.log x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (E1_add_log_identity hx).symm
  simpa only [add_zero] using hsum.congr' hcongr

end J0RadialUniqueness
