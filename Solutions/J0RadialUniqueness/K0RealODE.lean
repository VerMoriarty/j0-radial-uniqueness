import Solutions.J0RadialUniqueness.K0ModifiedODE
import Solutions.J0RadialUniqueness.K0SeriesLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

noncomputable section
open Filter
open scoped Topology

namespace J0RadialUniqueness

def realI0 (x : ℝ) : ℝ := (modifiedI0 (x : ℂ)).re
def realI0Slope (x : ℝ) : ℝ := (deriv modifiedI0 (x : ℂ)).re
def realK0Series (x : ℝ) : ℝ := (K0Series (x : ℂ)).re
def realK0SeriesSlope (x : ℝ) : ℝ := (K0SeriesSlope (x : ℂ)).re

theorem F_ofReal_re_ge_one {u : ℝ} (hu : 0 ≤ u) : 1 ≤ (F (u : ℂ)).re := by
  have hs := Complex.hasSum_re (fTerm_summable (u : ℂ)).hasSum
  have hnonneg (n : ℕ) : 0 ≤ (fTerm (u : ℂ) n).re := by
    have he : fTerm (u : ℂ) n = ((u ^ n / (n.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by
      simp [fTerm]
    rw [he, Complex.ofReal_re]
    positivity
  have h := hs.summable.le_tsum 0 (fun n _ => hnonneg n)
  rw [hs.tsum_eq] at h
  convert! h using 1 <;> simp [F, fTerm]

theorem realI0_ge_one (x : ℝ) : 1 ≤ realI0 x := by
  have he : (x : ℂ) ^ 2 / 4 = ((x ^ 2 / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [realI0, modifiedI0, he]
  exact F_ofReal_re_ge_one (by positivity)

theorem realI0_ne_zero (x : ℝ) : realI0 x ≠ 0 := ne_of_gt (by linarith [realI0_ge_one x])

theorem realI0_hasDerivAt (x : ℝ) : HasDerivAt realI0 (realI0Slope x) x := by
  have h := ((modifiedI0_analyticAt (x : ℂ)).differentiableAt.hasDerivAt).real_of_complex
  exact h

theorem realI0Slope_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt realI0Slope (realI0 x - realI0Slope x / x) x := by
  have h := (modifiedI0_deriv_hasDerivAt (x : ℂ)).real_of_complex
  have ho := congrArg Complex.re (modifiedI0_ode (x : ℂ))
  have he : (quadraticAccel F (x : ℂ)).re = realI0 x - realI0Slope x / x := by
    simp only [modifiedBesselOperator, modifiedI0_secondDerivative, Complex.sub_re,
      Complex.add_re, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      add_zero, Complex.zero_re] at ho
    change x ^ 2 * (quadraticAccel F (x : ℂ)).re +
      x * realI0Slope x - x ^ 2 * realI0 x = 0 at ho
    apply (eq_sub_iff_add_eq).mpr
    apply (mul_left_cancel₀ (pow_ne_zero 2 hx.ne'))
    field_simp
    nlinarith
  rw [he] at h
  exact h

theorem realI0_tendsto_one : Tendsto realI0 (𝓝[>] 0) (𝓝 1) := by
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    ((modifiedI0_analyticAt 0).continuousAt.tendsto.comp hx)
  convert! h using 1 <;> simp [realI0, modifiedI0, F_zero]

theorem realK0Series_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt realK0Series (realK0SeriesSlope x) x :=
  (K0Series_hasDerivAt (Or.inl hx)).real_of_complex

theorem realK0SeriesSlope_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt realK0SeriesSlope (realK0Series x - realK0SeriesSlope x / x) x := by
  have hz : (x : ℂ) ∈ Complex.slitPlane := Or.inl hx
  have h := (K0SeriesSlope_hasDerivAt hz).real_of_complex
  have ho := congrArg Complex.re (K0Series_ode hz)
  have he : (K0SeriesAccel (x : ℂ)).re = realK0Series x - realK0SeriesSlope x / x := by
    simp only [modifiedBesselOperator, K0Series_secondDerivative hz, K0Series_deriv hz,
      Complex.sub_re, Complex.add_re, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero, Complex.zero_re] at ho
    change x ^ 2 * (K0SeriesAccel (x : ℂ)).re +
      x * realK0SeriesSlope x - x ^ 2 * realK0Series x = 0 at ho
    apply (eq_sub_iff_add_eq).mpr
    apply (mul_left_cancel₀ (pow_ne_zero 2 hx.ne'))
    field_simp
    nlinarith
  rw [he] at h
  exact h

theorem realK0Series_log_limit :
    Tendsto (fun x : ℝ => realK0Series x + Real.log (x / 2))
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
  simpa only [Function.comp_def, Complex.add_re, Complex.ofReal_re, Complex.neg_re,
    realK0Series] using Complex.continuous_re.continuousAt.tendsto.comp
      K0Series_positive_real_limit

end J0RadialUniqueness
