import Solutions.J0RadialUniqueness.MeanDefectSpectrum
import Solutions.J0RadialUniqueness.SimpleOnePoints
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Actual entire division by a function with simple zeros. At a zero the
quotient is defined by the derivative ratio, and its analyticity is proved by
the two genuine `dslope` functions. No growth or support assertion is included.
-/

noncomputable section

open Filter
open scoped Topology

namespace J0RadialUniqueness

/-- Division with the removable values at the simple zeros filled explicitly. -/
def simpleZeroQuotient (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if g z = 0 then deriv f z / deriv g z else f z / g z

/-- The analytic divided difference at its base point follows from the actual
shifted power series, including its value at that base point. -/
theorem analyticAt_dslope_base {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- Near a common zero where the denominator has nonzero derivative, the
filled quotient agrees with the quotient of the actual divided differences. -/
theorem simpleZeroQuotient_eventuallyEq_dslope {f g : ℂ → ℂ} {a : ℂ}
    (hg : AnalyticAt ℂ g a) (hfa : f a = 0) (hga : g a = 0)
    (hderiv : deriv g a ≠ 0) :
    simpleZeroQuotient f g =ᶠ[𝓝 a] fun z => dslope f a z / dslope g a z := by
  have hgds : AnalyticAt ℂ (dslope g a) a := analyticAt_dslope_base hg
  have hnonzero : ∀ᶠ z in 𝓝 a, dslope g a z ≠ 0 :=
    hgds.continuousAt.eventually_ne (by simpa only [dslope_same] using hderiv)
  filter_upwards [hnonzero] with z hzds
  by_cases hza : z = a
  · subst z
    simp only [simpleZeroQuotient, hga, if_pos, dslope_same]
  · have hgfactor : (z - a) * dslope g a z = g z := by
      simpa only [smul_eq_mul] using sub_smul_dslope_of_zero hga z
    have hffactor : (z - a) * dslope f a z = f z := by
      simpa only [smul_eq_mul] using sub_smul_dslope_of_zero hfa z
    have hgz : g z ≠ 0 := by
      rw [← hgfactor]
      exact mul_ne_zero (sub_ne_zero.mpr hza) hzds
    rw [simpleZeroQuotient, if_neg hgz]
    apply (div_eq_div_iff hgz hzds).mpr
    rw [← hffactor, ← hgfactor]
    ring

/-- A local version of simple-zero division, with all local analytic hypotheses
and both vanishing conditions explicit. -/
theorem simpleZeroQuotient_analyticAt_zero {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hfa : f a = 0) (hga : g a = 0) (hderiv : deriv g a ≠ 0) :
    AnalyticAt ℂ (simpleZeroQuotient f g) a := by
  have hq := (analyticAt_dslope_base hf).div (analyticAt_dslope_base hg)
    (by simpa only [dslope_same] using hderiv)
  exact hq.congr (simpleZeroQuotient_eventuallyEq_dslope hg hfa hga hderiv).symm

/-- The quotient is analytic at ordinary nonzero denominator points as well. -/
theorem simpleZeroQuotient_analyticAt_nonzero {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0) :
    AnalyticAt ℂ (simpleZeroQuotient f g) a := by
  apply (hf.div hg hga).congr
  filter_upwards [hg.continuousAt.eventually_ne hga] with z hz
  simp only [simpleZeroQuotient, if_neg hz, Pi.div_apply]

/-- Every zero of the denominator is removable under the simple-zero and
vanishing hypotheses, so the explicitly filled quotient is entire. -/
theorem simpleZeroQuotient_analyticAt {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hvanish : ∀ z : ℂ, g z = 0 → f z = 0)
    (hsimple : ∀ z : ℂ, g z = 0 → deriv g z ≠ 0) (a : ℂ) :
    AnalyticAt ℂ (simpleZeroQuotient f g) a := by
  have hfa : AnalyticAt ℂ f a :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ) a (Set.mem_univ a)
  have hga : AnalyticAt ℂ g a :=
    (hg.differentiableOn.analyticOnNhd isOpen_univ) a (Set.mem_univ a)
  by_cases hzero : g a = 0
  · exact simpleZeroQuotient_analyticAt_zero hfa hga (hvanish a hzero) hzero (hsimple a hzero)
  · exact simpleZeroQuotient_analyticAt_nonzero hfa hga hzero

theorem simpleZeroQuotient_differentiable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hvanish : ∀ z : ℂ, g z = 0 → f z = 0)
    (hsimple : ∀ z : ℂ, g z = 0 → deriv g z ≠ 0) :
    Differentiable ℂ (simpleZeroQuotient f g) :=
  fun a => (simpleZeroQuotient_analyticAt hf hg hvanish hsimple a).differentiableAt

/-- The entire quotient satisfies the desired product identity at every point,
including the zero set of the denominator. -/
theorem simpleZeroQuotient_factorization {f g : ℂ → ℂ}
    (hvanish : ∀ z : ℂ, g z = 0 → f z = 0) (z : ℂ) :
    f z = g z * simpleZeroQuotient f g z := by
  by_cases hz : g z = 0
  · simp only [hvanish z hz, hz, zero_mul]
  · rw [simpleZeroQuotient, if_neg hz]
    field_simp [hz]

/-- A conventional existential entire-division interface, proved using the
explicit quotient above. -/
theorem exists_entire_quotient_of_simple_zeros {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hvanish : ∀ z : ℂ, g z = 0 → f z = 0)
    (hsimple : ∀ z : ℂ, g z = 0 → deriv g z ≠ 0) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z : ℂ, f z = g z * q z :=
  ⟨simpleZeroQuotient f g, simpleZeroQuotient_differentiable hf hg hvanish hsimple,
    simpleZeroQuotient_factorization hvanish⟩

/-- Differentiating the exact quadratic factorization at a multiplier zero. -/
theorem meanDefectMultiplier_deriv_at_root_factor (r : ℝ) {ζ : ℂ}
    (hroot : meanDefectMultiplier r ζ = 0) :
    ζ ^ 2 * deriv (meanDefectMultiplier r) ζ =
      (r : ℂ) * deriv J0 ((r : ℂ) * ζ) := by
  have harg : HasDerivAt (fun w : ℂ => (r : ℂ) * w) (r : ℂ) ζ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id ζ).const_mul (r : ℂ)
  have hleft : HasDerivAt (fun w : ℂ => J0 ((r : ℂ) * w) - 1)
      (deriv J0 ((r : ℂ) * ζ) * (r : ℂ)) ζ := by
    simpa only [Function.comp_def] using
      (((J0_differentiable ((r : ℂ) * ζ)).hasDerivAt.comp ζ harg).sub_const 1)
  have hm := (meanDefectMultiplier_analyticAt r ζ).differentiableAt.hasDerivAt
  have hright : HasDerivAt (fun w : ℂ => w ^ 2 * meanDefectMultiplier r w)
      (ζ ^ 2 * deriv (meanDefectMultiplier r) ζ) ζ := by
    convert! ((hasDerivAt_id ζ).pow 2).mul hm using 1 <;>
      simp only [id_eq, Pi.pow_apply, hroot, mul_zero, zero_add]
  have hfun : (fun w : ℂ => w ^ 2 * meanDefectMultiplier r w) =
      (fun w : ℂ => J0 ((r : ℂ) * w) - 1) := by
    funext w
    exact (J0_sub_one_eq_sq_mul_meanDefectMultiplier r w).symm
  rw [hfun] at hright
  simpa only [mul_comm] using hright.unique hleft

/-- Every zero of the actual normalized mean-defect multiplier is simple for
a positive radius. Its nonzero value at the origin is treated explicitly. -/
theorem meanDefectMultiplier_deriv_ne_zero_at_root {r : ℝ} (hr : 0 < r) {ζ : ℂ}
    (hroot : meanDefectMultiplier r ζ = 0) : deriv (meanDefectMultiplier r) ζ ≠ 0 := by
  have hζ : ζ ≠ 0 := by
    intro hzero
    subst ζ
    exact meanDefectMultiplier_zero_ne_zero_of_pos r hr hroot
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hJ := (meanDefectMultiplier_eq_zero_iff r ζ hζ).mp hroot
  have hJprime := J0_deriv_ne_zero_at_one_point (mul_ne_zero hrC hζ) hJ
  intro hzero
  have hfactor := meanDefectMultiplier_deriv_at_root_factor r hroot
  rw [hzero, mul_zero] at hfactor
  exact mul_ne_zero hrC hJprime hfactor.symm

end J0RadialUniqueness
