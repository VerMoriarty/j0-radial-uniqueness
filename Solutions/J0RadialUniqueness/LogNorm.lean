import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

theorem real_inner_div_norm_sq (a b : ℂ) :
    inner ℝ a b / ‖a‖ ^ 2 = (b / a).re := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.div_re]
  ring

/-- The real logarithmic modulus derivative needs nonvanishing, not a complex-log branch. -/
theorem hasDerivAt_log_norm {h : ℝ → ℂ} {h' : ℂ} {x : ℝ}
    (hd : HasDerivAt h h' x) (hn : h x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖h t‖) (h' / h x).re x := by
  have he : (fun t : ℝ => Real.log ‖h t‖) =
      (fun t : ℝ => (1 / 2 : ℝ) * Real.log (‖h t‖ ^ 2)) := by
    funext t
    rw [Real.log_pow]
    ring
  rw [he]
  have hn2 : ‖h x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  have hh := (hd.norm_sq.log hn2).const_mul (1 / 2 : ℝ)
  apply hh.congr_deriv
  rw [← real_inner_div_norm_sq]
  ring

theorem deriv_log_norm {h : ℝ → ℂ} {x : ℝ}
    (hd : DifferentiableAt ℝ h x) (hn : h x ≠ 0) :
    deriv (fun t : ℝ => Real.log ‖h t‖) x = (deriv h x / h x).re :=
  (hasDerivAt_log_norm hd.hasDerivAt hn).deriv

end J0RadialUniqueness
