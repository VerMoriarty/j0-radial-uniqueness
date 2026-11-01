import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Algebraic and holomorphic ingredients of the planar Chebyshev--Abel inversion
kernel. The Chebyshev polynomials below are Mathlib's actual polynomials. The
reciprocal-root identity is proved by their defining recurrence, and the
Möbius mean is proved by complex differentiability on the closed unit disk.

This module does not yet assert the improper Abel kernel integral: the real
change of variables and its endpoint integrability are separate obligations.
-/

noncomputable section

open Complex MeasureTheory Set Polynomial
open scoped Topology Interval ComplexConjugate

namespace J0RadialUniqueness

def chebyshevTValue (m : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x

/-- The reciprocal-root formula, with no analytic choice of a square root. -/
theorem two_mul_chebyshev_eval_of_reciprocal_roots
    {K : Type*} [CommRing K] (m : ℕ) (x z w : K)
    (hsum : z + w = 2 * x) (hprod : z * w = 1) :
    2 * (Polynomial.Chebyshev.T K (m : ℤ)).eval x = z ^ m + w ^ m := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [Nat.cast_zero, Polynomial.Chebyshev.T_zero,
      Polynomial.eval_one, pow_zero, mul_one]; ring
  | one => simpa only [Nat.cast_one, Polynomial.Chebyshev.T_one,
      Polynomial.eval_X, pow_one] using hsum.symm
  | more n hn hn1 =>
    have hT : Polynomial.Chebyshev.T K ((n + 2 : ℕ) : ℤ) =
        2 * X * Polynomial.Chebyshev.T K ((n + 1 : ℕ) : ℤ) -
          Polynomial.Chebyshev.T K (n : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        Polynomial.Chebyshev.T_add_two K (n : ℤ)
    have hrec : z ^ (n + 2) + w ^ (n + 2) =
        (z + w) * (z ^ (n + 1) + w ^ (n + 1)) -
          (z * w) * (z ^ n + w ^ n) := by
      simp only [pow_succ]
      ring
    rw [hsum, hprod, one_mul] at hrec
    calc
      2 * (Polynomial.Chebyshev.T K ((n + 2 : ℕ) : ℤ)).eval x =
          (2 * x) * (2 * (Polynomial.Chebyshev.T K ((n + 1 : ℕ) : ℤ)).eval x) -
            2 * (Polynomial.Chebyshev.T K (n : ℤ)).eval x := by
        rw [hT]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X]
        ring
      _ = (2 * x) * (z ^ (n + 1) + w ^ (n + 1)) - (z ^ n + w ^ n) := by
        rw [hn1, hn]
      _ = z ^ (n + 2) + w ^ (n + 2) := hrec.symm

/-- A unit complex number supplies the usual real Chebyshev evaluation, without
introducing an argument function or an inverse cosine. -/
theorem chebyshevTValue_re_of_mul_conj_eq_one (m : ℕ) (z : ℂ)
    (hz : z * conj z = 1) : chebyshevTValue m z.re = (z ^ m).re := by
  have hsum : z + conj z = 2 * (z.re : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.add_conj z
  have hh := two_mul_chebyshev_eval_of_reciprocal_roots m (z.re : ℂ) z (conj z) hsum hz
  rw [← Polynomial.Chebyshev.complex_ofReal_eval_T] at hh
  have hconj : (conj z) ^ m = conj (z ^ m) := (map_pow (starRingEnd ℂ) z m).symm
  rw [hconj] at hh
  have hre := congrArg Complex.re hh
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.add_re, Complex.conj_re] at hre
  dsimp only [chebyshevTValue]
  linarith

theorem chebyshevTValue_re_of_norm_eq_one (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    chebyshevTValue m z.re = (z ^ m).re := by
  apply chebyshevTValue_re_of_mul_conj_eq_one
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- The exact product identity used in the Abel kernel after the angular
substitution. The assumptions encode two Pythagorean identities and retain
the actual values of both Chebyshev factors. -/
theorem chebyshevTValue_product_rational_powers (m : ℕ)
    (a b c d s : ℝ) (hs : s ≠ 0)
    (hac : a ^ 2 + c ^ 2 = s ^ 2) (hbd : b ^ 2 - d ^ 2 = s ^ 2) :
    2 * chebyshevTValue m (a / s) * chebyshevTValue m (b / s) =
      ((((a : ℂ) + (c : ℂ) * I) / ((b - d : ℝ) : ℂ)) ^ m).re +
      ((((a : ℂ) + (c : ℂ) * I) / ((b + d : ℝ) : ℂ)) ^ m).re := by
  let z : ℂ := ((a : ℂ) + (c : ℂ) * I) / (s : ℂ)
  let wp : ℝ := (b + d) / s
  let wm : ℝ := (b - d) / s
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hbp : b + d ≠ 0 := by
    intro h
    have hpos := sq_pos_of_ne_zero hs
    have hb : b = -d := by linarith
    rw [hb] at hbd
    nlinarith only [hbd, hpos]
  have hbm : b - d ≠ 0 := by
    intro h
    have hpos := sq_pos_of_ne_zero hs
    have hb : b = d := by linarith
    rw [hb] at hbd
    nlinarith only [hbd, hpos]
  have hbpC : (b : ℂ) + (d : ℂ) ≠ 0 := by exact_mod_cast hbp
  have hbmC : (b : ℂ) - (d : ℂ) ≠ 0 := by exact_mod_cast hbm
  have hnormNum : Complex.normSq ((a : ℂ) + (c : ℂ) * I) = s ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, add_zero, zero_add, sub_zero]
    nlinarith only [hac]
  have hnormz : Complex.normSq z = 1 := by
    dsimp only [z]
    rw [Complex.normSq_div, hnormNum, Complex.normSq_ofReal]
    field_simp [hs]
  have hunit : z * conj z = 1 := by rw [Complex.mul_conj, hnormz, Complex.ofReal_one]
  have hzre : z.re = a / s := by simp [z]
  have hTa : chebyshevTValue m (a / s) = (z ^ m).re := by
    rw [← hzre]
    exact chebyshevTValue_re_of_mul_conj_eq_one m z hunit
  have hsum : wp + wm = 2 * (b / s) := by dsimp [wp, wm]; ring
  have hprod : wp * wm = 1 := by
    dsimp only [wp, wm]
    field_simp [hs]
    nlinarith only [hbd]
  have hTb : 2 * chebyshevTValue m (b / s) = wp ^ m + wm ^ m :=
    two_mul_chebyshev_eval_of_reciprocal_roots m (b / s) wp wm hsum hprod
  have hbdC : (b : ℂ) ^ 2 - (d : ℂ) ^ 2 = (s : ℂ) ^ 2 := by exact_mod_cast hbd
  have hzp : z * (wp : ℂ) = ((a : ℂ) + (c : ℂ) * I) / ((b - d : ℝ) : ℂ) := by
    dsimp only [z, wp]
    push_cast
    field_simp [hsC, hbmC]
    linear_combination ((a : ℂ) + (c : ℂ) * I) * hbdC
  have hzm : z * (wm : ℂ) = ((a : ℂ) + (c : ℂ) * I) / ((b + d : ℝ) : ℂ) := by
    dsimp only [z, wm]
    push_cast
    field_simp [hsC, hbpC]
    linear_combination ((a : ℂ) + (c : ℂ) * I) * hbdC
  calc
    2 * chebyshevTValue m (a / s) * chebyshevTValue m (b / s) =
        (z ^ m).re * (wp ^ m + wm ^ m) := by rw [hTa, ← hTb]; ring
    _ = ((z * (wp : ℂ)) ^ m).re + ((z * (wm : ℂ)) ^ m).re := by
      simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    _ = _ := by rw [hzp, hzm]

def chebyshevAngleRadius (a d θ : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + d ^ 2 * Real.sin θ ^ 2)

theorem chebyshevAngleRadius_pos {a : ℝ} (ha : 0 < a) (d θ : ℝ) :
    0 < chebyshevAngleRadius a d θ := by
  apply Real.sqrt_pos.mpr
  have h₁ : 0 < a ^ 2 := sq_pos_of_pos ha
  have h₂ : 0 ≤ d ^ 2 * Real.sin θ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-- The actual angular Chebyshev product, valid at every real angle. The two
terms correspond to angles θ and π−θ in the Möbius representation. -/
theorem chebyshevTValue_product_angle (m : ℕ) (a b d θ : ℝ)
    (ha : 0 < a) (hd : d ^ 2 = b ^ 2 - a ^ 2) :
    2 * chebyshevTValue m (a / chebyshevAngleRadius a d θ) *
        chebyshevTValue m (b / chebyshevAngleRadius a d θ) =
      ((((a : ℂ) + ((d * Real.sin θ : ℝ) : ℂ) * I) /
        ((b - d * Real.cos θ : ℝ) : ℂ)) ^ m).re +
      ((((a : ℂ) + ((d * Real.sin θ : ℝ) : ℂ) * I) /
        ((b + d * Real.cos θ : ℝ) : ℂ)) ^ m).re := by
  have hs : chebyshevAngleRadius a d θ ≠ 0 := (chebyshevAngleRadius_pos ha d θ).ne'
  have hrad : (chebyshevAngleRadius a d θ) ^ 2 = a ^ 2 + d ^ 2 * Real.sin θ ^ 2 := by
    apply Real.sq_sqrt
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hac : a ^ 2 + (d * Real.sin θ) ^ 2 = (chebyshevAngleRadius a d θ) ^ 2 := by
    rw [hrad]
    ring
  have htrig := congrArg (fun t : ℝ => d ^ 2 * t) (Real.sin_sq_add_cos_sq θ)
  have hbd : b ^ 2 - (d * Real.cos θ) ^ 2 = (chebyshevAngleRadius a d θ) ^ 2 := by
    rw [hrad]
    nlinarith only [hd, htrig]
  exact chebyshevTValue_product_rational_powers m a b (d * Real.sin θ)
    (d * Real.cos θ) (chebyshevAngleRadius a d θ) hs hac hbd

def chebyshevMobius (q : ℝ) (z : ℂ) : ℂ := (1 + (q : ℂ) * z) / (1 - (q : ℂ) * z)

theorem chebyshevMobius_den_ne_zero {q : ℝ} (hq : |q| < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : 1 - (q : ℂ) * z ≠ 0 := by
  intro h
  have heq : (q : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
  have hlt : ‖(q : ℂ) * z‖ < 1 := by
    calc
      ‖(q : ℂ) * z‖ = |q| * ‖z‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |q| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg q)
      _ < 1 := by simpa only [mul_one] using hq
  rw [heq, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- The actual rational parametrization of the Möbius image of a unit circle.
The two scalar equations are the elementary algebra of q=d/(a+b). -/
theorem chebyshevMobius_exp_eq_rational
    (q a b d θ : ℝ) (hq : |q| < 1)
    (hqa : q * (b + a) = d) (hqd : q * d = b - a)
    (hden : b - d * Real.cos θ ≠ 0) :
    chebyshevMobius q (Complex.exp ((θ : ℂ) * I)) =
      ((a : ℂ) + ((d * Real.sin θ : ℝ) : ℂ) * I) /
        ((b - d * Real.cos θ : ℝ) : ℂ) := by
  have hdenC : ((b - d * Real.cos θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden
  have hdenM := chebyshevMobius_den_ne_zero hq
    (show ‖Complex.exp ((θ : ℂ) * I)‖ ≤ 1 by rw [Complex.norm_exp_ofReal_mul_I])
  unfold chebyshevMobius
  apply (div_eq_div_iff hdenM hdenC).mpr
  have htrig := congrArg (fun t : ℝ => q * d * t) (Real.sin_sq_add_cos_sq θ)
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero, sub_zero]
  · linear_combination (Real.cos θ) * hqa - hqd - htrig
  · linear_combination (Real.sin θ) * hqa

theorem chebyshevAbel_parameter_bounds (a b d : ℝ) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 - a ^ 2) :
    0 < d / (b + a) ∧ d / (b + a) < 1 := by
  have hba : 0 < b + a := by linarith
  have hprod : 0 < 2 * a * (b + a) := by positivity
  have hsq : d ^ 2 < (b + a) ^ 2 := by nlinarith only [hd2, hprod]
  have hdlt : d < b + a := (sq_lt_sq₀ hd.le hba.le).mp hsq
  exact ⟨div_pos hd hba, (div_lt_one hba).mpr hdlt⟩

/-- The Chebyshev product expressed in the two genuine Möbius values at θ and
π−θ. This is the pointwise identity preceding the quarter-circle integral. -/
theorem chebyshevTValue_product_angle_mobius (m : ℕ) (a b d θ : ℝ)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 - a ^ 2) :
    2 * chebyshevTValue m (a / chebyshevAngleRadius a d θ) *
        chebyshevTValue m (b / chebyshevAngleRadius a d θ) =
      (chebyshevMobius (d / (b + a)) (Complex.exp ((θ : ℂ) * I)) ^ m).re +
      (chebyshevMobius (d / (b + a))
        (Complex.exp (((Real.pi - θ : ℝ) : ℂ) * I)) ^ m).re := by
  let q : ℝ := d / (b + a)
  have hba : b + a ≠ 0 := by linarith
  have hqbounds := chebyshevAbel_parameter_bounds a b d ha hab hd hd2
  have hq : |q| < 1 := by rw [abs_of_pos hqbounds.1]; exact hqbounds.2
  have hqa : q * (b + a) = d := by dsimp [q]; field_simp [hba]
  have hqd : q * d = b - a := by
    dsimp [q]
    field_simp [hba]
    nlinarith only [hd2]
  have hbd : d < b := by nlinarith [sq_pos_of_pos ha]
  have hden (t : ℝ) : b - d * Real.cos t ≠ 0 := by
    have hc : d * Real.cos t ≤ d := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.cos_le_one t) hd.le
    linarith
  rw [chebyshevMobius_exp_eq_rational q a b d θ hq hqa hqd (hden θ),
    chebyshevMobius_exp_eq_rational q a b d (Real.pi - θ) hq hqa hqd (hden _),
    Real.sin_pi_sub, Real.cos_pi_sub]
  simpa only [mul_neg, sub_neg_eq_add] using
    chebyshevTValue_product_angle m a b d θ ha hd2

theorem chebyshevMobius_pow_differentiableOn_closedBall (m : ℕ) {q : ℝ}
    (hq : |q| < 1) :
    DifferentiableOn ℂ (fun z => chebyshevMobius q z ^ m) (Metric.closedBall 0 1) := by
  intro z hz
  have hznorm : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hn : DifferentiableAt ℂ (fun w : ℂ => 1 + (q : ℂ) * w) z := by fun_prop
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - (q : ℂ) * w) z := by fun_prop
  exact ((hn.div hd (chebyshevMobius_den_ne_zero hq hznorm)).pow m).differentiableWithinAt

/-- The holomorphic mean underlying the angular kernel identity. -/
theorem circleAverage_chebyshevMobius_pow (m : ℕ) {q : ℝ} (hq : |q| < 1) :
    Real.circleAverage (fun z => chebyshevMobius q z ^ m) 0 1 = 1 := by
  have hd := chebyshevMobius_pow_differentiableOn_closedBall m hq
  have hdc : DiffContOnCl ℂ (fun z => chebyshevMobius q z ^ m)
      (Metric.ball 0 |(1 : ℝ)|) := by
    apply DifferentiableOn.diffContOnCl
    simpa only [abs_one, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hd
  simpa only [chebyshevMobius, mul_zero, add_zero, sub_zero, div_one, one_pow] using hdc.circleAverage

theorem integral_chebyshevMobius_pow_exp (m : ℕ) {q : ℝ} (hq : |q| < 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      chebyshevMobius q (Complex.exp ((θ : ℂ) * I)) ^ m) = (2 * Real.pi : ℝ) := by
  have havg := circleAverage_chebyshevMobius_pow m hq
  rw [Real.circleAverage_def] at havg
  have hh := congrArg (fun w : ℂ => (2 * Real.pi : ℝ) • w) havg
  have hπ : 2 * Real.pi ≠ 0 := ne_of_gt Real.two_pi_pos
  have hπC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ
  simp only [Complex.real_smul] at hh
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hπC, one_mul, mul_one] at hh
  simpa only [circleMap, zero_add, Complex.ofReal_one, one_mul] using hh

end J0RadialUniqueness
