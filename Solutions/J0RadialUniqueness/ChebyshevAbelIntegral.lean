import Solutions.J0RadialUniqueness.ChebyshevAbelKernel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
The actual planar Chebyshev--Abel composite integral. Its endpoint singularities
are handled by the one-dimensional Jacobian theorem on the open angular
interval. Integrability is obtained from the continuous angular pullback.
-/

noncomputable section

open Complex MeasureTheory Set Polynomial
open scoped Topology Interval ComplexConjugate

namespace J0RadialUniqueness

def chebyshevMobiusRealPower (m : ℕ) (q θ : ℝ) : ℝ :=
  (chebyshevMobius q (Complex.exp ((θ : ℂ) * I)) ^ m).re

theorem continuous_chebyshevMobius_power_exp (m : ℕ) {q : ℝ} (hq : |q| < 1) :
    Continuous (fun θ : ℝ => chebyshevMobius q (Complex.exp ((θ : ℂ) * I)) ^ m) := by
  have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * I)) := by fun_prop
  have hn : Continuous (fun θ : ℝ => 1 + (q : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    continuous_const.add (continuous_const.mul he)
  have hd : Continuous (fun θ : ℝ => 1 - (q : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    continuous_const.sub (continuous_const.mul he)
  exact (hn.div hd (fun θ => chebyshevMobius_den_ne_zero hq
    (by rw [Complex.norm_exp_ofReal_mul_I]))).pow m

theorem continuous_chebyshevMobiusRealPower (m : ℕ) {q : ℝ} (hq : |q| < 1) :
    Continuous (chebyshevMobiusRealPower m q) :=
  Complex.continuous_re.comp (continuous_chebyshevMobius_power_exp m hq)

theorem chebyshevMobius_conj (q : ℝ) (z : ℂ) :
    chebyshevMobius q (conj z) = conj (chebyshevMobius q z) := by
  simp only [chebyshevMobius, map_div₀, map_add, map_sub, map_mul,
    map_one, Complex.conj_ofReal]

theorem chebyshevMobiusRealPower_reflection (m : ℕ) (q θ : ℝ) :
    chebyshevMobiusRealPower m q (2 * Real.pi - θ) = chebyshevMobiusRealPower m q θ := by
  have he : Complex.exp ((((2 * Real.pi - θ : ℝ) : ℂ)) * I) =
      conj (Complex.exp ((θ : ℂ) * I)) := by
    apply Complex.ext <;> simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.conj_re, Complex.conj_im, Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  unfold chebyshevMobiusRealPower
  rw [he, chebyshevMobius_conj, ← map_pow, Complex.conj_re]

theorem integral_chebyshevMobiusRealPower_full (m : ℕ) {q : ℝ} (hq : |q| < 1) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), chebyshevMobiusRealPower m q θ) = 2 * Real.pi := by
  have hi := (continuous_chebyshevMobius_power_exp m hq).intervalIntegrable
    (μ := volume) 0 (2 * Real.pi)
  have hh := Complex.reCLM.intervalIntegral_comp_comm hi
  rw [integral_chebyshevMobius_pow_exp m hq] at hh
  simpa only [chebyshevMobiusRealPower, Complex.reCLM_apply, Complex.ofReal_re] using hh

theorem integral_chebyshevMobiusRealPower_half (m : ℕ) {q : ℝ} (hq : |q| < 1) :
    (∫ θ : ℝ in (0 : ℝ)..Real.pi, chebyshevMobiusRealPower m q θ) = Real.pi := by
  have hc := continuous_chebyshevMobiusRealPower m hq
  have hreflect : (∫ θ : ℝ in Real.pi..(2 * Real.pi),
      chebyshevMobiusRealPower m q θ) =
      ∫ θ : ℝ in (0 : ℝ)..Real.pi, chebyshevMobiusRealPower m q θ := by
    have hh := intervalIntegral.integral_comp_sub_left (chebyshevMobiusRealPower m q)
      (a := Real.pi) (b := 2 * Real.pi) (2 * Real.pi)
    simpa only [chebyshevMobiusRealPower_reflection, sub_self,
      show 2 * Real.pi - Real.pi = Real.pi by ring] using hh
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 Real.pi)
    (hc.intervalIntegrable (μ := volume) Real.pi (2 * Real.pi))
  rw [hreflect, integral_chebyshevMobiusRealPower_full m hq] at hs
  linarith

theorem continuous_chebyshevAngleRadius (a d : ℝ) :
    Continuous (chebyshevAngleRadius a d) := by
  unfold chebyshevAngleRadius
  fun_prop

def chebyshevAngleProduct (m : ℕ) (a b d θ : ℝ) : ℝ :=
  chebyshevTValue m (a / chebyshevAngleRadius a d θ) *
    chebyshevTValue m (b / chebyshevAngleRadius a d θ)

theorem continuous_chebyshevAngleProduct (m : ℕ) (a b d : ℝ) (ha : 0 < a) :
    Continuous (chebyshevAngleProduct m a b d) := by
  have hr := continuous_chebyshevAngleRadius a d
  have hn : ∀ θ, chebyshevAngleRadius a d θ ≠ 0 := fun θ =>
    (chebyshevAngleRadius_pos ha d θ).ne'
  exact ((Polynomial.Chebyshev.T ℝ (m : ℤ)).continuous.comp
    (continuous_const.div hr hn)).mul
      ((Polynomial.Chebyshev.T ℝ (m : ℤ)).continuous.comp (continuous_const.div hr hn))

/-- The quarter-angle identity, obtained from a genuine holomorphic circle
mean and reflection. No Abel integral is used in its proof. -/
theorem integral_chebyshevAngleProduct (m : ℕ) (a b d : ℝ)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 - a ^ 2) :
    (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), chebyshevAngleProduct m a b d θ) = Real.pi / 2 := by
  let q : ℝ := d / (b + a)
  have hqb := chebyshevAbel_parameter_bounds a b d ha hab hd hd2
  have hq : |q| < 1 := by rw [abs_of_pos hqb.1]; exact hqb.2
  have hc := continuous_chebyshevMobiusRealPower m hq
  have hcr : Continuous (fun θ : ℝ => chebyshevMobiusRealPower m q (Real.pi - θ)) :=
    hc.comp (continuous_const.sub continuous_id)
  have hpoint (θ : ℝ) : 2 * chebyshevAngleProduct m a b d θ =
      chebyshevMobiusRealPower m q θ + chebyshevMobiusRealPower m q (Real.pi - θ) := by
    simpa only [chebyshevAngleProduct, chebyshevMobiusRealPower, mul_assoc] using
      chebyshevTValue_product_angle_mobius m a b d θ ha hab hd hd2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (Real.pi / 2))
    (hc.intervalIntegrable (μ := volume) (Real.pi / 2) Real.pi)
  have hreflect : (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
      chebyshevMobiusRealPower m q (Real.pi - θ)) =
      ∫ θ : ℝ in (Real.pi / 2)..Real.pi, chebyshevMobiusRealPower m q θ := by
    simpa only [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] using
      intervalIntegral.integral_comp_sub_left (chebyshevMobiusRealPower m q)
        (a := (0 : ℝ)) (b := Real.pi / 2) Real.pi
  have hh : 2 * (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
      chebyshevAngleProduct m a b d θ) = Real.pi := by
    calc
      _ = ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), 2 * chebyshevAngleProduct m a b d θ :=
        (intervalIntegral.integral_const_mul 2 _).symm
      _ = ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
          chebyshevMobiusRealPower m q θ + chebyshevMobiusRealPower m q (Real.pi - θ) :=
        intervalIntegral.integral_congr (fun θ _ => hpoint θ)
      _ = (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), chebyshevMobiusRealPower m q θ) +
          ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
            chebyshevMobiusRealPower m q (Real.pi - θ) :=
        intervalIntegral.integral_add (hc.intervalIntegrable 0 (Real.pi / 2))
          (hcr.intervalIntegrable 0 (Real.pi / 2))
      _ = ∫ θ : ℝ in (0 : ℝ)..Real.pi, chebyshevMobiusRealPower m q θ := by
        rw [hreflect]
        exact hsplit
      _ = Real.pi := integral_chebyshevMobiusRealPower_half m hq
  linarith

def chebyshevAngleSlope (a d θ : ℝ) : ℝ :=
  d ^ 2 * Real.sin θ * Real.cos θ / chebyshevAngleRadius a d θ

theorem chebyshevAngleRadius_hasDerivAt (a d θ : ℝ) (ha : 0 < a) :
    HasDerivAt (chebyshevAngleRadius a d) (chebyshevAngleSlope a d θ) θ := by
  have hpos : 0 < a ^ 2 + d ^ 2 * Real.sin θ ^ 2 := by
    have h₁ := sq_pos_of_pos ha
    have h₂ := mul_nonneg (sq_nonneg d) (sq_nonneg (Real.sin θ))
    linarith
  have hh := ((((Real.hasDerivAt_sin θ).pow 2).const_mul (d ^ 2)).const_add (a ^ 2)).sqrt hpos.ne'
  have hsqrt : Real.sqrt (a ^ 2 + d ^ 2 * Real.sin θ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  convert! hh using 1 <;>
    simp only [chebyshevAngleRadius, chebyshevAngleSlope, id_eq, Pi.pow_apply] <;>
    field_simp [hsqrt] <;> ring

theorem chebyshevAngleSlope_pos (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) : 0 < chebyshevAngleSlope a d θ := by
  rcases hθ with ⟨hθ0, hθπ⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  exact div_pos (mul_pos (mul_pos (sq_pos_of_pos hd) hs) hc) (chebyshevAngleRadius_pos ha d θ)

theorem chebyshevAngleRadius_strictMonoOn (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    StrictMonoOn (chebyshevAngleRadius a d) (Icc 0 (Real.pi / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (Real.pi / 2))
    (continuous_chebyshevAngleRadius a d).continuousOn
  intro θ hθ
  rw [interior_Icc] at hθ
  rw [(chebyshevAngleRadius_hasDerivAt a d θ ha).deriv]
  exact chebyshevAngleSlope_pos a d ha hd hθ

theorem chebyshevAngleRadius_image (a b d : ℝ) (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 - a ^ 2) :
    chebyshevAngleRadius a d '' Ioo 0 (Real.pi / 2) = Ioo a b := by
  have hzero : chebyshevAngleRadius a d 0 = a := by
    simp only [chebyshevAngleRadius, Real.sin_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hhalf : chebyshevAngleRadius a d (Real.pi / 2) = b := by
    have hb : 0 < b := lt_trans ha hab
    have heq : a ^ 2 + d ^ 2 = b ^ 2 := by linarith
    simp only [chebyshevAngleRadius, Real.sin_pi_div_two, one_pow, mul_one, heq,
      Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have hh := (continuous_chebyshevAngleRadius a d).continuousOn.image_Ioo_of_strictMonoOn
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity) (chebyshevAngleRadius_strictMonoOn a d ha hd)
  simpa only [hzero, hhalf] using hh

def chebyshevAbelKernel (m : ℕ) (a b s : ℝ) : ℝ :=
  s * chebyshevTValue m (a / s) * chebyshevTValue m (b / s) /
    (Real.sqrt (s ^ 2 - a ^ 2) * Real.sqrt (b ^ 2 - s ^ 2))

theorem chebyshevAbelKernel_angular_pullback (m : ℕ) (a b d : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 - a ^ 2)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    |chebyshevAngleSlope a d θ| •
        chebyshevAbelKernel m a b (chebyshevAngleRadius a d θ) =
      chebyshevAngleProduct m a b d θ := by
  rcases hθ with ⟨hθ0, hθπ⟩
  have hs := chebyshevAngleRadius_pos ha d θ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  have hsq : chebyshevAngleRadius a d θ ^ 2 = a ^ 2 + d ^ 2 * Real.sin θ ^ 2 := by
    exact Real.sq_sqrt (add_nonneg (sq_nonneg a) (mul_nonneg (sq_nonneg d) (sq_nonneg _)))
  have htrig := congrArg (fun t : ℝ => d ^ 2 * t) (Real.sin_sq_add_cos_sq θ)
  have h₁ : chebyshevAngleRadius a d θ ^ 2 - a ^ 2 = (d * Real.sin θ) ^ 2 := by
    rw [hsq]
    ring
  have h₂ : b ^ 2 - chebyshevAngleRadius a d θ ^ 2 = (d * Real.cos θ) ^ 2 := by
    rw [hsq]
    nlinarith only [hd2, htrig]
  rw [abs_of_pos (chebyshevAngleSlope_pos a d ha hd ⟨hθ0, hθπ⟩)]
  dsimp only [chebyshevAbelKernel, chebyshevAngleSlope, chebyshevAngleProduct]
  rw [h₁, h₂, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos hd hsin), abs_of_pos (mul_pos hd hcos)]
  simp only [smul_eq_mul]
  field_simp [hs.ne', hd.ne', hsin.ne', hcos.ne']

/-- Both the value and the genuine endpoint integrability of the composite
kernel. The Jacobian theorem is used only on the open interval. -/
theorem chebyshevAbelKernel_integrable_and_integral (m : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    IntegrableOn (chebyshevAbelKernel m a b) (Ioo a b) ∧
      (∫ s : ℝ in Ioo a b, chebyshevAbelKernel m a b s) = Real.pi / 2 := by
  let d : ℝ := Real.sqrt (b ^ 2 - a ^ 2)
  have hdiff : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have hd : 0 < d := Real.sqrt_pos.mpr hdiff
  have hd2 : d ^ 2 = b ^ 2 - a ^ 2 := Real.sq_sqrt hdiff.le
  have himage := chebyshevAngleRadius_image a b d ha hab hd hd2
  have hinj : InjOn (chebyshevAngleRadius a d) (Ioo 0 (Real.pi / 2)) :=
    ((chebyshevAngleRadius_strictMonoOn a d ha hd).mono Ioo_subset_Icc_self).injOn
  have hderiv (θ : ℝ) (_hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
      HasDerivWithinAt (chebyshevAngleRadius a d) (chebyshevAngleSlope a d θ)
        (Ioo 0 (Real.pi / 2)) θ :=
    (chebyshevAngleRadius_hasDerivAt a d θ ha).hasDerivWithinAt
  have hpull (θ : ℝ) (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :=
    chebyshevAbelKernel_angular_pullback m a b d ha hd hd2 hθ
  have hc := continuous_chebyshevAngleProduct m a b d ha
  have hiP : IntegrableOn (chebyshevAngleProduct m a b d) (Ioo 0 (Real.pi / 2)) := by
    have hh := (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).mp
        (hc.intervalIntegrable (μ := volume) 0 (Real.pi / 2))
    exact hh.mono_set Ioo_subset_Ioc_self
  have hiPull : IntegrableOn (fun θ => |chebyshevAngleSlope a d θ| •
      chebyshevAbelKernel m a b (chebyshevAngleRadius a d θ)) (Ioo 0 (Real.pi / 2)) :=
    hiP.congr_fun (fun θ hθ => (hpull θ hθ).symm) measurableSet_Ioo
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo hderiv hinj (chebyshevAbelKernel m a b)
  rw [himage] at hiff
  refine ⟨hiff.mpr hiPull, ?_⟩
  have hJac := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj (chebyshevAbelKernel m a b)
  rw [himage] at hJac
  calc
    _ = ∫ θ : ℝ in Ioo 0 (Real.pi / 2), |chebyshevAngleSlope a d θ| •
        chebyshevAbelKernel m a b (chebyshevAngleRadius a d θ) := hJac
    _ = ∫ θ : ℝ in Ioo 0 (Real.pi / 2), chebyshevAngleProduct m a b d θ :=
      setIntegral_congr_fun measurableSet_Ioo hpull
    _ = ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), chebyshevAngleProduct m a b d θ := by
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity),
        integral_Ioc_eq_integral_Ioo]
    _ = Real.pi / 2 := integral_chebyshevAngleProduct m a b d ha hab hd hd2

theorem integral_chebyshevAbelKernel (m : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∫ s : ℝ in Ioo a b, chebyshevAbelKernel m a b s) = Real.pi / 2 :=
  (chebyshevAbelKernel_integrable_and_integral m a b ha hab).2

end J0RadialUniqueness
