import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Actual integrals on the four sides of a square. Cauchy--Goursat is the
proved Mathlib rectangle theorem. The inverse-kernel integral is computed at
the center by arctan, and then transported to every interior pole by a finite
partition into four holomorphic rectangles and a translated smaller square.
No winding-number assertion is taken as an input. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval

namespace J0RadialUniqueness

def rectangleBoundaryIntegral (x₀ x₁ y₀ y₁ : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ t : ℝ in x₀..x₁, f ((t : ℂ) + (y₀ : ℂ) * Complex.I)) -
  (∫ t : ℝ in x₀..x₁, f ((t : ℂ) + (y₁ : ℂ) * Complex.I)) +
  Complex.I * (∫ t : ℝ in y₀..y₁, f ((x₁ : ℂ) + (t : ℂ) * Complex.I)) -
  Complex.I * (∫ t : ℝ in y₀..y₁, f ((x₀ : ℂ) + (t : ℂ) * Complex.I))

def squareBoundaryIntegral (a : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ t : ℝ in -a..a, f ((t : ℂ) - (a : ℂ) * Complex.I)) -
  (∫ t : ℝ in -a..a, f ((t : ℂ) + (a : ℂ) * Complex.I)) +
  Complex.I * (∫ t : ℝ in -a..a, f ((a : ℂ) + (t : ℂ) * Complex.I)) -
  Complex.I * (∫ t : ℝ in -a..a, f (-(a : ℂ) + (t : ℂ) * Complex.I))

theorem squareBoundaryIntegral_eq_rectangle (a : ℝ) (f : ℂ → ℂ) :
    squareBoundaryIntegral a f = rectangleBoundaryIntegral (-a) a (-a) a f := by
  simp only [squareBoundaryIntegral, rectangleBoundaryIntegral, Complex.ofReal_neg,
    neg_mul, sub_eq_add_neg]

theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Icc x₀ x₁ ×ℂ Icc y₀ y₁)) :
    rectangleBoundaryIntegral x₀ x₁ y₀ y₁ f = 0 := by
  have hd : DifferentiableOn ℂ f ([[x₀, x₁]] ×ℂ [[y₀, y₁]]) := by
    simpa only [uIcc_of_le hx, uIcc_of_le hy] using hf
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f (⟨x₀, y₀⟩ : ℂ) (⟨x₁, y₁⟩ : ℂ) hd
  simpa only [rectangleBoundaryIntegral, smul_eq_mul] using hh

theorem squareBoundaryIntegral_eq_zero_of_differentiableOn {a : ℝ} (ha : 0 ≤ a)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Icc (-a) a ×ℂ Icc (-a) a)) :
    squareBoundaryIntegral a f = 0 := by
  rw [squareBoundaryIntegral_eq_rectangle]
  exact rectangleBoundaryIntegral_eq_zero_of_differentiableOn (by linarith) (by linarith) f hf

def squareBoundarySet (a : ℝ) : Set ℂ :=
  {z | (|z.re| = a ∧ |z.im| ≤ a) ∨ (|z.im| = a ∧ |z.re| ≤ a)}

/-- The actual total boundary length is 8a. The estimate does not silently
assume an exchange or a contour parametrization theorem. -/
theorem norm_squareBoundaryIntegral_le {a C : ℝ} (ha : 0 ≤ a) (f : ℂ → ℂ)
    (hbound : ∀ z ∈ squareBoundarySet a, ‖f z‖ ≤ C) :
    ‖squareBoundaryIntegral a f‖ ≤ 8 * a * C := by
  have hpoint (t : ℝ) (ht : t ∈ Icc (-a) a) : |t| ≤ a := abs_le.mpr ht
  have h2a : (0 : ℝ) ≤ 2 * a := mul_nonneg (by norm_num) ha
  have hb : ‖∫ t : ℝ in -a..a, f ((t : ℂ) - (a : ℂ) * Complex.I)‖ ≤ C * (2 * a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ => f ((t : ℂ) - (a : ℂ) * Complex.I)) (a := -a) (b := a)
      (C := C) (fun t ht => hbound _ (Or.inr ⟨by simp [ha], by simpa using (hpoint t
        (by rw [uIoc_of_le (by linarith : -a ≤ a)] at ht; exact ⟨ht.1.le, ht.2⟩))⟩))
    simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg h2a] using hh
  have ht : ‖∫ t : ℝ in -a..a, f ((t : ℂ) + (a : ℂ) * Complex.I)‖ ≤ C * (2 * a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ => f ((t : ℂ) + (a : ℂ) * Complex.I)) (a := -a) (b := a)
      (C := C) (fun t ht => hbound _ (Or.inr ⟨by simp [ha], by simpa using (hpoint t
        (by rw [uIoc_of_le (by linarith : -a ≤ a)] at ht; exact ⟨ht.1.le, ht.2⟩))⟩))
    simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg h2a] using hh
  have hr : ‖∫ t : ℝ in -a..a, f ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (2 * a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I)) (a := -a) (b := a)
      (C := C) (fun t ht => hbound _ (Or.inl ⟨by simp [ha], by simpa using (hpoint t
        (by rw [uIoc_of_le (by linarith : -a ≤ a)] at ht; exact ⟨ht.1.le, ht.2⟩))⟩))
    simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg h2a] using hh
  have hl : ‖∫ t : ℝ in -a..a, f (-(a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (2 * a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ => f (-(a : ℂ) + (t : ℂ) * Complex.I)) (a := -a) (b := a)
      (C := C) (fun t ht => hbound _ (Or.inl ⟨by simp [ha], by simpa using (hpoint t
        (by rw [uIoc_of_le (by linarith : -a ≤ a)] at ht; exact ⟨ht.1.le, ht.2⟩))⟩))
    simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg h2a] using hh
  unfold squareBoundaryIntegral
  have hn := norm_sub_le
    ((∫ t : ℝ in -a..a, f ((t : ℂ) - (a : ℂ) * Complex.I)) -
      (∫ t : ℝ in -a..a, f ((t : ℂ) + (a : ℂ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in -a..a, f ((a : ℂ) + (t : ℂ) * Complex.I)))
    (Complex.I * (∫ t : ℝ in -a..a, f (-(a : ℂ) + (t : ℂ) * Complex.I)))
  have hn₂ := norm_add_le
    ((∫ t : ℝ in -a..a, f ((t : ℂ) - (a : ℂ) * Complex.I)) -
      (∫ t : ℝ in -a..a, f ((t : ℂ) + (a : ℂ) * Complex.I)))
    (Complex.I * (∫ t : ℝ in -a..a, f ((a : ℂ) + (t : ℂ) * Complex.I)))
  have hn₃ := norm_sub_le
    (∫ t : ℝ in -a..a, f ((t : ℂ) - (a : ℂ) * Complex.I))
    (∫ t : ℝ in -a..a, f ((t : ℂ) + (a : ℂ) * Complex.I))
  simp only [norm_mul, Complex.norm_I, one_mul] at hn hn₂
  linarith

theorem rectangleBoundaryIntegral_split_y (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ y₂ : ℝ)
    (hl₀ : IntervalIntegrable (fun t : ℝ => f ((x₀ : ℂ) + (t : ℂ) * Complex.I)) volume y₀ y₁)
    (hl₁ : IntervalIntegrable (fun t : ℝ => f ((x₀ : ℂ) + (t : ℂ) * Complex.I)) volume y₁ y₂)
    (hr₀ : IntervalIntegrable (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * Complex.I)) volume y₀ y₁)
    (hr₁ : IntervalIntegrable (fun t : ℝ => f ((x₁ : ℂ) + (t : ℂ) * Complex.I)) volume y₁ y₂) :
    rectangleBoundaryIntegral x₀ x₁ y₀ y₂ f =
      rectangleBoundaryIntegral x₀ x₁ y₀ y₁ f + rectangleBoundaryIntegral x₀ x₁ y₁ y₂ f := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hr₀ hr₁,
    ← intervalIntegral.integral_add_adjacent_intervals hl₀ hl₁]
  ring

theorem rectangleBoundaryIntegral_split_x (f : ℂ → ℂ) (x₀ x₁ x₂ y₀ y₁ : ℝ)
    (hb₀ : IntervalIntegrable (fun t : ℝ => f ((t : ℂ) + (y₀ : ℂ) * Complex.I)) volume x₀ x₁)
    (hb₁ : IntervalIntegrable (fun t : ℝ => f ((t : ℂ) + (y₀ : ℂ) * Complex.I)) volume x₁ x₂)
    (ht₀ : IntervalIntegrable (fun t : ℝ => f ((t : ℂ) + (y₁ : ℂ) * Complex.I)) volume x₀ x₁)
    (ht₁ : IntervalIntegrable (fun t : ℝ => f ((t : ℂ) + (y₁ : ℂ) * Complex.I)) volume x₁ x₂) :
    rectangleBoundaryIntegral x₀ x₂ y₀ y₁ f =
      rectangleBoundaryIntegral x₀ x₁ y₀ y₁ f + rectangleBoundaryIntegral x₁ x₂ y₀ y₁ f := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hb₀ hb₁,
    ← intervalIntegral.integral_add_adjacent_intervals ht₀ ht₁]
  ring

theorem continuous_inv_sub_horizontal (w : ℂ) {b : ℝ} (hb : b ≠ w.im) :
    Continuous (fun t : ℝ => ((t : ℂ) + (b : ℂ) * Complex.I - w)⁻¹) := by
  have hc : Continuous (fun t : ℝ => (t : ℂ) + (b : ℂ) * Complex.I - w) := by fun_prop
  apply hc.inv₀
  intro t hz
  have he : b - w.im = 0 := by simpa [Complex.mul_im] using congrArg Complex.im hz
  exact hb (sub_eq_zero.mp he)

theorem continuous_inv_sub_vertical (w : ℂ) {b : ℝ} (hb : b ≠ w.re) :
    Continuous (fun t : ℝ => ((b : ℂ) + (t : ℂ) * Complex.I - w)⁻¹) := by
  have hc : Continuous (fun t : ℝ => (b : ℂ) + (t : ℂ) * Complex.I - w) := by fun_prop
  apply hc.inv₀
  intro t hz
  have he : b - w.re = 0 := by simpa [Complex.mul_re] using congrArg Complex.re hz
  exact hb (sub_eq_zero.mp he)

theorem rectangleBoundaryIntegral_inv_sub_eq_zero {x₀ x₁ y₀ y₁ : ℝ}
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (w : ℂ)
    (hw : w ∉ Icc x₀ x₁ ×ℂ Icc y₀ y₁) :
    rectangleBoundaryIntegral x₀ x₁ y₀ y₁ (fun z => (z - w)⁻¹) = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn hx hy
  intro z hz
  have hzw : z - w ≠ 0 := by
    intro he
    exact hw ((sub_eq_zero.mp he) ▸ hz)
  exact ((differentiableAt_id.sub_const w).inv hzw).differentiableWithinAt

theorem integral_symmetric_eq_zero_of_odd (g : ℝ → ℝ)
    (hg : ∀ t, g (-t) = -g t) (a : ℝ) : (∫ t : ℝ in -a..a, g t) = 0 := by
  have hh := intervalIntegral.integral_comp_neg (a := -a) (b := a) g
  simp only [neg_neg] at hh
  simp_rw [hg, intervalIntegral.integral_neg] at hh
  linarith

theorem integral_inv_right_edge {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in -a..a, ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) = (Real.pi / 2 : ℝ) := by
  have hc : Continuous (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) := by
    simpa only [sub_zero] using continuous_inv_sub_vertical (0 : ℂ) (by simpa using ha.ne')
  have hi : IntervalIntegrable
      (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) volume (-a) a :=
    hc.intervalIntegrable (μ := volume) (-a) a
  have hre (t : ℝ) : (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹).re = a / (a ^ 2 + t ^ 2) := by
    rw [Complex.inv_re, Complex.normSq_add_mul_I]
    simp
  have him (t : ℝ) : (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹).im = -t / (a ^ 2 + t ^ 2) := by
    rw [Complex.inv_im, Complex.normSq_add_mul_I]
    simp
  have hreint :
      (∫ t : ℝ in -a..a, ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
      ∫ t : ℝ in -a..a, (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hi).symm
  have himint :
      (∫ t : ℝ in -a..a, ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
      ∫ t : ℝ in -a..a, (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hi).symm
  apply Complex.ext
  · rw [hreint]
    simp_rw [hre]
    rw [integral_div_sq_add_sq]
    simp only [div_self ha.ne', neg_div, Real.arctan_neg, Real.arctan_one, Complex.ofReal_re]
    ring
  · rw [himint]
    simp_rw [him]
    have hh := integral_symmetric_eq_zero_of_odd
      (fun t : ℝ => -t / (a ^ 2 + t ^ 2)) (by intro t; simp [neg_div]) a
    simpa only [Complex.ofReal_im] using hh

theorem squareBoundaryIntegral_inv_zero {a : ℝ} (ha : 0 < a) :
    squareBoundaryIntegral a (fun z : ℂ => z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
  let J : ℂ := ∫ t : ℝ in -a..a, ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹
  have hflip : (∫ t : ℝ in -a..a, ((a : ℂ) - (t : ℂ) * Complex.I)⁻¹) = J := by
    have hh := intervalIntegral.integral_comp_neg (a := -a) (b := a)
      (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)
    simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, neg_neg] using hh
  have hbottom (t : ℝ) : ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹ =
      Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
    have he : (t : ℂ) - (a : ℂ) * Complex.I =
        -Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I) := by
      linear_combination (t : ℂ) * Complex.I_sq
    rw [he, mul_inv_rev]
    simp only [inv_neg, Complex.inv_I, neg_neg]
    ring
  have htop (t : ℝ) : ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹ =
      -Complex.I * ((a : ℂ) - (t : ℂ) * Complex.I)⁻¹ := by
    have he : (t : ℂ) + (a : ℂ) * Complex.I =
        Complex.I * ((a : ℂ) - (t : ℂ) * Complex.I) := by
      linear_combination (t : ℂ) * Complex.I_sq
    rw [he, mul_inv_rev, Complex.inv_I]
    ring
  have hleft (t : ℝ) : (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹ =
      -((a : ℂ) - (t : ℂ) * Complex.I)⁻¹ := by
    rw [show -(a : ℂ) + (t : ℂ) * Complex.I =
      -((a : ℂ) - (t : ℂ) * Complex.I) by ring, inv_neg]
  unfold squareBoundaryIntegral
  simp_rw [hbottom, htop, hleft]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_neg, hflip]
  have hJ : J = ((Real.pi / 2 : ℝ) : ℂ) := integral_inv_right_edge ha
  change Complex.I * J - -Complex.I * J + Complex.I * J - Complex.I * -J = _
  rw [hJ]
  push_cast
  ring

theorem integral_translate_horizontal_inv_kernel (w : ℂ) (a b c : ℝ) :
    (∫ t : ℝ in (w.re + a)..(w.re + b),
      ((t : ℂ) + ((w.im + c : ℝ) : ℂ) * Complex.I - w)⁻¹) =
      ∫ t : ℝ in a..b, ((t : ℂ) + (c : ℂ) * Complex.I)⁻¹ := by
  rw [← intervalIntegral.integral_comp_add_left
    (fun t : ℝ => ((t : ℂ) + ((w.im + c : ℝ) : ℂ) * Complex.I - w)⁻¹) w.re]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  congr 1
  push_cast
  linear_combination Complex.re_add_im w

theorem integral_translate_vertical_inv_kernel (w : ℂ) (a b c : ℝ) :
    (∫ t : ℝ in (w.im + a)..(w.im + b),
      (((w.re + c : ℝ) : ℂ) + (t : ℂ) * Complex.I - w)⁻¹) =
      ∫ t : ℝ in a..b, ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
  rw [← intervalIntegral.integral_comp_add_left
    (fun t : ℝ => (((w.re + c : ℝ) : ℂ) + (t : ℂ) * Complex.I - w)⁻¹) w.im]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  congr 1
  push_cast
  linear_combination Complex.re_add_im w

theorem rectangleBoundaryIntegral_inv_sub_center (w : ℂ) (e : ℝ) :
    rectangleBoundaryIntegral (w.re - e) (w.re + e) (w.im - e) (w.im + e)
      (fun z => (z - w)⁻¹) = squareBoundaryIntegral e (fun z : ℂ => z⁻¹) := by
  rw [squareBoundaryIntegral_eq_rectangle]
  unfold rectangleBoundaryIntegral
  rw [show w.re - e = w.re + (-e) by ring, show w.im - e = w.im + (-e) by ring]
  rw [integral_translate_horizontal_inv_kernel w (-e) e (-e),
    integral_translate_horizontal_inv_kernel w (-e) e e,
    integral_translate_vertical_inv_kernel w (-e) e e,
    integral_translate_vertical_inv_kernel w (-e) e (-e)]

/-- The actual inverse kernel has integral 2πi at every strictly interior
point. Four genuine Cauchy--Goursat applications and adjacent-interval
identities reduce the arbitrary pole to the explicit central calculation. -/
theorem squareBoundaryIntegral_inv_sub {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hre : |w.re| < a) (him : |w.im| < a) :
    squareBoundaryIntegral a (fun z => (z - w)⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
  let e : ℝ := min (a - |w.re|) (a - |w.im|) / 2
  have hmin : 0 < min (a - |w.re|) (a - |w.im|) := lt_min (by linarith) (by linarith)
  have he : 0 < e := by dsimp [e]; positivity
  have heR : e < a - |w.re| := by
    have hh := min_le_left (a - |w.re|) (a - |w.im|)
    dsimp [e]
    linarith
  have heI : e < a - |w.im| := by
    have hh := min_le_right (a - |w.re|) (a - |w.im|)
    dsimp [e]
    linarith
  have hx₀ : -a < w.re - e := by linarith [neg_abs_le w.re]
  have hx₁ : w.re + e < a := by linarith [le_abs_self w.re]
  have hy₀ : -a < w.im - e := by linarith [neg_abs_le w.im]
  have hy₁ : w.im + e < a := by linarith [le_abs_self w.im]
  let f : ℂ → ℂ := fun z => (z - w)⁻¹
  have hvl := continuous_inv_sub_vertical w
    (b := -a) (ne_of_lt (abs_lt.mp hre).1)
  have hvr := continuous_inv_sub_vertical w
    (b := a) (ne_of_gt (abs_lt.mp hre).2)
  have hhb := continuous_inv_sub_horizontal w
    (b := w.im - e) (by linarith : w.im - e ≠ w.im)
  have hht := continuous_inv_sub_horizontal w
    (b := w.im + e) (by linarith : w.im + e ≠ w.im)
  have hsplit₀ := rectangleBoundaryIntegral_split_y f (-a) a (-a) (w.im - e) a
    (hvl.intervalIntegrable _ _) (hvl.intervalIntegrable _ _)
    (hvr.intervalIntegrable _ _) (hvr.intervalIntegrable _ _)
  have hsplit₁ := rectangleBoundaryIntegral_split_y f (-a) a (w.im - e) (w.im + e) a
    (hvl.intervalIntegrable _ _) (hvl.intervalIntegrable _ _)
    (hvr.intervalIntegrable _ _) (hvr.intervalIntegrable _ _)
  have hsplit₂ := rectangleBoundaryIntegral_split_x f (-a) (w.re - e) a (w.im - e) (w.im + e)
    (hhb.intervalIntegrable _ _) (hhb.intervalIntegrable _ _)
    (hht.intervalIntegrable _ _) (hht.intervalIntegrable _ _)
  have hsplit₃ := rectangleBoundaryIntegral_split_x f (w.re - e) (w.re + e) a (w.im - e) (w.im + e)
    (hhb.intervalIntegrable _ _) (hhb.intervalIntegrable _ _)
    (hht.intervalIntegrable _ _) (hht.intervalIntegrable _ _)
  have hb : rectangleBoundaryIntegral (-a) a (-a) (w.im - e) f = 0 := by
    apply rectangleBoundaryIntegral_inv_sub_eq_zero (by linarith) hy₀.le w
    intro hw
    have hh := hw.2.2
    linarith
  have ht : rectangleBoundaryIntegral (-a) a (w.im + e) a f = 0 := by
    apply rectangleBoundaryIntegral_inv_sub_eq_zero (by linarith) hy₁.le w
    intro hw
    have hh := hw.2.1
    linarith
  have hl : rectangleBoundaryIntegral (-a) (w.re - e) (w.im - e) (w.im + e) f = 0 := by
    apply rectangleBoundaryIntegral_inv_sub_eq_zero hx₀.le (by linarith) w
    intro hw
    have hh := hw.1.2
    linarith
  have hr : rectangleBoundaryIntegral (w.re + e) a (w.im - e) (w.im + e) f = 0 := by
    apply rectangleBoundaryIntegral_inv_sub_eq_zero hx₁.le (by linarith) w
    intro hw
    have hh := hw.1.1
    linarith
  rw [squareBoundaryIntegral_eq_rectangle, hsplit₀, hsplit₁, hsplit₂, hsplit₃, hb, ht, hl, hr]
  simp only [zero_add, add_zero]
  exact (rectangleBoundaryIntegral_inv_sub_center w e).trans (squareBoundaryIntegral_inv_zero he)

end J0RadialUniqueness
