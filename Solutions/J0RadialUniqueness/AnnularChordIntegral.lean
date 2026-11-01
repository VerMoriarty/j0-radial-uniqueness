import Solutions.J0RadialUniqueness.ChebyshevAbelIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The genuine annular chord substitution on the open angular interval.
The zero chord at the possible endpoint `ρ = r, α = π` is never differentiated.
The Jacobian theorem also proves the integrability of the endpoint-singular
radial density, rather than treating it as a formal change of variables. -/

noncomputable section

open MeasureTheory Set
open scoped Topology Interval

namespace J0RadialUniqueness

def annularChordRadius (ρ r α : ℝ) : ℝ :=
  Real.sqrt (ρ ^ 2 + r ^ 2 + 2 * ρ * r * Real.cos α)

def annularChordSlope (ρ r α : ℝ) : ℝ :=
  -(ρ * r * Real.sin α) / annularChordRadius ρ r α

def annularChordAngleArgument (ρ r α : ℝ) : ℝ :=
  (ρ + r * Real.cos α) / annularChordRadius ρ r α

def annularChordArgument (ρ r s : ℝ) : ℝ :=
  (s ^ 2 + ρ ^ 2 - r ^ 2) / (2 * s * ρ)

def annularChordDensity (ρ r s : ℝ) : ℝ :=
  2 * s / Real.sqrt ((s ^ 2 - (ρ - r) ^ 2) * ((ρ + r) ^ 2 - s ^ 2))

def annularChordChebyshevKernel (m : ℕ) (ρ r s : ℝ) : ℝ :=
  annularChordDensity ρ r s * chebyshevTValue m (annularChordArgument ρ r s)

theorem annularChordRadicand_nonneg {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (α : ℝ) :
    0 ≤ ρ ^ 2 + r ^ 2 + 2 * ρ * r * Real.cos α := by
  have hp : 0 ≤ 2 * ρ * r * (1 + Real.cos α) :=
    mul_nonneg (by positivity) (by linarith [Real.neg_one_le_cos α])
  nlinarith only [hp, sq_nonneg (ρ - r)]

theorem annularChordRadius_sq {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (α : ℝ) :
    annularChordRadius ρ r α ^ 2 = ρ ^ 2 + r ^ 2 + 2 * ρ * r * Real.cos α :=
  Real.sq_sqrt (annularChordRadicand_nonneg hρ hr α)

theorem continuous_annularChordRadius (ρ r : ℝ) : Continuous (annularChordRadius ρ r) := by
  unfold annularChordRadius
  fun_prop

theorem annularChordRadius_nonneg (ρ r α : ℝ) : 0 ≤ annularChordRadius ρ r α :=
  Real.sqrt_nonneg _

theorem annularChordRadius_le_sum {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (α : ℝ) :
    annularChordRadius ρ r α ≤ ρ + r := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hp := mul_le_mul_of_nonneg_left (Real.cos_le_one α) (show 0 ≤ 2 * ρ * r by positivity)
  nlinarith

theorem annularChordRadius_pos {ρ r α : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hα : α ∈ Ioo (0 : ℝ) Real.pi) : 0 < annularChordRadius ρ r α := by
  apply Real.sqrt_pos.mpr
  have hc : -1 < Real.cos α := by
    have hh := Real.strictAntiOn_cos ⟨hα.1.le, hα.2.le⟩
      ⟨Real.pi_pos.le, le_refl Real.pi⟩ hα.2
    simpa only [Real.cos_pi] using hh
  have hp : 0 < 2 * ρ * r * (1 + Real.cos α) := mul_pos (by positivity) (by linarith)
  nlinarith only [hp, sq_nonneg (ρ - r)]

theorem annularChordRadius_hasDerivAt {ρ r α : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    HasDerivAt (annularChordRadius ρ r) (annularChordSlope ρ r α) α := by
  have hpos : 0 < ρ ^ 2 + r ^ 2 + 2 * ρ * r * Real.cos α :=
    Real.sqrt_pos.mp (annularChordRadius_pos hρ hr hα)
  have hd := (((Real.hasDerivAt_cos α).const_mul (2 * ρ * r)).const_add (ρ ^ 2 + r ^ 2)).sqrt hpos.ne'
  have hs := (annularChordRadius_pos hρ hr hα).ne'
  convert! hd using 1 <;>
    simp only [annularChordRadius, annularChordSlope, id_eq] <;>
    field_simp [hs] <;> ring

theorem annularChordSlope_neg {ρ r α : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hα : α ∈ Ioo (0 : ℝ) Real.pi) : annularChordSlope ρ r α < 0 := by
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (mul_pos hρ hr)
    (Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2))) (annularChordRadius_pos hρ hr hα)

theorem annularChordRadius_strictAntiOn {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    StrictAntiOn (annularChordRadius ρ r) (Icc (0 : ℝ) Real.pi) := by
  intro α hα β hβ hαβ
  apply Real.sqrt_lt_sqrt (annularChordRadicand_nonneg hρ hr β)
  have hc := mul_lt_mul_of_pos_left (Real.strictAntiOn_cos hα hβ hαβ)
    (show 0 < 2 * ρ * r by positivity)
  linarith

theorem annularChordRadius_zero {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    annularChordRadius ρ r 0 = ρ + r := by
  have he : ρ ^ 2 + r ^ 2 + 2 * ρ * r = (ρ + r) ^ 2 := by ring
  simp only [annularChordRadius, Real.cos_zero, mul_one, he, Real.sqrt_sq_eq_abs,
    abs_of_pos (add_pos hρ hr)]

theorem annularChordRadius_pi (ρ r : ℝ) : annularChordRadius ρ r Real.pi = |ρ - r| := by
  have he : ρ ^ 2 + r ^ 2 - 2 * ρ * r = (ρ - r) ^ 2 := by ring
  simp only [annularChordRadius, Real.cos_pi, mul_neg_one, ← sub_eq_add_neg, he,
    Real.sqrt_sq_eq_abs]

theorem annularChordRadius_image {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    annularChordRadius ρ r '' Ioo (0 : ℝ) Real.pi = Ioo |ρ - r| (ρ + r) := by
  have hh := (continuous_annularChordRadius ρ r).continuousOn.image_Ioo_of_strictAntiOn
    Real.pi_pos.le (annularChordRadius_strictAntiOn hρ hr)
  simpa only [annularChordRadius_zero hρ hr, annularChordRadius_pi] using hh

theorem annularChordAngleArgument_abs_le_one {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (α : ℝ) :
    |annularChordAngleArgument ρ r α| ≤ 1 := by
  have hs := annularChordRadius_nonneg ρ r α
  have hsq := annularChordRadius_sq hρ hr α
  have hcos : Real.cos α ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α)]
  have hp := mul_le_mul_of_nonneg_left hcos (sq_nonneg r)
  have hnum : |ρ + r * Real.cos α| ≤ annularChordRadius ρ r α := by
    apply abs_le_of_sq_le_sq _ hs
    nlinarith
  by_cases hz : annularChordRadius ρ r α = 0
  · simp only [annularChordAngleArgument, hz, div_zero, abs_zero, zero_le_one]
  · unfold annularChordAngleArgument
    rw [abs_div, abs_of_nonneg hs]
    exact (div_le_one (lt_of_le_of_ne hs (Ne.symm hz))).2 hnum

theorem chebyshevTValue_abs_le_one (m : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |chebyshevTValue m x| ≤ 1 := by
  have hx' := abs_le.mp hx
  unfold chebyshevTValue
  rw [← Real.cos_arccos hx'.1 hx'.2, Polynomial.Chebyshev.T_real_cos]
  exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem measurable_annularChordAngleArgument (ρ r : ℝ) :
    Measurable (annularChordAngleArgument ρ r) := by
  exact (measurable_const.add (Real.continuous_cos.measurable.const_mul r)).div
    (continuous_annularChordRadius ρ r).measurable

theorem measurable_annularChordAngleIntegrand (m : ℕ) (ρ r : ℝ)
    {v : ℝ → ℂ} (hv : Continuous v) :
    Measurable (fun α : ℝ => chebyshevTValue m (annularChordAngleArgument ρ r α) •
      v (annularChordRadius ρ r α)) := by
  exact (((Polynomial.Chebyshev.T ℝ (m : ℤ)).continuous.measurable.comp
    (measurable_annularChordAngleArgument ρ r)).smul
      (hv.measurable.comp (continuous_annularChordRadius ρ r).measurable))

theorem annularChordAngleIntegrand_integrableOn (m : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn (fun α : ℝ => chebyshevTValue m (annularChordAngleArgument ρ r α) •
      v (annularChordRadius ρ r α)) (Ioo (0 : ℝ) Real.pi) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (ρ + r))).exists_bound_of_continuousOn hv.continuousOn
  have hMnonneg : 0 ≤ M := (norm_nonneg (v 0)).trans (hM 0 ⟨le_refl 0, by positivity⟩)
  have hbound (α : ℝ) :
      ‖chebyshevTValue m (annularChordAngleArgument ρ r α) • v (annularChordRadius ρ r α)‖ ≤ M := by
    rw [norm_smul, Real.norm_eq_abs]
    have hT := chebyshevTValue_abs_le_one m (annularChordAngleArgument_abs_le_one hρ hr α)
    have hvM := hM (annularChordRadius ρ r α)
      ⟨annularChordRadius_nonneg ρ r α, annularChordRadius_le_sum hρ hr α⟩
    exact (mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans (by simpa only [one_mul] using hvM)
  have hi : IntegrableOn (fun _α : ℝ => M) (Ioo (0 : ℝ) Real.pi) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact hi.mono' (measurable_annularChordAngleIntegrand m ρ r hv).aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall hbound)

theorem annularChordArgument_pullback {ρ r α : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    annularChordArgument ρ r (annularChordRadius ρ r α) = annularChordAngleArgument ρ r α := by
  have hs := (annularChordRadius_pos hρ hr hα).ne'
  have hsq := annularChordRadius_sq hρ hr α
  unfold annularChordArgument annularChordAngleArgument
  field_simp [hs, hρ.ne']
  nlinarith only [hsq]

theorem annularChordDiscriminant_sqrt {ρ r α : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    Real.sqrt ((annularChordRadius ρ r α ^ 2 - (ρ - r) ^ 2) *
      ((ρ + r) ^ 2 - annularChordRadius ρ r α ^ 2)) = 2 * ρ * r * Real.sin α := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hsq := annularChordRadius_sq hρ hr α
  have htrig : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq α]
  have he : (annularChordRadius ρ r α ^ 2 - (ρ - r) ^ 2) *
      ((ρ + r) ^ 2 - annularChordRadius ρ r α ^ 2) = (2 * ρ * r * Real.sin α) ^ 2 := by
    calc
      _ = 4 * ρ ^ 2 * r ^ 2 * (1 - Real.cos α ^ 2) := by rw [hsq]; ring
      _ = _ := by rw [htrig]; ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 2 * ρ * r * Real.sin α)]

theorem annularChordDensity_pullback {ρ r α : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    |annularChordSlope ρ r α| • annularChordDensity ρ r (annularChordRadius ρ r α) = 1 := by
  have hs := (annularChordRadius_pos hρ hr hα).ne'
  have hsin := (Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2).ne'
  rw [abs_of_neg (annularChordSlope_neg hρ hr hα)]
  unfold annularChordDensity annularChordSlope
  rw [annularChordDiscriminant_sqrt hρ hr hα]
  simp only [smul_eq_mul]
  field_simp [hs, hρ.ne', hr.ne', hsin] <;> ring

theorem annularChordChebyshevKernel_pullback (m : ℕ) {ρ r α : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    |annularChordSlope ρ r α| • annularChordChebyshevKernel m ρ r (annularChordRadius ρ r α) =
      chebyshevTValue m (annularChordAngleArgument ρ r α) := by
  unfold annularChordChebyshevKernel
  rw [annularChordArgument_pullback hρ hr hα]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  have hp := annularChordDensity_pullback hρ hr hα
  simp only [smul_eq_mul] at hp
  rw [hp, one_mul]

theorem annularChordDensity_integrable_and_integral {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    IntegrableOn (annularChordDensity ρ r) (Ioo |ρ - r| (ρ + r)) ∧
      (∫ s : ℝ in Ioo |ρ - r| (ρ + r), annularChordDensity ρ r s) = Real.pi := by
  have himage := annularChordRadius_image hρ hr
  have hinj := ((annularChordRadius_strictAntiOn hρ hr).mono Ioo_subset_Icc_self).injOn
  have hderiv (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
      HasDerivWithinAt (annularChordRadius ρ r) (annularChordSlope ρ r α) (Ioo 0 Real.pi) α :=
    (annularChordRadius_hasDerivAt hρ hr hα).hasDerivWithinAt
  have hi : IntegrableOn (fun α : ℝ => |annularChordSlope ρ r α| •
      annularChordDensity ρ r (annularChordRadius ρ r α)) (Ioo (0 : ℝ) Real.pi) :=
    (show IntegrableOn (fun _α : ℝ => (1 : ℝ)) (Ioo (0 : ℝ) Real.pi) from
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).congr_fun
      (fun α hα => (annularChordDensity_pullback hρ hr hα).symm) measurableSet_Ioo
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (annularChordDensity ρ r)
  rw [himage] at hiff
  refine ⟨hiff.mpr hi, ?_⟩
  have hJac := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (annularChordDensity ρ r)
  rw [himage] at hJac
  calc
    _ = ∫ α : ℝ in Ioo (0 : ℝ) Real.pi, |annularChordSlope ρ r α| •
        annularChordDensity ρ r (annularChordRadius ρ r α) := hJac
    _ = ∫ _α : ℝ in Ioo (0 : ℝ) Real.pi, (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Ioo (fun α hα => annularChordDensity_pullback hρ hr hα)
    _ = ∫ _α : ℝ in (0 : ℝ)..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
    _ = Real.pi := by simp

/-- The actual annular change of variables, including complex-valued radial
data and genuine integrability of the weighted density. -/
theorem annularChordChebyshev_integrable_and_integral (m : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn (fun s : ℝ => annularChordChebyshevKernel m ρ r s • v s)
        (Ioo |ρ - r| (ρ + r)) ∧
      (∫ α : ℝ in (0 : ℝ)..Real.pi,
        chebyshevTValue m (annularChordAngleArgument ρ r α) • v (annularChordRadius ρ r α)) =
        ∫ s : ℝ in Ioo |ρ - r| (ρ + r), annularChordChebyshevKernel m ρ r s • v s := by
  have himage := annularChordRadius_image hρ hr
  have hinj := ((annularChordRadius_strictAntiOn hρ hr).mono Ioo_subset_Icc_self).injOn
  have hderiv (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
      HasDerivWithinAt (annularChordRadius ρ r) (annularChordSlope ρ r α) (Ioo 0 Real.pi) α :=
    (annularChordRadius_hasDerivAt hρ hr hα).hasDerivWithinAt
  have hpull (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
      |annularChordSlope ρ r α| •
          (annularChordChebyshevKernel m ρ r (annularChordRadius ρ r α) • v (annularChordRadius ρ r α)) =
        chebyshevTValue m (annularChordAngleArgument ρ r α) • v (annularChordRadius ρ r α) := by
    rw [smul_smul]
    have hh := annularChordChebyshevKernel_pullback m hρ hr hα
    simp only [smul_eq_mul] at hh
    rw [hh]
  have hiPull := (annularChordAngleIntegrand_integrableOn m hρ hr hv).congr_fun
    (fun α hα => (hpull α hα).symm) measurableSet_Ioo
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun s : ℝ => annularChordChebyshevKernel m ρ r s • v s)
  rw [himage] at hiff
  refine ⟨hiff.mpr hiPull, ?_⟩
  have hJac := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun s : ℝ => annularChordChebyshevKernel m ρ r s • v s)
  rw [himage] at hJac
  symm
  calc
    _ = ∫ α : ℝ in Ioo (0 : ℝ) Real.pi, |annularChordSlope ρ r α| •
        (annularChordChebyshevKernel m ρ r (annularChordRadius ρ r α) • v (annularChordRadius ρ r α)) := hJac
    _ = ∫ α : ℝ in Ioo (0 : ℝ) Real.pi,
        chebyshevTValue m (annularChordAngleArgument ρ r α) • v (annularChordRadius ρ r α) :=
      setIntegral_congr_fun measurableSet_Ioo hpull
    _ = _ := by rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]

/-- The explicit form with the factor two outside the annular integral. -/
theorem integral_annularChord_chebyshev (m : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) {v : ℝ → ℂ} (hv : Continuous v) :
    (∫ α : ℝ in (0 : ℝ)..Real.pi,
      chebyshevTValue m ((ρ + r * Real.cos α) / annularChordRadius ρ r α) •
        v (annularChordRadius ρ r α)) =
      (2 : ℝ) • ∫ s : ℝ in Ioo |ρ - r| (ρ + r),
        (s * chebyshevTValue m ((s ^ 2 + ρ ^ 2 - r ^ 2) / (2 * s * ρ)) /
          Real.sqrt ((s ^ 2 - (ρ - r) ^ 2) * ((ρ + r) ^ 2 - s ^ 2))) • v s := by
  change (∫ α : ℝ in (0 : ℝ)..Real.pi,
    chebyshevTValue m (annularChordAngleArgument ρ r α) • v (annularChordRadius ρ r α)) = _
  rw [(annularChordChebyshev_integrable_and_integral m hρ hr hv).2,
    ← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    simp only [annularChordChebyshevKernel, annularChordDensity, annularChordArgument, smul_smul]
    congr 1
    ring)

end J0RadialUniqueness
