import Solutions.J0RadialUniqueness.AbelAveragedKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual angular substitution and singular-integrability foundation for
the second Abel transform. The sin² substitution is used on the open angular
interval. Full singular-product integrability is proved before any Fubini
exchange: the inner norm integral is identified with a continuous angular
average and the product-integrability criterion is then applied.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace J0RadialUniqueness

def abelAngleScalar (t s θ : ℝ) : ℝ := s + (t - s) * Real.sin θ ^ 2

def abelAngleScalarSlope (t s θ : ℝ) : ℝ :=
  2 * (t - s) * Real.sin θ * Real.cos θ

def abelBetaDensity (t s p : ℝ) : ℝ :=
  (Real.sqrt (t - p))⁻¹ * (Real.sqrt (p - s))⁻¹

theorem abelBetaDensity_nonneg (t s p : ℝ) : 0 ≤ abelBetaDensity t s p :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem continuous_abelAngleScalar (t s : ℝ) : Continuous (abelAngleScalar t s) := by
  unfold abelAngleScalar
  fun_prop

theorem abelAngleScalar_hasDerivAt (t s θ : ℝ) :
    HasDerivAt (abelAngleScalar t s) (abelAngleScalarSlope t s θ) θ := by
  have hh := (((Real.hasDerivAt_sin θ).pow 2).const_mul (t - s)).const_add s
  convert! hh using 1 <;>
    simp only [abelAngleScalar, abelAngleScalarSlope, Pi.pow_apply] <;>
    first | (funext u; ring) | ring

theorem abelAngleScalarSlope_pos {t s θ : ℝ} (hst : s < t)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) : 0 < abelAngleScalarSlope t s θ := by
  rcases hθ with ⟨hθ0, hθπ⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  unfold abelAngleScalarSlope
  positivity

theorem abelAngleScalar_strictMonoOn {t s : ℝ} (hst : s < t) :
    StrictMonoOn (abelAngleScalar t s) (Icc (0 : ℝ) (Real.pi / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (Real.pi / 2))
    (continuous_abelAngleScalar t s).continuousOn
  intro θ hθ
  rw [interior_Icc] at hθ
  rw [(abelAngleScalar_hasDerivAt t s θ).deriv]
  exact abelAngleScalarSlope_pos hst hθ

theorem abelAngleScalar_image {t s : ℝ} (hst : s < t) :
    abelAngleScalar t s '' Ioo (0 : ℝ) (Real.pi / 2) = Ioo s t := by
  have hzero : abelAngleScalar t s 0 = s := by simp [abelAngleScalar]
  have hhalf : abelAngleScalar t s (Real.pi / 2) = t := by
    simp only [abelAngleScalar, Real.sin_pi_div_two, one_pow, mul_one]
    ring
  have hi := (continuous_abelAngleScalar t s).continuousOn.image_Ioo_of_strictMonoOn
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity) (abelAngleScalar_strictMonoOn hst)
  simpa only [hzero, hhalf] using hi

/-- The entire singular Jacobian cancels to the constant two at every interior
angle. Neither singular endpoint is used in this calculation. -/
theorem abelBetaDensity_angular_jacobian {t s θ : ℝ} (hst : s < t)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    |abelAngleScalarSlope t s θ| * abelBetaDensity t s (abelAngleScalar t s θ) = 2 := by
  rcases hθ with ⟨hθ0, hθπ⟩
  have hd : 0 < t - s := sub_pos.mpr hst
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  have htrig := congrArg (fun u : ℝ => (t - s) * u) (Real.sin_sq_add_cos_sq θ)
  have htp : t - abelAngleScalar t s θ = (t - s) * Real.cos θ ^ 2 := by
    dsimp only [abelAngleScalar]
    nlinarith only [htrig]
  have hps : abelAngleScalar t s θ - s = (t - s) * Real.sin θ ^ 2 := by
    dsimp only [abelAngleScalar]
    ring
  have hprodpos : 0 < (t - s) * Real.sin θ * Real.cos θ := by positivity
  have hden : Real.sqrt (t - abelAngleScalar t s θ) *
      Real.sqrt (abelAngleScalar t s θ - s) = (t - s) * Real.sin θ * Real.cos θ := by
    calc
      _ = Real.sqrt ((t - abelAngleScalar t s θ) * (abelAngleScalar t s θ - s)) :=
        (Real.sqrt_mul (by rw [htp]; positivity) _).symm
      _ = Real.sqrt (((t - s) * Real.sin θ * Real.cos θ) ^ 2) := by
        congr 1
        rw [htp, hps]
        ring
      _ = _ := Real.sqrt_sq hprodpos.le
  rw [abs_of_pos (abelAngleScalarSlope_pos hst ⟨hθ0, hθπ⟩)]
  unfold abelBetaDensity
  rw [← mul_inv, hden]
  unfold abelAngleScalarSlope
  field_simp [hd.ne', hsin.ne', hcos.ne']

section WeightedSubstitution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Integrability and the exact sin² change of variables for a continuous
Banach-valued numerator, including both inverse-square-root endpoints. -/
theorem abelBetaDensity_weighted_integrable_and_integral {t s : ℝ} (hst : s < t)
    {h : ℝ → V} (hh : Continuous h) :
    IntegrableOn (fun p : ℝ => abelBetaDensity t s p • h p) (Ioo s t) ∧
      (∫ p : ℝ in Ioo s t, abelBetaDensity t s p • h p) =
        (2 : ℝ) • ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), h (abelAngleScalar t s θ) := by
  have himage := abelAngleScalar_image hst
  have hinj : InjOn (abelAngleScalar t s) (Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((abelAngleScalar_strictMonoOn hst).mono Ioo_subset_Icc_self).injOn
  have hd (θ : ℝ) (_hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
      HasDerivWithinAt (abelAngleScalar t s) (abelAngleScalarSlope t s θ)
        (Ioo (0 : ℝ) (Real.pi / 2)) θ :=
    (abelAngleScalar_hasDerivAt t s θ).hasDerivWithinAt
  have hpull (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
      |abelAngleScalarSlope t s θ| •
          (abelBetaDensity t s (abelAngleScalar t s θ) • h (abelAngleScalar t s θ)) =
        (2 : ℝ) • h (abelAngleScalar t s θ) := by
    rw [smul_smul, abelBetaDensity_angular_jacobian hst hθ]
  have hc : Continuous (fun θ : ℝ => (2 : ℝ) • h (abelAngleScalar t s θ)) :=
    (hh.comp (continuous_abelAngleScalar t s)).const_smul 2
  have hiC : IntegrableOn (fun θ : ℝ => (2 : ℝ) • h (abelAngleScalar t s θ))
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ Real.pi / 2 by positivity)).mp
        (hc.intervalIntegrable (μ := volume) 0 (Real.pi / 2))
    exact hi.mono_set Ioo_subset_Ioc_self
  have hiPull : IntegrableOn (fun θ : ℝ => |abelAngleScalarSlope t s θ| •
      (abelBetaDensity t s (abelAngleScalar t s θ) • h (abelAngleScalar t s θ)))
      (Ioo (0 : ℝ) (Real.pi / 2)) :=
    hiC.congr_fun (fun θ hθ => (hpull θ hθ).symm) measurableSet_Ioo
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo hd hinj (fun p : ℝ => abelBetaDensity t s p • h p)
  rw [himage] at hiff
  refine ⟨hiff.mpr hiPull, ?_⟩
  have hjac := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hd hinj (fun p : ℝ => abelBetaDensity t s p • h p)
  rw [himage] at hjac
  calc
    _ = ∫ θ : ℝ in Ioo (0 : ℝ) (Real.pi / 2), |abelAngleScalarSlope t s θ| •
        (abelBetaDensity t s (abelAngleScalar t s θ) • h (abelAngleScalar t s θ)) := hjac
    _ = ∫ θ : ℝ in Ioo (0 : ℝ) (Real.pi / 2), (2 : ℝ) • h (abelAngleScalar t s θ) :=
      setIntegral_congr_fun measurableSet_Ioo hpull
    _ = ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), (2 : ℝ) • h (abelAngleScalar t s θ) := by
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity),
        integral_Ioc_eq_integral_Ioo]
    _ = _ := intervalIntegral.integral_smul _ _

end WeightedSubstitution

theorem abelBetaDensity_integrable_and_integral {t s : ℝ} (hst : s < t) :
    IntegrableOn (abelBetaDensity t s) (Ioo s t) ∧
      (∫ p : ℝ in Ioo s t, abelBetaDensity t s p) = Real.pi := by
  have hh := abelBetaDensity_weighted_integrable_and_integral hst
    (h := fun _ : ℝ => (1 : ℝ)) continuous_const
  have hi : IntegrableOn (abelBetaDensity t s) (Ioo s t) := by
    simpa only [smul_eq_mul, mul_one] using hh.1
  refine ⟨hi, ?_⟩
  have he := hh.2
  simp only [smul_eq_mul, mul_one, intervalIntegral.integral_const, sub_zero] at he
  convert! he using 1 <;> ring

def abelTriangleIntegrand (K : ℝ × ℝ → ℂ) (v : ℝ → ℂ) (t s p : ℝ) : ℂ :=
  if s < p ∧ p < t then abelBetaDensity t s p • (K (p, s) * v s) else 0

theorem abelTriangleIntegrand_eq_indicator (K : ℝ × ℝ → ℂ) (v : ℝ → ℂ) (t s : ℝ) :
    (fun p : ℝ => abelTriangleIntegrand K v t s p) =
      (Ioo s t).indicator (fun p : ℝ => abelBetaDensity t s p • (K (p, s) * v s)) := by
  funext p
  by_cases hp : s < p ∧ p < t
  · have hpSet : p ∈ Ioo s t := hp
    simp only [abelTriangleIntegrand, if_pos hp, indicator_of_mem hpSet]
  · have hpSet : p ∉ Ioo s t := hp
    simp only [abelTriangleIntegrand, if_neg hp, indicator_of_notMem hpSet]

theorem measurable_abelTriangleIntegrand {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) (t : ℝ) :
    Measurable (fun q : ℝ × ℝ => abelTriangleIntegrand K v t q.1 q.2) := by
  have hset : MeasurableSet {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 < t} :=
    ((isOpen_lt continuous_fst continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)).measurableSet
  have hb : Measurable (fun q : ℝ × ℝ => abelBetaDensity t q.1 q.2) := by
    unfold abelBetaDensity
    exact ((Real.continuous_sqrt.measurable.comp
      (measurable_const.sub measurable_snd)).inv).mul
      ((Real.continuous_sqrt.measurable.comp (measurable_snd.sub measurable_fst)).inv)
  have hf : Continuous (fun q : ℝ × ℝ => K (q.2, q.1) * v q.1) :=
    (hK.comp (continuous_snd.prodMk continuous_fst)).mul (hv.comp continuous_fst)
  exact Measurable.ite hset (hb.smul hf.measurable) measurable_const

def abelAveragedNormKernel (K : ℝ × ℝ → ℂ) (v : ℝ → ℂ) (t s : ℝ) : ℝ :=
  2 * ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), ‖K (abelAnglePoint t s θ) * v s‖

theorem continuous_abelAveragedNormKernel {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) (t : ℝ) : Continuous (abelAveragedNormKernel K v t) := by
  have hp : Continuous (fun q : ℝ × ℝ => abelAnglePoint t q.1 q.2) := by
    unfold abelAnglePoint
    fun_prop
  have hc : Continuous (fun q : ℝ × ℝ => ‖K (abelAnglePoint t q.1 q.2) * v q.1‖) :=
    ((hK.comp hp).mul (hv.comp continuous_fst)).norm
  have hi : Continuous (fun s : ℝ => ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
      ‖K (abelAnglePoint t s θ) * v s‖) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (s θ : ℝ) => ‖K (abelAnglePoint t s θ) * v s‖) ?_ 0 (Real.pi / 2)
    convert! hc using 1 <;> rfl
  exact hi.const_mul 2

theorem abelTriangleIntegrand_fiber_integrable {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) {t s : ℝ} (hst : s < t) :
    Integrable (fun p : ℝ => abelTriangleIntegrand K v t s p) := by
  have hh : Continuous (fun p : ℝ => K (p, s) * v s) :=
    (hK.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  rw [abelTriangleIntegrand_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Ioo).mpr
    (abelBetaDensity_weighted_integrable_and_integral hst hh).1

theorem integral_norm_abelTriangleIntegrand {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) {t s : ℝ} (hst : s < t) :
    (∫ p : ℝ, ‖abelTriangleIntegrand K v t s p‖) = abelAveragedNormKernel K v t s := by
  have hh : Continuous (fun p : ℝ => ‖K (p, s) * v s‖) :=
    ((hK.comp (continuous_id.prodMk continuous_const)).mul continuous_const).norm
  have he : (fun p : ℝ => ‖abelTriangleIntegrand K v t s p‖) =
      (Ioo s t).indicator (fun p : ℝ => abelBetaDensity t s p • ‖K (p, s) * v s‖) := by
    funext p
    by_cases hp : p ∈ Ioo s t
    · have hp' : s < p ∧ p < t := hp
      simp only [abelTriangleIntegrand, if_pos hp', indicator_of_mem hp, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (abelBetaDensity_nonneg t s p), smul_eq_mul]
    · have hp' : ¬ (s < p ∧ p < t) := hp
      simp only [abelTriangleIntegrand, if_neg hp', indicator_of_notMem hp, norm_zero]
  rw [he, integral_indicator measurableSet_Ioo]
  have hval := (abelBetaDensity_weighted_integrable_and_integral hst hh).2
  simpa only [abelAveragedNormKernel, abelAnglePoint, abelAngleScalar, smul_eq_mul] using hval

/-- The complete singular triangle integrand is genuinely L¹. The proof first
computes its inner norm integral by the actual one-dimensional Jacobian, then
uses product integrability. Thus the later Fubini step has an L¹ certificate. -/
theorem abelTriangleIntegrand_integrable {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) {a t : ℝ} (hat : a < t) :
    Integrable (fun q : ℝ × ℝ => abelTriangleIntegrand K v t q.1 q.2)
      ((volume.restrict (Ioo a t)).prod volume) := by
  have hm := (measurable_abelTriangleIntegrand hK hv t).stronglyMeasurable.aestronglyMeasurable
    (μ := (volume.restrict (Ioo a t)).prod volume)
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact abelTriangleIntegrand_fiber_integrable hK hv hs.2
  · have hc := continuous_abelAveragedNormKernel hK hv t
    have hi : IntegrableOn (abelAveragedNormKernel K v t) (Ioo a t) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat.le).mp
        (hc.intervalIntegrable (μ := volume) a t)).mono_set Ioo_subset_Ioc_self
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (integral_norm_abelTriangleIntegrand hK hv hs.2).symm

/-- The inner spectral numerator is precisely the actual averaged Abel kernel,
not a separately assumed composition kernel. -/
theorem integral_abelTriangleIntegrand {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) {t s : ℝ} (hst : s < t) :
    (∫ p : ℝ, abelTriangleIntegrand K v t s p) = abelAveragedKernel K t s * v s := by
  have hh : Continuous (fun p : ℝ => K (p, s) * v s) :=
    (hK.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  rw [abelTriangleIntegrand_eq_indicator, integral_indicator measurableSet_Ioo]
  rw [(abelBetaDensity_weighted_integrable_and_integral hst hh).2]
  simp only [Complex.real_smul, Complex.ofReal_ofNat]
  change (2 : ℂ) * (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), K (abelAnglePoint t s θ) * v s) =
    ((2 : ℂ) * ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), K (abelAnglePoint t s θ)) * v s
  rw [intervalIntegral.integral_mul_const]
  ring

def abelHalfTransform (K : ℝ × ℝ → ℂ) (v : ℝ → ℂ) (a p : ℝ) : ℂ :=
  ∫ s : ℝ in Ioo a p, (Real.sqrt (p - s))⁻¹ • (K (p, s) * v s)

theorem integral_abelTriangleIntegrand_restrict_first {K : ℝ × ℝ → ℂ}
    {v : ℝ → ℂ} {a t p : ℝ} (hp : p ∈ Ioo a t) :
    (∫ s : ℝ in Ioo a t, abelTriangleIntegrand K v t s p) =
      (Real.sqrt (t - p))⁻¹ • abelHalfTransform K v a p := by
  have he : (fun s : ℝ => abelTriangleIntegrand K v t s p) =
      (Iio p).indicator (fun s : ℝ => abelBetaDensity t s p • (K (p, s) * v s)) := by
    funext s
    by_cases hsp : s < p <;> simp [abelTriangleIntegrand, hsp, hp.2]
  have hinter : Iio p ∩ Ioo a t = Ioo a p := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · intro hs
      exact ⟨hs.2.1, hs.1⟩
    · intro hs
      exact ⟨hs.2, hs.1, hs.2.trans hp.2⟩
  rw [he, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, hinter]
  unfold abelHalfTransform
  rw [← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by simp only [abelBetaDensity, smul_smul])

theorem integral_abelTriangleIntegrand_restrict_first_zero {K : ℝ × ℝ → ℂ}
    {v : ℝ → ℂ} {a t p : ℝ} (hp : p ∉ Ioo a t) :
    (∫ s : ℝ in Ioo a t, abelTriangleIntegrand K v t s p) = 0 := by
  calc
    _ = ∫ s : ℝ in Ioo a t, (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      have hnot : ¬(s < p ∧ p < t) := by
        intro hh
        exact hp ⟨hs.1.trans hh.1, hh.2⟩
      exact if_neg hnot
    _ = 0 := integral_zero _ _

theorem abelTriangleIntegrand_reversed_integral_eq_indicator
    (K : ℝ × ℝ → ℂ) (v : ℝ → ℂ) (a t : ℝ) :
    (fun p : ℝ => ∫ s : ℝ in Ioo a t, abelTriangleIntegrand K v t s p) =
      (Ioo a t).indicator (fun p : ℝ => (Real.sqrt (t - p))⁻¹ • abelHalfTransform K v a p) := by
  funext p
  by_cases hp : p ∈ Ioo a t
  · rw [indicator_of_mem hp]
    exact integral_abelTriangleIntegrand_restrict_first hp
  · rw [indicator_of_notMem hp]
    exact integral_abelTriangleIntegrand_restrict_first_zero hp

/-- The complete second-Abel integrand on its natural open interval is L¹,
deduced from the already established L¹ singular triangle. -/
theorem abelSecondTransform_integrable {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) {a t : ℝ} (hat : a < t) :
    IntegrableOn (fun p : ℝ => (Real.sqrt (t - p))⁻¹ • abelHalfTransform K v a p) (Ioo a t) := by
  have hi := (abelTriangleIntegrand_integrable hK hv hat).integral_prod_right
  rw [abelTriangleIntegrand_reversed_integral_eq_indicator K v a t] at hi
  exact (integrable_indicator_iff measurableSet_Ioo).mp hi

/-- Fubini is applied only after the actual singular triangle has been proved
integrable. Its inner integral is the proved angularly averaged kernel. -/
theorem abelSecondTransform_setIntegral {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) {a t : ℝ} (hat : a < t) :
    (∫ p : ℝ in Ioo a t, (Real.sqrt (t - p))⁻¹ • abelHalfTransform K v a p) =
      ∫ s : ℝ in Ioo a t, abelAveragedKernel K t s * v s := by
  have hF := abelTriangleIntegrand_integrable hK hv hat
  have hswap := (integral_integral_swap
    (f := fun s p : ℝ => abelTriangleIntegrand K v t s p) hF).symm
  rw [abelTriangleIntegrand_reversed_integral_eq_indicator K v a t,
    integral_indicator measurableSet_Ioo] at hswap
  calc
    _ = ∫ s : ℝ in Ioo a t, ∫ p : ℝ, abelTriangleIntegrand K v t s p := hswap
    _ = _ := setIntegral_congr_fun measurableSet_Ioo
      (fun s hs => integral_abelTriangleIntegrand hK hv hs.2)

/-- The original iterated interval-integral form. Endpoint values are replaced
only through the actual zero-measure Ioc/Ioo identities. -/
theorem abelSecondTransform_intervalIntegral {K : ℝ × ℝ → ℂ} (hK : Continuous K)
    {v : ℝ → ℂ} (hv : Continuous v) {a t : ℝ} (hat : a < t) :
    (∫ p : ℝ in a..t, (Real.sqrt (t - p))⁻¹ •
      (∫ s : ℝ in a..p, (Real.sqrt (p - s))⁻¹ • (K (p, s) * v s))) =
      ∫ s : ℝ in a..t, abelAveragedKernel K t s * v s := by
  have he : (∫ p : ℝ in a..t, (Real.sqrt (t - p))⁻¹ •
      (∫ s : ℝ in a..p, (Real.sqrt (p - s))⁻¹ • (K (p, s) * v s))) =
      ∫ p : ℝ in Ioo a t, (Real.sqrt (t - p))⁻¹ • abelHalfTransform K v a p := by
    rw [intervalIntegral.integral_of_le hat.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro p hp
    unfold abelHalfTransform
    dsimp only
    rw [intervalIntegral.integral_of_le hp.1.le, integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ p : ℝ in Ioo a t, (Real.sqrt (t - p))⁻¹ • abelHalfTransform K v a p := he
    _ = ∫ s : ℝ in Ioo a t, abelAveragedKernel K t s * v s :=
      abelSecondTransform_setIntegral hK hv hat
    _ = _ := by
      rw [intervalIntegral.integral_of_le hat.le, integral_Ioc_eq_integral_Ioo]

end J0RadialUniqueness
