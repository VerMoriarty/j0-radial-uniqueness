import Solutions.J0RadialUniqueness.AnnularChordIntegral
import Solutions.J0RadialUniqueness.AnnularVolterraKernel

/-! Exact reduction of the actual annular chord integral to the weakly
singular Volterra kernel. The lower radial interval is removed using its
vanishing data and the fact that the cutting point has Lebesgue measure zero. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Interval

namespace J0RadialUniqueness

theorem annular_cut_lower_lt {r a p : ℝ} (hr : 0 < r) (hra : r < a)
    (hap : a < p) (hpa : p < a + r) : |p - 2 * r| < a := by
  apply abs_lt.mpr
  constructor <;> linarith

theorem annular_cut_mem_kernelDomain {r a p s : ℝ} (hr : 0 < r) (hra : r < a)
    (hap : a < p) (hpa : p < a + r) (hs : s ∈ Ioo a p) :
    (p, s) ∈ annularKernelDomain r := by
  exact ⟨by linarith, by linarith [hs.1], (annular_cut_lower_lt hr hra hap hpa).trans hs.1⟩

/-- The positive square-root factors on the genuine integration interval. -/
theorem annular_cut_sqrt_factors_pos {r a p s : ℝ} (hr : 0 < r) (hra : r < a)
    (hap : a < p) (hpa : p < a + r) (hs : s ∈ Ioo a p) :
    0 < Real.sqrt (p - s) ∧
      0 < Real.sqrt ((s ^ 2 - (p - 2 * r) ^ 2) * (p + s)) := by
  exact ⟨Real.sqrt_pos.mpr (sub_pos.mpr hs.2),
    Real.sqrt_pos.mpr (annularKernelDomain_denominator_pos hr
      (annular_cut_mem_kernelDomain hr hra hap hpa hs))⟩

/-- Factorization of the full annular square root, with the weak singularity
extracted only on the open interval where both factors are positive. -/
theorem annular_cut_discriminant_sqrt {r a p s : ℝ} (hr : 0 < r) (hra : r < a)
    (hap : a < p) (hpa : p < a + r) (hs : s ∈ Ioo a p) :
    Real.sqrt ((s ^ 2 - (p - 2 * r) ^ 2) * (p ^ 2 - s ^ 2)) =
      Real.sqrt (p - s) * Real.sqrt ((s ^ 2 - (p - 2 * r) ^ 2) * (p + s)) := by
  have he : (s ^ 2 - (p - 2 * r) ^ 2) * (p ^ 2 - s ^ 2) =
      (p - s) * ((s ^ 2 - (p - 2 * r) ^ 2) * (p + s)) := by ring
  rw [he, Real.sqrt_mul (sub_pos.mpr hs.2).le]

/-- The normalized chord kernel is precisely the actual Volterra kernel with
its explicit inverse square-root factor. -/
theorem annularChordChebyshevKernel_eq_volterra (m : ℕ) {r a p s : ℝ}
    (hr : 0 < r) (hra : r < a) (hap : a < p) (hpa : p < a + r) (hs : s ∈ Ioo a p) :
    (1 / Real.pi) * annularChordChebyshevKernel m (p - r) r s =
      (Real.sqrt (p - s))⁻¹ * annularVolterraKernel m r (p, s) := by
  obtain ⟨hroot, hden⟩ := annular_cut_sqrt_factors_pos hr hra hap hpa hs
  unfold annularChordChebyshevKernel annularChordDensity annularChordArgument annularVolterraKernel
  simp only [show p - r - r = p - 2 * r by ring, show p - r + r = p by ring]
  rw [annular_cut_discriminant_sqrt hr hra hap hpa hs]
  field_simp [hroot.ne', hden.ne', Real.pi_ne_zero] <;> ring

/-- The same identity written as the coefficient displayed in the radial
chord integral. -/
theorem annular_radial_coefficient_eq_volterra (m : ℕ) {r a p s : ℝ}
    (hr : 0 < r) (hra : r < a) (hap : a < p) (hpa : p < a + r) (hs : s ∈ Ioo a p) :
    (2 / Real.pi) * s * chebyshevTValue m
        ((s ^ 2 + (p - r) ^ 2 - r ^ 2) / (2 * s * (p - r))) /
      Real.sqrt ((s ^ 2 - (p - 2 * r) ^ 2) * (p ^ 2 - s ^ 2)) =
        (Real.sqrt (p - s))⁻¹ * annularVolterraKernel m r (p, s) := by
  have hh := annularChordChebyshevKernel_eq_volterra m hr hra hap hpa hs
  simp only [annularChordChebyshevKernel, annularChordDensity, annularChordArgument,
    show p - r - r = p - 2 * r by ring, show p - r + r = p by ring] at hh
  convert hh using 1 <;> ring

theorem annularChordChebyshev_smul_eq_volterra (m : ℕ) {r a p s : ℝ}
    (hr : 0 < r) (hra : r < a) (hap : a < p) (hpa : p < a + r) (hs : s ∈ Ioo a p)
    (w : ℂ) :
    (1 / Real.pi) • (annularChordChebyshevKernel m (p - r) r s • w) =
      (Real.sqrt (p - s))⁻¹ • ((annularVolterraKernel m r (p, s) : ℂ) * w) := by
  rw [smul_smul, Complex.real_smul,
    annularChordChebyshevKernel_eq_volterra m hr hra hap hpa hs]
  simp only [Complex.ofReal_mul, Complex.real_smul, mul_assoc]

/-- An open subinterval can be removed without requiring a value at the
cutting point. Its singleton is excluded by the actual Lebesgue AE statement. -/
theorem integral_Ioo_truncate_of_eq_zero {L a p : ℝ} (hLa : L < a) (hap : a < p)
    {f : ℝ → ℂ} (hzero : ∀ s ∈ Ioo L a, f s = 0) :
    (∫ s : ℝ in Ioo L p, f s) = ∫ s : ℝ in Ioo a p, f s := by
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
    (fun s hs => ⟨hLa.trans hs.1, hs.2⟩)
  filter_upwards [(volume : Measure ℝ).ae_ne a] with s hsa hs
  have hle : s ≤ a := by
    by_contra h
    exact hs.2 ⟨lt_of_not_ge h, hs.1.2⟩
  exact hzero s ⟨hs.1.1, lt_of_le_of_ne hle hsa⟩

def annularAbelIntegrand (m : ℕ) (r p : ℝ) (v : ℝ → ℂ) (s : ℝ) : ℂ :=
  (Real.sqrt (p - s))⁻¹ • ((annularVolterraKernel m r (p, s) : ℂ) * v s)

/-- Genuine integrability of the weakly singular integrand follows from the
proved chord Jacobian, with no separate regularity assumption on that density. -/
theorem annularAbelIntegrand_integrableOn (m : ℕ) {r a p : ℝ}
    (hr : 0 < r) (hra : r < a) (hap : a < p) (hpa : p < a + r)
    {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn (annularAbelIntegrand m r p v) (Ioo a p) := by
  have hρ : 0 < p - r := by linarith
  have hwhole := (annularChordChebyshev_integrable_and_integral m hρ hr hv).1
  have hwhole' : IntegrableOn (fun s : ℝ => annularChordChebyshevKernel m (p - r) r s • v s)
      (Ioo |p - 2 * r| p) := by
    simpa only [show p - r - r = p - 2 * r by ring, show p - r + r = p by ring] using hwhole
  have hsub : Ioo a p ⊆ Ioo |p - 2 * r| p :=
    fun s hs => ⟨(annular_cut_lower_lt hr hra hap hpa).trans hs.1, hs.2⟩
  have hi : IntegrableOn (fun s : ℝ => (1 / Real.pi) •
      (annularChordChebyshevKernel m (p - r) r s • v s)) (Ioo a p) :=
    (hwhole'.mono_set hsub).smul (1 / Real.pi : ℝ)
  exact hi.congr_fun (fun s hs => annularChordChebyshev_smul_eq_volterra m hr hra hap hpa hs (v s))
    measurableSet_Ioo

theorem annularAbelIntegrand_intervalIntegrable (m : ℕ) {r a p : ℝ}
    (hr : 0 < r) (hra : r < a) (hap : a < p) (hpa : p < a + r)
    {v : ℝ → ℂ} (hv : Continuous v) :
    IntervalIntegrable (annularAbelIntegrand m r p v) volume a p :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le hap.le).mpr
    (annularAbelIntegrand_integrableOn m hr hra hap hpa hv)

/-- The actual normalized angular integral, truncated by its vanishing radial
data, equals the weakly singular Volterra integral. No endpoint value at `a`
is imposed. -/
theorem annularChord_integral_eq_abel (m : ℕ) {r a p : ℝ}
    (hr : 0 < r) (hra : r < a) (hap : a < p) (hpa : p < a + r)
    {v : ℝ → ℂ} (hv : Continuous v)
    (hzero : ∀ s ∈ Ioo |p - 2 * r| a, v s = 0) :
    (1 / Real.pi) • (∫ α : ℝ in (0 : ℝ)..Real.pi,
      chebyshevTValue m (annularChordAngleArgument (p - r) r α) •
        v (annularChordRadius (p - r) r α)) =
      ∫ s : ℝ in a..p, annularAbelIntegrand m r p v s := by
  have hρ : 0 < p - r := by linarith
  have hangle := (annularChordChebyshev_integrable_and_integral m hρ hr hv).2
  have hangle' : (∫ α : ℝ in (0 : ℝ)..Real.pi,
      chebyshevTValue m (annularChordAngleArgument (p - r) r α) •
        v (annularChordRadius (p - r) r α)) =
      ∫ s : ℝ in Ioo |p - 2 * r| p, annularChordChebyshevKernel m (p - r) r s • v s := by
    simpa only [show p - r - r = p - 2 * r by ring, show p - r + r = p by ring] using hangle
  have htruncate : (∫ s : ℝ in Ioo |p - 2 * r| p,
      annularChordChebyshevKernel m (p - r) r s • v s) =
      ∫ s : ℝ in Ioo a p, annularChordChebyshevKernel m (p - r) r s • v s :=
    integral_Ioo_truncate_of_eq_zero (annular_cut_lower_lt hr hra hap hpa) hap
      (fun s hs => by rw [hzero s hs, smul_zero])
  calc
    _ = (1 / Real.pi) • ∫ s : ℝ in Ioo a p,
        annularChordChebyshevKernel m (p - r) r s • v s := by rw [hangle', htruncate]
    _ = ∫ s : ℝ in Ioo a p, (1 / Real.pi) •
        (annularChordChebyshevKernel m (p - r) r s • v s) := (integral_smul _ _).symm
    _ = ∫ s : ℝ in Ioo a p, annularAbelIntegrand m r p v s :=
      setIntegral_congr_fun measurableSet_Ioo
        (fun s hs => annularChordChebyshev_smul_eq_volterra m hr hra hap hpa hs (v s))
    _ = _ := by rw [intervalIntegral.integral_of_le hap.le, integral_Ioc_eq_integral_Ioo]

end J0RadialUniqueness
