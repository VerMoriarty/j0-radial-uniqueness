import Solutions.J0RadialUniqueness.ResolventQuotientEstimates
import Solutions.J0RadialUniqueness.ResolventSymmetry
import Solutions.J0RadialUniqueness.BesselBiorthogonality
import Solutions.J0RadialUniqueness.LocalResolventQuotient

/-! The actual spectral transform of a continuous radial profile. Its radial
integral is identified with the genuine compact planar B convolution. The
proved T identity supplies parameter analyticity, including zero, and the
principal-sector estimate is the actual B convolution estimate. The optional
zero-division result is explicitly an intermediate theorem: no completeness
or vanishing premise is asserted for arbitrary profiles. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval

namespace J0RadialUniqueness

def radialProfileLift (p : ℝ → ℂ) (x : Plane) : ℂ := p ‖x‖

theorem continuous_radialProfileLift {p : ℝ → ℂ} (hp : Continuous p) :
    Continuous (radialProfileLift p) := hp.comp continuous_norm

theorem circularMean_radialProfileLift_zero (p : ℝ → ℂ) (s : ℝ) :
    circularMean (radialProfileLift p) s 0 = p |s| := by
  unfold circularMean
  simp only [radialProfileLift, zero_add, norm_smul, Real.norm_eq_abs,
    norm_circleDirection, mul_one]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_smul]
  rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul]

def radialBProfileTransform (r : ℝ) (p : ℝ → ℂ) (lam : ℂ) : ℂ :=
  ∫ s : ℝ in (0 : ℝ)..r,
    (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s * p s

theorem radialBProfileTransform_intervalIntegrable {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) (lam : ℂ) :
    IntervalIntegrable (fun s : ℝ =>
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s * p s) volume 0 r :=
  ((continuous_const.mul (continuous_helmholtzResolventWeightedB hr lam)).mul hp).intervalIntegrable 0 r

/-- The profile transform is exactly the planar convolution at the origin.
The imported polar theorem already proves both planar and polar L1 before
the exchange of integrals. -/
theorem radialBProfileTransform_eq_planarConvolution {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) (lam : ℂ) :
    radialBProfileTransform r p lam =
      planarResolventBConvolution r (radialProfileLift p) 0 lam := by
  unfold planarResolventBConvolution planarHelmholtzResolventB
  rw [compactRadialComplexKernel_integral_eq_radial hr
    (measurable_helmholtzResolventB r lam)
    (intervalIntegrable_weighted_helmholtzResolventB hr lam)
    (continuous_radialProfileLift hp) 0]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by
    rw [uIcc_of_le hr.le] at hs
    exact hs.1
  dsimp only
  rw [circularMean_radialProfileLift_zero, abs_of_nonneg hs0,
    helmholtzResolventWeightedB_eq]
  ring

/-- The actual identity gives an entire formula without dividing by the
spectral parameter, so the singular-looking parameter zero is included. -/
theorem radialBProfileTransform_eq_green_sub_T {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) (lam : ℂ) :
    radialBProfileTransform r p lam =
      localConvolution (planarGreenKernel r) (radialProfileLift p) 0 -
        lam ^ 2 * planarResolventTConvolution r (radialProfileLift p) 0 lam := by
  rw [radialBProfileTransform_eq_planarConvolution hr hp]
  have hh := planarResolventTConvolution_mul_parameter_sq hr
    (continuous_radialProfileLift hp) (0 : Plane) lam
  linear_combination hh

@[simp] theorem radialBProfileTransform_zero_parameter {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) :
    radialBProfileTransform r p 0 =
      localConvolution (planarGreenKernel r) (radialProfileLift p) 0 := by
  rw [radialBProfileTransform_eq_green_sub_T hr hp]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_zero]

theorem radialBProfileTransform_analyticAt {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) (lam : ℂ) :
    AnalyticAt ℂ (radialBProfileTransform r p) lam := by
  have he : radialBProfileTransform r p = fun z : ℂ =>
      localConvolution (planarGreenKernel r) (radialProfileLift p) 0 -
        z ^ 2 * planarResolventTConvolution r (radialProfileLift p) 0 z :=
    funext (radialBProfileTransform_eq_green_sub_T hr hp)
  rw [he]
  exact analyticAt_const.sub ((analyticAt_id.pow 2).mul
    (planarResolventTConvolution_analyticAt hr (continuous_radialProfileLift hp) 0 lam))

theorem radialBProfileTransform_differentiable {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) : Differentiable ℂ (radialBProfileTransform r p) :=
  fun lam => (radialBProfileTransform_analyticAt hr hp lam).differentiableAt

@[simp] theorem radialBProfileTransform_neg (r : ℝ) (p : ℝ → ℂ) (lam : ℂ) :
    radialBProfileTransform r p (-lam) = radialBProfileTransform r p lam := by
  unfold radialBProfileTransform
  simp only [helmholtzResolventWeightedB_eq, helmholtzResolventB_neg]

/-- The bound in the principal sector is inherited from the actual compact B
action, with a constant depending on the fixed continuous radial profile. -/
theorem radialBProfileTransform_principal_bound {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ, ClosedPrincipalSector lam → 1 ≤ ‖lam‖ →
      ‖radialBProfileTransform r p lam‖ ≤ C * Real.exp (r * lam.im) / ‖lam‖ := by
  obtain ⟨C, hC, hB⟩ := resolventB_principal_convolution_bound
    (continuous_radialProfileLift hp) (0 : Plane) hr
  refine ⟨C, hC, fun lam hlam hL => ?_⟩
  rw [radialBProfileTransform_eq_planarConvolution hr hp]
  exact hB lam hlam hL

theorem unit_radialBProfileTransform_principal_bound {p : ℝ → ℂ} (hp : Continuous p) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ, ClosedPrincipalSector lam → 1 ≤ ‖lam‖ →
      ‖radialBProfileTransform 1 p lam‖ ≤ C * Real.exp lam.im / ‖lam‖ := by
  simpa only [one_mul] using
    radialBProfileTransform_principal_bound (by norm_num : (0 : ℝ) < 1) hp

/-- Global order-one growth follows from the actual entire T action. The
quadratic factor in the identity is absorbed into exp(2‖lam‖). -/
theorem radialBProfileTransform_uniform_exp_bound {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ,
      ‖radialBProfileTransform r p lam‖ ≤ C * Real.exp ((2 * r + 2) * ‖lam‖) := by
  obtain ⟨A, hA, hT⟩ := planarResolventTConvolution_uniform_exp_bound hr
    (continuous_radialProfileLift hp) (0 : Plane)
  let G : ℂ := localConvolution (planarGreenKernel r) (radialProfileLift p) 0
  refine ⟨‖G‖ + A, by positivity, fun lam => ?_⟩
  have hLexp : ‖lam‖ ≤ Real.exp ‖lam‖ := by
    linarith only [Real.add_one_le_exp ‖lam‖]
  have hsq : ‖lam‖ ^ 2 ≤ (Real.exp ‖lam‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mpr hLexp
  have hexp : (Real.exp ‖lam‖) ^ 2 * Real.exp (2 * r * ‖lam‖) =
      Real.exp ((2 * r + 2) * ‖lam‖) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have heone : 1 ≤ Real.exp ((2 * r + 2) * ‖lam‖) := by
    rw [Real.one_le_exp_iff]
    positivity
  rw [radialBProfileTransform_eq_green_sub_T hr hp]
  calc
    _ ≤ ‖G‖ + ‖lam ^ 2 * planarResolventTConvolution r (radialProfileLift p) 0 lam‖ :=
      norm_sub_le _ _
    _ ≤ ‖G‖ + ‖lam‖ ^ 2 * (A * Real.exp (2 * r * ‖lam‖)) := by
      rw [norm_mul, norm_pow]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hT lam) (sq_nonneg _))
    _ ≤ ‖G‖ + (Real.exp ‖lam‖) ^ 2 * (A * Real.exp (2 * r * ‖lam‖)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq
        (mul_nonneg hA.le (Real.exp_pos _).le))
    _ = ‖G‖ + A * Real.exp ((2 * r + 2) * ‖lam‖) := by
      rw [show (Real.exp ‖lam‖) ^ 2 * (A * Real.exp (2 * r * ‖lam‖)) =
        A * ((Real.exp ‖lam‖) ^ 2 * Real.exp (2 * r * ‖lam‖)) by ring, hexp]
    _ ≤ (‖G‖ + A) * Real.exp ((2 * r + 2) * ‖lam‖) := by
      nlinarith only [mul_le_mul_of_nonneg_left heone (norm_nonneg G)]

/-- The companion-mode pairing and the B transform differ by this exact scalar.
The identity is valid for every profile, without a root or completeness input. -/
theorem volchkovDualMode_profile_pairing (p : ℝ → ℂ) (lam : ℂ) :
    (∫ s : ℝ in (0 : ℝ)..1, p s * volchkovDualMode lam s) =
      (2 * lam / (Real.pi : ℂ)) * radialBProfileTransform 1 p lam := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold radialBProfileTransform
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [volchkovDualMode]
  field_simp [hpi] <;> ring

def radialBProfileQuotient (r : ℝ) (p : ℝ → ℂ) : ℂ → ℂ :=
  simpleZeroQuotient (radialBProfileTransform r p) (helmholtzResolventMass r)

/-- An explicitly conditional intermediate division theorem. The hypothesis is
the vanishing of this particular actual transform at the actual mass roots;
it is not an assertion that arbitrary profile coefficients vanish. -/
theorem radialBProfileQuotient_analyticAt_of_root_vanishing {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p)
    (hv : ∀ lam : ℂ, helmholtzResolventMass r lam = 0 → radialBProfileTransform r p lam = 0)
    (lam : ℂ) : AnalyticAt ℂ (radialBProfileQuotient r p) lam :=
  simpleZeroQuotient_analyticAt (radialBProfileTransform_differentiable hr hp)
    (fun z => (helmholtzResolventMass_parameter_analyticAt r z).differentiableAt)
    hv (fun _ hroot => helmholtzResolventMass_deriv_ne_zero_at_root hr hroot) lam

theorem radialBProfileQuotient_factorization_of_root_vanishing {r : ℝ} (hr : 0 < r)
    {p : ℝ → ℂ} (hp : Continuous p)
    (hv : ∀ lam : ℂ, helmholtzResolventMass r lam = 0 → radialBProfileTransform r p lam = 0)
    (lam : ℂ) : radialBProfileTransform r p lam =
      helmholtzResolventMass r lam * radialBProfileQuotient r p lam :=
  simpleZeroQuotient_factorization (f := radialBProfileTransform r p)
    (g := helmholtzResolventMass r) hv lam

end J0RadialUniqueness
