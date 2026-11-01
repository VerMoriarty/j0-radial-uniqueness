import Solutions.J0RadialUniqueness.ResolventParameterAnalytic
import Solutions.J0RadialUniqueness.CircularBesselIntegral
import Solutions.J0RadialUniqueness.SpectralExponential
import Solutions.J0RadialUniqueness.SimpleOnePoints
import Mathlib.Tactic

/-! Actual Bessel root modes and a boundary-conditioned logarithmic companion.

The companion is defined by the proved F/harmonic-number series resolvent,
not by an assumed Neumann-function identity. Its pairing follows from the
actual radial Green identity applied to exp(-i μ x₀). Differentiating that
identity gives the diagonal normalizer. No completeness assertion is made.
Identifying the companion with a conventionally named Y₀ combination is a
separate, unnecessary naming bridge for the identities proved here. -/

noncomputable section

open Set MeasureTheory Filter Laplacian
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

def besselResolventPairing (r : ℝ) (lam mu : ℂ) : ℂ :=
  ∫ s : ℝ in (0 : ℝ)..r,
    (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s * helmholtzP mu s

theorem besselResolventPairing_intervalIntegrable {r : ℝ} (hr : 0 < r) (lam mu : ℂ) :
    IntervalIntegrable (fun s : ℝ => (2 * (Real.pi : ℂ)) *
      helmholtzResolventWeightedB r lam s * helmholtzP mu s) volume 0 r :=
  ((continuous_const.mul (continuous_helmholtzResolventWeightedB hr lam)).mul
    (continuous_helmholtzP mu)).intervalIntegrable 0 r

theorem circularMean_complex_mul_const (f : Plane → ℂ) (c : ℂ) (r : ℝ) (x : Plane) :
    circularMean (fun y => c * f y) r x = c * circularMean f r x := by
  unfold circularMean
  simp only [Complex.real_smul]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem circularMean_helmholtzExponential_zero (mu : ℂ) (s : ℝ) :
    circularMean (spectralExponential (-Complex.I * mu)) s 0 = helmholtzP mu s := by
  rw [circularMean_spectralExponential, spectralExponential_zero, one_mul, helmholtzP_eq_J0]
  congr 1
  calc
    _ = -(Complex.I ^ 2) * ((s : ℂ) * mu) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The Lagrange/Green pairing identity has no root or nonzero-parameter
restriction. Both endpoint terms come from the previously proved singular
radial Green identity. -/
theorem besselResolventPairing_green {r : ℝ} (hr : 0 < r) (lam mu : ℂ) :
    (lam ^ 2 - mu ^ 2) * besselResolventPairing r lam mu =
      helmholtzP mu r - helmholtzP lam r := by
  have hsq : (-Complex.I * mu) ^ 2 = -(mu ^ 2) := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  have hΔ : laplacian (spectralExponential (-Complex.I * mu)) =
      fun y => -(mu ^ 2) * spectralExponential (-Complex.I * mu) y := by
    funext y
    rw [laplacian_spectralExponential, hsq]
  have hh := integral_helmholtzResolventB_circle_laplacian
    (spectralExponential_contDiff (-Complex.I * mu)) (0 : Plane) hr lam
  simp_rw [hΔ, circularMean_complex_mul_const, circularMean_helmholtzExponential_zero] at hh
  rw [spectralExponential_zero, mul_one] at hh
  have hfun : (fun s : ℝ =>
      (2 * (Real.pi : ℂ) * (s : ℂ) * helmholtzResolventB r lam s) *
        (-(mu ^ 2) * helmholtzP mu s + lam ^ 2 * helmholtzP mu s)) =
      fun s : ℝ => (lam ^ 2 - mu ^ 2) *
        ((2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s * helmholtzP mu s) := by
    funext s
    rw [helmholtzResolventWeightedB_eq]
    ring
  rw [hfun, intervalIntegral.integral_const_mul] at hh
  exact hh

set_option maxHeartbeats 1000000 in
/-- Complex differentiation under the actual finite radial pairing. The
continuous weighted logarithmic companion supplies an ordinary compact
majorant; no formal differentiation of a singular integral is used. -/
theorem besselResolventPairing_hasDerivAt {r : ℝ} (hr : 0 < r) (lam mu : ℂ) :
    HasDerivAt (besselResolventPairing r lam)
      (∫ s : ℝ in (0 : ℝ)..r, (2 * (Real.pi : ℂ)) *
        helmholtzResolventWeightedB r lam s * resolventParameterSlope F mu s) mu := by
  have hW : Continuous (fun p : ℂ × ℝ =>
      (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam p.2) :=
    continuous_const.mul ((continuous_helmholtzResolventWeightedB hr lam).comp continuous_snd)
  have hG : Continuous (fun p : ℂ × ℝ => (2 * (Real.pi : ℂ)) *
      helmholtzResolventWeightedB r lam p.2 * helmholtzP p.1 p.2) :=
    hW.mul continuous_helmholtzP_joint
  have hH : Continuous (fun p : ℂ × ℝ => (2 * (Real.pi : ℂ)) *
      helmholtzResolventWeightedB r lam p.2 * resolventParameterSlope F p.1 p.2) :=
    hW.mul (continuous_resolventParameterSlope_joint F F_differentiable)
  have hd (z : ℂ) (s : ℝ) : HasDerivAt
      (fun w : ℂ => (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s * helmholtzP w s)
      ((2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s *
        resolventParameterSlope F z s) z :=
    (helmholtzP_parameter_hasDerivAt z s).const_mul
      ((2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s)
  exact hasDerivAt_complex_intervalIntegral_of_joint_continuous
    (G := fun z s => (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s * helmholtzP z s)
    (H := fun z s => (2 * (Real.pi : ℂ)) * helmholtzResolventWeightedB r lam s *
      resolventParameterSlope F z s) hG hH hd 0 r mu

/-- The diagonal pairing is determined by the genuine parameter derivative
of P. The term containing the derivative of the integral cancels because
the factor lam²-mu² vanishes on the diagonal. -/
theorem besselResolventPairing_diagonal_relation {r : ℝ} (hr : 0 < r) (lam : ℂ) :
    (2 * lam) * besselResolventPairing r lam lam = -resolventParameterSlope F lam r := by
  have hcoef := (hasDerivAt_const lam (lam ^ 2)).sub ((hasDerivAt_id lam).pow 2)
  have hleft := hcoef.mul (besselResolventPairing_hasDerivAt hr lam lam)
  have heq : (fun mu : ℂ => helmholtzP mu r - helmholtzP lam r) =ᶠ[𝓝 lam]
      fun mu : ℂ => (lam ^ 2 - mu ^ 2) * besselResolventPairing r lam mu :=
    Eventually.of_forall (fun mu => (besselResolventPairing_green hr lam mu).symm)
  have hh := (hleft.congr_of_eventuallyEq heq).unique
    ((helmholtzP_parameter_hasDerivAt lam r).sub_const (helmholtzP lam r))
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    show 2 - 1 = (1 : ℕ) by decide, pow_one, mul_one, sub_self, mul_zero, add_zero] at hh
  linear_combination -hh

/-- The finite, continuously extended dual mode in dimension two. At a root
J₀(lam)=1 it is the boundary-conditioned logarithmic companion corresponding
to the source's Bessel–Neumann dual, with its exact source scaling. -/
def volchkovDualMode (lam : ℂ) (s : ℝ) : ℂ :=
  4 * lam * helmholtzResolventWeightedB 1 lam s

theorem continuous_volchkovDualMode (lam : ℂ) : Continuous (volchkovDualMode lam) :=
  (continuous_helmholtzResolventWeightedB (by norm_num : (0 : ℝ) < 1) lam).const_mul (4 * lam)

@[simp] theorem volchkovDualMode_zero (lam : ℂ) : volchkovDualMode lam 0 = 0 := by
  simp [volchkovDualMode]

@[simp] theorem volchkovDualMode_one (lam : ℂ) : volchkovDualMode lam 1 = 0 := by
  rw [volchkovDualMode, helmholtzResolventWeightedB_eq,
    helmholtzResolventB_radius (by norm_num : (0 : ℝ) < 1)]
  simp

theorem volchkovDualMode_pairing (lam mu : ℂ) :
    (∫ s : ℝ in (0 : ℝ)..1, helmholtzP mu s * volchkovDualMode lam s) =
      (2 * lam / (Real.pi : ℂ)) * besselResolventPairing 1 lam mu := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold besselResolventPairing
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [volchkovDualMode]
  field_simp [hpi] <;> ring

/-- The non-diagonal double orthogonality is proved for the actual companion,
with distinct spectral squares (the ± symmetry cannot be ignored). -/
theorem volchkovDualMode_orthogonal {lam mu : ℂ}
    (hlam : J0 lam = 1) (hmu : J0 mu = 1) (hneq : lam ^ 2 ≠ mu ^ 2) :
    (∫ s : ℝ in (0 : ℝ)..1, helmholtzP mu s * volchkovDualMode lam s) = 0 := by
  have hh := besselResolventPairing_green (by norm_num : (0 : ℝ) < 1) lam mu
  simp only [helmholtzP_eq_J0, Complex.ofReal_one, one_mul, hlam, hmu, sub_self] at hh
  have hpair : besselResolventPairing 1 lam mu = 0 :=
    (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hneq)
  rw [volchkovDualMode_pairing, hpair, mul_zero]

theorem resolventParameterSlope_one_eq_J0_deriv (lam : ℂ) :
    resolventParameterSlope F lam 1 = deriv J0 lam := by
  have hfun : (fun mu : ℂ => helmholtzP mu 1) = J0 := by
    funext mu
    simp only [helmholtzP_eq_J0, Complex.ofReal_one, one_mul]
  have hh := helmholtzP_parameter_hasDerivAt lam 1
  rw [hfun] at hh
  exact hh.deriv.symm

/-- Exact diagonal normalization. In the classical notation -J₀′=J₁,
this is the source's J₁(lam)/π constant. -/
theorem volchkovDualMode_diagonal (lam : ℂ) :
    (∫ s : ℝ in (0 : ℝ)..1, helmholtzP lam s * volchkovDualMode lam s) =
      -deriv J0 lam / (Real.pi : ℂ) := by
  rw [volchkovDualMode_pairing]
  have hh := besselResolventPairing_diagonal_relation (by norm_num : (0 : ℝ) < 1) lam
  rw [resolventParameterSlope_one_eq_J0_deriv] at hh
  calc
    _ = ((2 * lam) * besselResolventPairing 1 lam lam) / (Real.pi : ℂ) := by ring
    _ = _ := by rw [hh]

/-- The normalizer does not vanish at any nonzero J₀ one-point. -/
theorem volchkovDualMode_diagonal_ne_zero {lam : ℂ} (hlam : lam ≠ 0) (hroot : J0 lam = 1) :
    (∫ s : ℝ in (0 : ℝ)..1, helmholtzP lam s * volchkovDualMode lam s) ≠ 0 := by
  rw [volchkovDualMode_diagonal]
  exact div_ne_zero (neg_ne_zero.mpr (J0_deriv_ne_zero_at_one_point hlam hroot))
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

end J0RadialUniqueness
