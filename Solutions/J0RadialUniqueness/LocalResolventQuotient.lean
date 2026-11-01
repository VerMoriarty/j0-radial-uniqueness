import Solutions.J0RadialUniqueness.LocalFilterPoleElimination
import Solutions.J0RadialUniqueness.ResolventSymmetry

/-! The actual local resolvent quotient with its removable values filled.

Every vanishing and simple-zero input to the general division theorem is
discharged using the proved local filter and actual Bessel spectrum. The only
spectral input of the smooth mathematical core is the explicit no-common-zero
condition; the original root-ratio exclusion is also provided as an interface.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace J0RadialUniqueness

def localResolventQuotient (r : ℝ) (u : Plane → ℂ) (x : Plane) (lam : ℂ) : ℂ :=
  simpleZeroQuotient (planarResolventTConvolution r u x) (helmholtzResolventMass r) lam

theorem localResolventQuotient_eq_div (r : ℝ) (u : Plane → ℂ) (x : Plane)
    {lam : ℂ} (hmass : helmholtzResolventMass r lam ≠ 0) :
    localResolventQuotient r u x lam =
      planarResolventTConvolution r u x lam / helmholtzResolventMass r lam := by
  simp only [localResolventQuotient, simpleZeroQuotient, if_neg hmass]

theorem localResolventQuotient_eq_deriv_div_at_root (r : ℝ) (u : Plane → ℂ) (x : Plane)
    {lam : ℂ} (hmass : helmholtzResolventMass r lam = 0) :
    localResolventQuotient r u x lam =
      deriv (planarResolventTConvolution r u x) lam / deriv (helmholtzResolventMass r) lam := by
  simp only [localResolventQuotient, simpleZeroQuotient, if_pos hmass]

/-- The derivative of an actual differentiable even function is odd. -/
theorem deriv_at_neg_of_even_function {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (heven : ∀ z : ℂ, f (-z) = f z) (z : ℂ) : deriv f (-z) = -deriv f z := by
  have hd : HasDerivAt (fun w : ℂ => f (-w)) (-deriv f (-z)) z := by
    convert! (hf (-z)).hasDerivAt.comp z (hasDerivAt_id z).neg using 1 <;>
      simp only [id_eq, mul_neg, mul_one]
  have he : (fun w : ℂ => f (-w)) = f := funext heven
  rw [he] at hd
  have hval := hd.unique (hf z).hasDerivAt
  linear_combination -hval

/-- The explicit derivative-ratio filling preserves evenness, including every
denominator zero. No vanishing or simple-zero premise is needed for parity. -/
theorem simpleZeroQuotient_even_of_even_functions {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfeven : ∀ z : ℂ, f (-z) = f z) (hgeven : ∀ z : ℂ, g (-z) = g z) (z : ℂ) :
    simpleZeroQuotient f g (-z) = simpleZeroQuotient f g z := by
  by_cases hz : g z = 0
  · simp only [simpleZeroQuotient, hgeven z, if_pos hz, deriv_at_neg_of_even_function hf hfeven z,
      deriv_at_neg_of_even_function hg hgeven z, neg_div_neg_eq]
  · simp only [simpleZeroQuotient, hgeven z, if_neg hz, hfeven z]

theorem helmholtzResolventMass_differentiable (r : ℝ) :
    Differentiable ℂ (helmholtzResolventMass r) :=
  fun lam => (helmholtzResolventMass_parameter_analyticAt r lam).differentiableAt

/-- Evenness holds for the filled actual quotient for every continuous input,
independently of the local mean equations and the spectral exclusion. -/
theorem localResolventQuotient_neg {r : ℝ} (hr : 0 < r) {u : Plane → ℂ}
    (hu : Continuous u) (x : Plane) (lam : ℂ) :
    localResolventQuotient r u x (-lam) = localResolventQuotient r u x lam := by
  exact simpleZeroQuotient_even_of_even_functions
    (planarResolventTConvolution_differentiable hr hu x)
    (helmholtzResolventMass_differentiable r)
    (planarResolventTConvolution_neg r u x) (helmholtzResolventMass_neg r) lam

theorem planarResolventTConvolution_eq_complexConvolution (r : ℝ) (u : Plane → ℂ)
    (x : Plane) (lam : ℂ) :
    planarResolventTConvolution r u x lam =
      complexConvolution (planarHelmholtzResolventT r lam) u x := rfl

theorem local_resolvent_numerator_zero_at_mass_root {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) {lam : ℂ}
    (hroot : helmholtzResolventMass r₁ lam = 0) :
    planarResolventTConvolution r₁ u x lam = 0 := by
  rw [planarResolventTConvolution_eq_complexConvolution]
  exact localFilterPoleElimination hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ lam hroot x hx

/-- All removable-pole premises are discharged using the actual local filter,
actual entire numerator and actual simple spectral zeros. -/
theorem localResolventQuotient_analyticAt {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) (lam : ℂ) :
    AnalyticAt ℂ (localResolventQuotient r₁ u x) lam := by
  exact simpleZeroQuotient_analyticAt
    (planarResolventTConvolution_differentiable hr₁ hu.continuous x)
    (helmholtzResolventMass_differentiable r₁)
    (fun z hz => local_resolvent_numerator_zero_at_mass_root hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx hz)
    (fun z hz => helmholtzResolventMass_deriv_ne_zero_at_root hr₁ hz) lam

theorem localResolventQuotient_differentiable {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) :
    Differentiable ℂ (localResolventQuotient r₁ u x) :=
  fun lam => (localResolventQuotient_analyticAt hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx lam).differentiableAt

/-- The factorization is valid at every spectral parameter, including the roots
where the quotient is the actual derivative ratio rather than totalized f/g. -/
theorem localResolventQuotient_factorization {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) (lam : ℂ) :
    planarResolventTConvolution r₁ u x lam =
      helmholtzResolventMass r₁ lam * localResolventQuotient r₁ u x lam := by
  exact simpleZeroQuotient_factorization
    (f := planarResolventTConvolution r₁ u x) (g := helmholtzResolventMass r₁)
    (fun z hz => local_resolvent_numerator_zero_at_mass_root hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx hz) lam

theorem localResolventQuotient_analyticAt_of_ratio_exclusion {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {R r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hratio : ((r₁ / r₂ : ℝ) : ℂ) ∉ ratioSet)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) (lam : ℂ) :
    AnalyticAt ℂ (localResolventQuotient r₁ u x) lam :=
  localResolventQuotient_analyticAt hu hr₁ hr₂ hR
    (helmholtzResolventMasses_no_common_zero_of_ratio_exclusion hr₁ hr₂ hratio) hG₁ hG₂ hx lam

theorem localResolventQuotient_factorization_of_ratio_exclusion {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {R r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hratio : ((r₁ / r₂ : ℝ) : ℂ) ∉ ratioSet)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) (lam : ℂ) :
    planarResolventTConvolution r₁ u x lam =
      helmholtzResolventMass r₁ lam * localResolventQuotient r₁ u x lam :=
  localResolventQuotient_factorization hu hr₁ hr₂ hR
    (helmholtzResolventMasses_no_common_zero_of_ratio_exclusion hr₁ hr₂ hratio) hG₁ hG₂ hx lam

end J0RadialUniqueness
