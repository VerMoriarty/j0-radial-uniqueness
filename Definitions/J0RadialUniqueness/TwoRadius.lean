import Definitions.J0RadialUniqueness.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Support

/-! Exact analytic statements for Section 6 of the supplied paper.

These are definitions of the statements to be proved, not proofs or axioms.
Functions on a ball are represented by functions on the ambient plane: only their
restrictions to the stated ball enter the local hypotheses and distributional conclusion.
The test-function formulation uses the actual Mathlib Laplacian and Lebesgue integral.
-/

noncomputable section

open MeasureTheory Laplacian
open scoped ContDiff

namespace J0RadialUniqueness

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def planeBall (R : ℝ) : Set Plane := Metric.ball (0 : Plane) R

def circleDirection (t : ℝ) : Plane := WithLp.toLp 2 ![Real.cos t, Real.sin t]

/-- The normalized arclength mean, for either real or complex valued functions. -/
def circularMean {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) (r : ℝ) (x : Plane) : V :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ t : ℝ in (0 : ℝ)..(2 * Real.pi), f (x + r • circleDirection t)

/-- A mean identity almost everywhere on its specified natural domain. -/
def MeanIdentityOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) (r : ℝ) (U : Set Plane) : Prop :=
  ∀ᵐ x ∂(volume.restrict U), circularMean f r x = f x

/-- Actual circle integrability and representative independence on the full
natural center domain; no assertion about every individual circle is made. -/
def CircularMeanWellDefinedStatement : Prop :=
  (∀ (f g : Plane → ℂ) (R r : ℝ), 0 ≤ r →
    f =ᵐ[volume.restrict (planeBall R)] g →
    circularMean f r =ᵐ[volume.restrict (planeBall (R - r))] circularMean g r) ∧
  (∀ (f : Plane → ℂ) (R r : ℝ), 0 ≤ r → LocallyIntegrableOn f (planeBall R) →
    (∀ᵐ x ∂volume.restrict (planeBall (R - r)),
      IntervalIntegrable (fun t : ℝ => f (x + r • circleDirection t)) volume
        0 (2 * Real.pi)) ∧
    LocallyIntegrableOn (circularMean f r) (planeBall (R - r)))

/-- `Δ f = 0` on an open set, in the sense of real smooth compactly supported tests.
The original complex valued function is paired with a real test function, so the zero
identity contains both its real and imaginary distributional equations. -/
def DistributionHarmonicOn (f : Plane → ℂ) (U : Set Plane) : Prop :=
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x : Plane, (laplacian φ x : ℂ) * f x) = 0

/-- The explicit exponential spectral mode in Proposition 6.2. -/
def spectralExponential (lam : ℂ) (x : Plane) : ℂ :=
  Complex.exp (lam * (x 0 : ℂ))

def spectralRealPart (lam : ℂ) (x : Plane) : ℝ := (spectralExponential lam x).re

def spectralImagPart (lam : ℂ) (x : Plane) : ℝ := (spectralExponential lam x).im

/-- Proposition 6.2, with the explicit real or imaginary exponential witness from its proof.
This is only a specification of the still required theorem. -/
def ExplicitCounterexampleStatement : Prop :=
  ∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ →
    ∀ lam : ℂ, lam ≠ 0 →
      J0 (Complex.I * lam * (r₁ : ℂ)) = 1 →
      J0 (Complex.I * lam * (r₂ : ℂ)) = 1 →
      ∃ g : Plane → ℝ,
        (g = spectralRealPart lam ∨ g = spectralImagPart lam) ∧
        ContDiff ℝ ∞ g ∧
        ¬ InnerProductSpace.HarmonicOnNhd g Set.univ ∧
        (∀ x : Plane, circularMean g r₁ x = g x) ∧
        (∀ x : Plane, circularMean g r₂ x = g x)

/-- Theorem 6.3: the exact cited local Volchkov theorem, as an unproved proposition. -/
def VolchkovLocalStatement : Prop :=
  ∀ (r₁ r₂ R : ℝ) (f : Plane → ℂ),
    0 < r₁ → 0 < r₂ → r₁ + r₂ < R →
    LocallyIntegrableOn f (planeBall R) →
    MeanIdentityOn f r₁ (planeBall (R - r₁)) →
    MeanIdentityOn f r₂ (planeBall (R - r₂)) →
    ((r₁ / r₂ : ℝ) : ℂ) ∉ ratioSet →
    DistributionHarmonicOn f (planeBall R)

/-- Corollary 6.4: the local two-radius conclusion with the spectral exclusion removed. -/
def LocalTwoRadiusStatement : Prop :=
  ∀ (r₁ r₂ R : ℝ) (f : Plane → ℂ),
    0 < r₁ → 0 < r₂ → r₁ ≠ r₂ → r₁ + r₂ < R →
    LocallyIntegrableOn f (planeBall R) →
    MeanIdentityOn f r₁ (planeBall (R - r₁)) →
    MeanIdentityOn f r₂ (planeBall (R - r₂)) →
    DistributionHarmonicOn f (planeBall R)

/-- Corollary 6.5, including its smooth harmonic representative and continuous case. -/
def GlobalTwoRadiusStatement : Prop :=
  ∀ (r₁ r₂ : ℝ) (f : Plane → ℂ),
    0 < r₁ → 0 < r₂ → r₁ ≠ r₂ → LocallyIntegrable f →
    MeanIdentityOn f r₁ Set.univ → MeanIdentityOn f r₂ Set.univ →
    DistributionHarmonicOn f Set.univ ∧
    (∃ g : Plane → ℂ, ContDiff ℝ ∞ g ∧
      InnerProductSpace.HarmonicOnNhd g Set.univ ∧ ∀ᵐ x, f x = g x) ∧
    (Continuous f → InnerProductSpace.HarmonicOnNhd f Set.univ ∧
      ∀ r : ℝ, 0 < r → ∀ x : Plane, circularMean f r x = f x)

/-- The actual global Weyl regularity obligation used in Corollary 6.5. -/
def WeylRegularizationStatement : Prop :=
  ∀ f : Plane → ℂ, LocallyIntegrable f → DistributionHarmonicOn f Set.univ →
    ∃ g : Plane → ℂ, ContDiff ℝ ∞ g ∧
      InnerProductSpace.HarmonicOnNhd g Set.univ ∧ ∀ᵐ x : Plane, f x = g x

def AllRadiusMeanValueStatement : Prop :=
  ∀ g : Plane → ℂ, InnerProductSpace.HarmonicOnNhd g Set.univ →
    ∀ r : ℝ, 0 < r → ∀ x : Plane, circularMean g r x = g x

end J0RadialUniqueness
