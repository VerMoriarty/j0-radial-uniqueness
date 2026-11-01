import Definitions.J0RadialUniqueness.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
Analytic definitions and open statement specifications for Sections 2--5.

Every `...Statement` below is a proposition to be proved, not an assumption
or a theorem. Bochner integrals are accompanied by separate integrability
obligations. `K0Series` is defined independently of the Laplace integral,
using the principal logarithm series in DLMF 10.31.2.
-/

noncomputable section

open MeasureTheory

namespace J0RadialUniqueness

def rightHalfPlane : Set ℂ := {z | 0 < z.re}

/-- The density of the paper's probability measure, integrated over `Ioi 0`. -/
def muDensity (t : ℝ) : ℝ :=
  Real.exp (-t) * Real.rpow t (-1 / 2 : ℝ) / Real.sqrt Real.pi

def weightedIntegral (g : ℝ → ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (muDensity t : ℂ) * g t

def laplaceKernel (w : ℂ) (t : ℝ) : ℂ :=
  Complex.cpow (1 + (t : ℂ) / (2 * w)) (-1 / 2 : ℂ)

def laplaceMomentKernel (w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * Complex.cpow (1 + (t : ℂ) / (2 * w)) (-3 / 2 : ℂ)

def laplaceI (w : ℂ) : ℂ := weightedIntegral (laplaceKernel w)

def laplaceK (w : ℂ) : ℂ :=
  Complex.cpow ((Real.pi : ℂ) / (2 * w)) (1 / 2 : ℂ) *
    Complex.exp (-w) * laplaceI w

/-- The principal-branch logarithmic series for the actual modified Bessel K₀.
The coefficient at `n = 0` is zero because `harmonic 0 = 0`.
Its convergence and identification with the Laplace integral remain obligations. -/
def K0Series (w : ℂ) : ℂ :=
  -(Complex.log (w / 2) + (Real.eulerMascheroniConstant : ℂ)) * F (w ^ 2 / 4) +
    ∑' n : ℕ, (harmonic n : ℂ) * fTerm (w ^ 2 / 4) n

def plusKernel (z : ℂ) (t : ℝ) : ℂ :=
  Complex.cpow (1 + Complex.I * (t : ℂ) / (2 * z)) (-1 / 2 : ℂ)

def minusKernel (z : ℂ) (t : ℝ) : ℂ :=
  Complex.cpow (1 - Complex.I * (t : ℂ) / (2 * z)) (-1 / 2 : ℂ)

def plusMomentKernel (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * Complex.cpow (1 + Complex.I * (t : ℂ) / (2 * z)) (-3 / 2 : ℂ)

def minusMomentKernel (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * Complex.cpow (1 - Complex.I * (t : ℂ) / (2 * z)) (-3 / 2 : ℂ)

def APlus (z : ℂ) : ℂ := weightedIntegral (plusKernel z)

def AMinus (z : ℂ) : ℂ := weightedIntegral (minusKernel z)

def amplitudeDomain : Set ℂ :=
  {z | z ∈ rightHalfPlane ∧ APlus z * AMinus z ≠ 0}

def delta (z : ℂ) : ℂ :=
  Complex.exp (2 * Complex.I * (z - (Real.pi : ℂ) / 4)) * APlus z / AMinus z

def kappa : ℝ := Real.rpow 2 (-9 / 4 : ℝ)

def rayLogNorm (z : ℂ) (τ : ℝ) : ℝ :=
  Real.log ‖J0 ((τ : ℂ) * z)‖

def rayLogDerivative (z : ℂ) (τ : ℝ) : ℝ := τ * deriv (rayLogNorm z) τ

/-- Lemma 2.1. -/
def FRightHalfPlaneStatement : Prop :=
  ∀ w : ℂ, w ≠ 0 → 0 ≤ w.re → 1 < ‖F w‖

/-- The termwise differentiated differential equation needed in Lemma 2.1. -/
def FODEStatement : Prop :=
  Differentiable ℂ F ∧ Differentiable ℂ (deriv F) ∧
    ∀ w : ℂ, w * deriv (deriv F) w + deriv F w = F w

/-- The real-parameter energy identity (2.1), including both boundary values. -/
def FEnergyStatement : Prop :=
  ∀ φ : ℝ, -(Real.pi / 2) ≤ φ → φ ≤ Real.pi / 2 →
    let h : ℝ → ℂ := fun s => F ((s : ℂ) * Complex.exp (Complex.I * (φ : ℂ)))
    let Y : ℝ → ℝ := fun s => ‖h s‖ ^ 2
    h 0 = 1 ∧ deriv h 0 = Complex.exp (Complex.I * (φ : ℂ)) ∧
      ∀ s : ℝ, 0 ≤ s →
        s * deriv Y s = 2 * ∫ u in (0 : ℝ)..s,
          (u * ‖deriv h u‖ ^ 2 + Real.cos φ * ‖h u‖ ^ 2)

/-- Lemma 2.2. -/
def NoRealOnePointsStatement : Prop :=
  ∀ x : ℝ, x ≠ 0 → ‖J0 (x : ℂ)‖ < 1

/-- The Bessel integral formula cited from DLMF 10.9.2. -/
def RealBesselIntegralStatement : Prop :=
  ∀ x : ℝ,
    IntervalIntegrable
      (fun t : ℝ => Complex.exp (Complex.I * (x : ℂ) * (Real.cos t : ℂ)))
      volume 0 Real.pi ∧
    J0 (x : ℂ) = (1 / (Real.pi : ℂ)) *
      ∫ t in (0 : ℝ)..Real.pi,
        Complex.exp (Complex.I * (x : ℂ) * (Real.cos t : ℂ))

/-- Lemma 2.3. -/
def QZeroFreeStatement : Prop := ∀ w : ℂ, ‖w‖ < 4 → Q w ≠ 0

/-- Proposition 2.4. For a complex number, nonrealness means its imaginary part is nonzero. -/
def GlobalLocalizationStatement : Prop :=
  ∀ z : ℂ, z ≠ 0 → J0 z = 1 → 0 < (z ^ 2).re ∧ z.im ≠ 0 ∧ 4 ≤ ‖z‖

/-- The two Gamma(1/2) moment evaluations used throughout Sections 3--4. -/
def MuMomentsStatement : Prop :=
  IntegrableOn muDensity (Set.Ioi (0 : ℝ)) volume ∧
  IntegrableOn (fun t => t * muDensity t) (Set.Ioi (0 : ℝ)) volume ∧
  (∫ t in Set.Ioi (0 : ℝ), muDensity t) = 1 ∧
  (∫ t in Set.Ioi (0 : ℝ), t * muDensity t) = 1 / 2

/-- Absolute convergence obligations for the Laplace formula and its derivative. -/
def LaplaceIntegrabilityStatement : Prop :=
  ∀ w ∈ Complex.slitPlane,
    IntegrableOn (fun t => (muDensity t : ℂ) * laplaceKernel w t)
      (Set.Ioi (0 : ℝ)) volume ∧
    IntegrableOn (fun t => (muDensity t : ℂ) * laplaceMomentKernel w t)
      (Set.Ioi (0 : ℝ)) volume

/-- Analytic assertions of Proposition 3.1, before identifying the independent K₀ series. -/
def KLaplaceStatement : Prop :=
  DifferentiableOn ℂ laplaceI Complex.slitPlane ∧
  DifferentiableOn ℂ laplaceK Complex.slitPlane ∧
  ∀ w ∈ Complex.slitPlane,
    HasDerivAt laplaceI ((1 / (4 * w ^ 2)) * weightedIntegral (laplaceMomentKernel w)) w

def K0SeriesConvergenceStatement : Prop :=
  ∀ w : ℂ, Summable (fun n : ℕ => (harmonic n : ℂ) * fTerm (w ^ 2 / 4) n)

/-- Remaining identification assertion of Proposition 3.1. -/
def KLaplaceIdentificationStatement : Prop :=
  ∀ w ∈ Complex.slitPlane, laplaceK w = K0Series w

/-- The order-zero connection formula cited from DLMF 10.27.9. -/
def K0ConnectionStatement : Prop :=
  ∀ z ∈ rightHalfPlane,
    (Real.pi : ℂ) * Complex.I * J0 z =
      K0Series (-Complex.I * z) - K0Series (Complex.I * z)

def AmplitudeIntegrabilityStatement : Prop :=
  ∀ z ∈ rightHalfPlane,
    IntegrableOn (fun t => (muDensity t : ℂ) * plusKernel z t)
      (Set.Ioi (0 : ℝ)) volume ∧
    IntegrableOn (fun t => (muDensity t : ℂ) * minusKernel z t)
      (Set.Ioi (0 : ℝ)) volume ∧
    IntegrableOn (fun t => (muDensity t : ℂ) * plusMomentKernel z t)
      (Set.Ioi (0 : ℝ)) volume ∧
    IntegrableOn (fun t => (muDensity t : ℂ) * minusMomentKernel z t)
      (Set.Ioi (0 : ℝ)) volume

/-- Holomorphy and derivative assertions of Proposition 3.2. -/
def AmplitudeDerivativeStatement : Prop :=
  DifferentiableOn ℂ APlus rightHalfPlane ∧
  DifferentiableOn ℂ AMinus rightHalfPlane ∧
  ∀ z ∈ rightHalfPlane,
    HasDerivAt APlus (Complex.I / (4 * z ^ 2) * weightedIntegral (plusMomentKernel z)) z ∧
    HasDerivAt AMinus (-Complex.I / (4 * z ^ 2) * weightedIntegral (minusMomentKernel z)) z

/-- The exact principal-branch J₀ decomposition in Proposition 3.2. -/
def ExactDecompositionStatement : Prop :=
  ∀ z ∈ rightHalfPlane,
    J0 z =
      (Complex.exp (Complex.I * (z - (Real.pi : ℂ) / 4)) * APlus z +
        Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4)) * AMinus z) /
      Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)

/-- The two integral amplitude estimates in Proposition 4.1. -/
def AmplitudeUniformEstimatesStatement : Prop :=
  ∀ z : ℂ, ClosedPrincipalSector z →
    ‖APlus z - 1‖ ≤ kappa / ‖z‖ ∧ ‖AMinus z - 1‖ ≤ kappa / ‖z‖ ∧
    ‖deriv APlus z‖ ≤ kappa / ‖z‖ ^ 2 ∧ ‖deriv AMinus z‖ ≤ kappa / ‖z‖ ^ 2

/-- The strict large-radius consequences in Proposition 4.1. -/
def AmplitudeModulusBoundsStatement : Prop :=
  ∀ z : ℂ, ClosedPrincipalSector z → 4 ≤ ‖z‖ →
    15 / 16 < ‖APlus z‖ ∧ ‖APlus z‖ < 17 / 16 ∧
    15 / 16 < ‖AMinus z‖ ∧ ‖AMinus z‖ < 17 / 16 ∧
    ‖z * deriv APlus z / APlus z‖ < 1 / 15 ∧
    ‖z * deriv AMinus z / AMinus z‖ < 1 / 15

def FactorizationStatement : Prop :=
  ∀ z ∈ amplitudeDomain,
    J0 z =
      (Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4)) * AMinus z /
        Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)) * (1 + delta z)

/-- Proposition 4.2. -/
def QuantitativeSeparationStatement : Prop :=
  ∀ z : ℂ, J0 z = 1 → PrincipalSector z →
    z ∈ amplitudeDomain ∧ 7 / 5 < z.im ∧ Real.exp (-2 * z.im) < 1 / 16 ∧
    ‖delta z‖ < 17 / 240 ∧ ‖z‖ * Real.exp (-2 * z.im) < 11 / 50

/-- The propagated bounds and absence of zeros used in Proposition 5.1. -/
def RaySeparationStatement : Prop :=
  ∀ z : ℂ, J0 z = 1 → PrincipalSector z → ∀ τ : ℝ, 1 ≤ τ →
    let w := (τ : ℂ) * z
    w ∈ amplitudeDomain ∧ ‖delta w‖ < 17 / 240 ∧
      ‖w‖ * ‖delta w‖ < 187 / 750 ∧ J0 w ≠ 0

def DeltaDerivativeStatement : Prop :=
  ∀ z ∈ amplitudeDomain,
    z * deriv delta z = delta z *
      (2 * Complex.I * z + z * deriv APlus z / APlus z -
        z * deriv AMinus z / AMinus z)

def RadialDerivativeDecompositionStatement : Prop :=
  ∀ z : ℂ, J0 z = 1 → PrincipalSector z → ∀ τ : ℝ, 1 ≤ τ →
    let w := (τ : ℂ) * z
    DifferentiableAt ℝ (rayLogNorm z) τ ∧
      rayLogDerivative z τ = w.im - 1 / 2 +
        (w * deriv AMinus w / AMinus w + w * deriv delta w / (1 + delta w)).re

/-- Both conclusions of Proposition 5.1, with the real derivative stated explicitly. -/
def PrincipalRadialEscapeStatement : Prop :=
  ∀ z : ℂ, J0 z = 1 → PrincipalSector z →
    (∀ τ : ℝ, 1 ≤ τ → DifferentiableAt ℝ (rayLogNorm z) τ ∧
      7 / 25 < rayLogDerivative z τ) ∧
    (∀ c : ℝ, 1 < c → Real.rpow c (7 / 25 : ℝ) < ‖J0 ((c : ℂ) * z)‖)

end J0RadialUniqueness
