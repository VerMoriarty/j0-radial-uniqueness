import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact definitions from the supplied paper. No analytic assertions are postulated here. -/

noncomputable section

namespace J0RadialUniqueness

def fTerm (w : ℂ) (n : ℕ) : ℂ := w ^ n / (n.factorial : ℂ) ^ 2

def F (w : ℂ) : ℂ := ∑' n : ℕ, fTerm w n

def Q (w : ℂ) : ℂ := ∑' n : ℕ, w ^ n / ((n + 1).factorial : ℂ) ^ 2

/-- The series defining the actual Bessel function of order zero. -/
def J0 (z : ℂ) : ℂ := F (-z ^ 2 / 4)

def onePoints : Set ℂ := {z | z ≠ 0 ∧ J0 z = 1}

def ratioSet : Set ℂ := {c | ∃ α ∈ onePoints, ∃ β ∈ onePoints, α / β = c}

def PrincipalSector (z : ℂ) : Prop := 0 < z.im ∧ z.im < z.re

def ClosedPrincipalSector (z : ℂ) : Prop := 0 ≤ z.im ∧ z.im ≤ z.re ∧ 0 < z.re

/-- The full quantified statement of Theorem A / Theorem 5.2. -/
def RadialEscape : Prop :=
  ∀ z : ℂ, z ≠ 0 → J0 z = 1 → ∀ c : ℝ, 1 < c →
    Real.rpow c (7 / 25 : ℝ) < ‖J0 ((c : ℂ) * z)‖

/-- There is at most one positive radius with value one in each nonzero direction. -/
def RayUniqueness : Prop :=
  ∀ v : ℂ, v ≠ 0 → ∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ →
    J0 ((r₁ : ℂ) * v) = 1 → J0 ((r₂ : ℂ) * v) = 1 → r₁ = r₂

end J0RadialUniqueness
