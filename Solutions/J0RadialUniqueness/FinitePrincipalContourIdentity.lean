import Solutions.J0RadialUniqueness.FinitePrincipalParts
import Solutions.J0RadialUniqueness.SquareContourAlgebra

/-! Finite Cauchy contour identity from the proved analytic remainder.
All principal-part edge integrals are genuine L1 integrals; the identity is
derived from rectangle Cauchy--Goursat, rather than supplied as a residue
theorem assumption. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical

namespace J0RadialUniqueness

def closedSpectralSquare (a : ℝ) : Set ℂ := Icc (-a) a ×ℂ Icc (-a) a

theorem squareBoundary_subset_closedSpectralSquare {a : ℝ} {z : ℂ}
    (hz : z ∈ squareBoundarySet a) : z ∈ closedSpectralSquare a := by
  rcases hz with ⟨hr, hi⟩ | ⟨hi, hr⟩
  · exact ⟨abs_le.mp hr.le, abs_le.mp hi⟩
  · exact ⟨abs_le.mp hr, abs_le.mp hi.le⟩

theorem inside_square_not_boundary {a : ℝ} {z : ℂ} (hr : |z.re| < a) (hi : |z.im| < a) :
    z ∉ squareBoundarySet a := by
  rintro (⟨he, _⟩ | ⟨he, _⟩)
  · exact hr.ne he
  · exact hi.ne he

theorem squareBoundaryIntegral_eq_sum_principalParts {a : ℝ} (ha : 0 < a)
    (S : Finset ℂ) (F : ℂ → ℂ) (P H : ℂ → ℂ → ℂ)
    (hS : ∀ b ∈ S, |b.re| < a ∧ |b.im| < a)
    (hF : ∀ z ∈ closedSpectralSquare a, z ∉ S → AnalyticAt ℂ F z)
    (hP : ∀ z ∈ closedSpectralSquare a, ∀ b ∈ S, z ≠ b → AnalyticAt ℂ (P b) z)
    (hH : ∀ z ∈ closedSpectralSquare a, z ∈ S → AnalyticAt ℂ (H z) z)
    (hlocal : ∀ z ∈ closedSpectralSquare a, z ∈ S →
      ∀ᶠ w : ℂ in 𝓝 z, w ≠ z → F w = P z w + H z w) :
    squareBoundaryIntegral a F = ∑ b ∈ S, squareBoundaryIntegral a (P b) := by
  let R : ℂ → ℂ := finitePrincipalRemainder S F P H
  have hR : AnalyticOnNhd ℂ R (closedSpectralSquare a) :=
    finitePrincipalRemainder_analyticOnNhd S F P H hF hP hH hlocal
  have hbd (z : ℂ) (hz : z ∈ squareBoundarySet a) : z ∉ S := by
    intro hzS
    exact inside_square_not_boundary (hS z hzS).1 (hS z hzS).2 hz
  have hPi (b : ℂ) (hb : b ∈ S) : AnalyticOnNhd ℂ (P b) (squareBoundarySet a) := by
    intro z hz
    exact hP z (squareBoundary_subset_closedSpectralSquare hz) b hb
      (by intro he; subst z; exact hbd b hz hb)
  have hPint (b : ℂ) (hb : b ∈ S) : SquareBoundaryIntegrable a (P b) :=
    squareBoundaryIntegrable_of_continuousOn ha.le (hPi b hb).continuousOn
  have hsum : AnalyticOnNhd ℂ (fun z => ∑ b ∈ S, P b z) (squareBoundarySet a) := by
    intro z hz
    apply Finset.analyticAt_fun_sum
    intro b hb
    exact hPi b hb z hz
  have hRi : SquareBoundaryIntegrable a R :=
    squareBoundaryIntegrable_of_continuousOn ha.le
      (hR.continuousOn.mono (fun _ => squareBoundary_subset_closedSpectralSquare))
  have hSi : SquareBoundaryIntegrable a (fun z => ∑ b ∈ S, P b z) :=
    squareBoundaryIntegrable_of_continuousOn ha.le hsum.continuousOn
  have hRzero : squareBoundaryIntegral a R = 0 :=
    squareBoundaryIntegral_eq_zero_of_differentiableOn ha.le R hR.differentiableOn
  have heq : EqOn F (fun z => R z + ∑ b ∈ S, P b z) (squareBoundarySet a) := by
    intro z hz
    dsimp only [R]
    rw [finitePrincipalRemainder_eq_of_notMem S F P H (hbd z hz)]
    ring
  calc
    squareBoundaryIntegral a F = squareBoundaryIntegral a
        (fun z => R z + ∑ b ∈ S, P b z) := squareBoundaryIntegral_congr ha.le heq
    _ = squareBoundaryIntegral a R + squareBoundaryIntegral a (fun z => ∑ b ∈ S, P b z) :=
      squareBoundaryIntegral_add hRi hSi
    _ = _ := by rw [hRzero, zero_add, squareBoundaryIntegral_sum S P hPint]

end J0RadialUniqueness
