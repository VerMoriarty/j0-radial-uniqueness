import Solutions.J0RadialUniqueness.AbelVolterraInjectivity
import Solutions.J0RadialUniqueness.HelmholtzBallUniqueContinuation
import Mathlib.Tactic

/-! Recovery from the actual annular Abel equations. These are intermediate
tools: the hypotheses explicitly contain the Abel equations, and no conversion
from a circular mean identity is claimed here. The kernel uses m.natAbs for
each integer angular Fourier mode, and recovery uses all integer modes. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff Interval

namespace J0RadialUniqueness

/-- The concrete annular kernel is injective on every positive-width interval
strictly below a+r. The larger open square is constructed from the actual
radius margins, rather than postulated as an extra regularity assumption. -/
theorem annularAbelInjectivity_on_closedInterval (m : ℕ) {r a b : ℝ}
    (hr : 0 < r) (hra : r < a) (hab : a < b) (hb : b < a + r)
    {v : ℝ → ℂ} (hv : Continuous v)
    (hAbel : ∀ p ∈ Ioo a (a + r),
      (∫ s : ℝ in a..p, (Real.sqrt (p - s))⁻¹ •
        ((annularVolterraKernel m r (p, s) : ℂ) * v s)) = 0) :
    ∀ s ∈ Icc a b, v s = 0 := by
  let δ : ℝ := min ((a - r) / 4) ((a + r - b) / 4)
  let A : ℝ := a - δ
  let B : ℝ := b + δ
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by linarith) (by linarith)
  have hδa : 4 * δ ≤ a - r := by
    have hh := min_le_left ((a - r) / 4) ((a + r - b) / 4)
    change δ ≤ (a - r) / 4 at hh
    linarith
  have hδb : 4 * δ ≤ a + r - b := by
    have hh := min_le_right ((a - r) / 4) ((a + r - b) / 4)
    change δ ≤ (a + r - b) / 4 at hh
    linarith
  have hrA : r < A := by dsimp only [A]; linarith
  have hAa : A < a := by dsimp only [A]; linarith
  have hbB : b < B := by dsimp only [B]; linarith
  have hB : B < A + r := by dsimp only [A, B]; linarith
  apply abelVolterraInjectivity_local hv hAa hab hbB
    (annularVolterraKernel_complex_contDiffAt_on_openSquare m hr hrA hB)
  · intro t ht
    exact Complex.ofReal_ne_zero.mpr (annularVolterraKernel_diagonal_pos m hr
      (hra.trans_le ht.1)).ne'
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with hat | hat
    · subst t
      exact intervalIntegral.integral_same
    · exact hAbel t ⟨hat, ht.2.trans_lt hb⟩

/-- A mode vanishes throughout the annulus once its actual Abel equations
vanish. The initial endpoint is included by positive-width injectivity. -/
theorem annularAbelInjectivity_on_annulus (m : ℕ) {r a : ℝ}
    (hr : 0 < r) (hra : r < a) {v : ℝ → ℂ} (hv : Continuous v)
    (hAbel : ∀ p ∈ Ioo a (a + r),
      (∫ s : ℝ in a..p, (Real.sqrt (p - s))⁻¹ •
        ((annularVolterraKernel m r (p, s) : ℂ) * v s)) = 0) :
    ∀ s ∈ Ico a (a + r), v s = 0 := by
  intro s hs
  obtain ⟨b, hsb, hb⟩ := exists_between hs.2
  exact annularAbelInjectivity_on_closedInterval m hr hra (hs.1.trans_lt hsb) hb hv hAbel
    s ⟨hs.1, hsb.le⟩

/-- Every genuine integer Fourier mode is zero on the larger ball's radius
interval. No angular completeness statement is a hypothesis. -/
theorem helmholtzFourierMode_eq_zero_of_annular_abel {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r a : ℝ} (hr : 0 < r) (hra : r < a)
    (hinner : ∀ x ∈ planeBall a, u x = 0)
    (hAbel : ∀ m : ℤ, ∀ p ∈ Ioo a (a + r),
      (∫ s : ℝ in a..p, (Real.sqrt (p - s))⁻¹ •
        ((annularVolterraKernel m.natAbs r (p, s) : ℂ) * helmholtzFourierMode u m s)) = 0)
    (m : ℤ) {s : ℝ} (hs : 0 ≤ s) (hsR : s < a + r) :
    helmholtzFourierMode u m s = 0 := by
  by_cases hsa : s < a
  · exact helmholtzFourierMode_eq_zero_on_smaller_ball hinner m hs hsa
  · have hmc : Continuous (helmholtzFourierMode u m) :=
      continuous_iff_continuousAt.mpr fun t => (helmholtzFourierMode_hasDerivAt hu m t).continuousAt
    exact annularAbelInjectivity_on_annulus m.natAbs hr hra hmc (hAbel m)
      s ⟨le_of_not_gt hsa, hsR⟩

/-- Vanishing of every actual angular mode recovers the original continuous
function pointwise. This invokes the proved Fourier completeness theorem and
the real plane's actual polar representation. -/
theorem eq_zero_on_planeBall_of_helmholtz_modes {u : Plane → ℂ}
    (hu : Continuous u) {R : ℝ}
    (hmodes : ∀ m : ℤ, ∀ s : ℝ, 0 ≤ s → s < R → helmholtzFourierMode u m s = 0) :
    ∀ y ∈ planeBall R, u y = 0 := by
  intro y hy
  let s : ℝ := ‖y‖
  have hs : 0 ≤ s := norm_nonneg y
  have hsR : s < R := by
    simpa only [planeBall, Metric.mem_ball, dist_zero_right, s] using hy
  let G : ℝ → ℂ := fun θ => u (s • circleDirection θ)
  have hGc : Continuous G := hu.comp (continuous_circleDirection.const_smul s)
  have hGp : Function.Periodic G (2 * Real.pi) := by
    intro θ
    change u (s • circleDirection (θ + 2 * Real.pi)) = u (s • circleDirection θ)
    have hdir : circleDirection (θ + 2 * Real.pi) = circleDirection θ := by
      ext i
      fin_cases i <;> simp [circleDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]
    rw [hdir]
  have hGm (m : ℤ) : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      helmholtzAngularWeight m θ * G θ) = 0 := by
    simpa only [helmholtzFourierMode, circleValueIntegrand, zero_add, G] using hmodes m s hs hsR
  have hGzero := continuous_periodic_eq_zero_of_helmholtz_modes G hGc hGp hGm
  have hpolar : s • circleDirection (Complex.arg (complexToPlane.symm y)) = y := by
    apply complexToPlane.symm.injective
    simp only [map_smul, complexToPlane_symm_circleDirection, Complex.real_smul]
    have hh := Complex.norm_mul_exp_arg_mul_I (complexToPlane.symm y)
    simpa only [LinearIsometryEquiv.norm_map, s] using hh
  have hz := hGzero (Complex.arg (complexToPlane.symm y))
  change u (s • circleDirection (Complex.arg (complexToPlane.symm y))) = 0 at hz
  rw [hpolar] at hz
  exact hz

/-- The annular recovery layer with the actual Abel equations kept explicit
as an intermediate input. All integer angular modes, including negative ones,
use the kernel with index m.natAbs. -/
theorem eq_zero_on_larger_ball_of_annular_abel {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r a : ℝ} (hr : 0 < r) (hra : r < a)
    (hinner : ∀ x ∈ planeBall a, u x = 0)
    (hAbel : ∀ m : ℤ, ∀ p ∈ Ioo a (a + r),
      (∫ s : ℝ in a..p, (Real.sqrt (p - s))⁻¹ •
        ((annularVolterraKernel m.natAbs r (p, s) : ℂ) * helmholtzFourierMode u m s)) = 0) :
    ∀ y ∈ planeBall (a + r), u y = 0 := by
  apply eq_zero_on_planeBall_of_helmholtz_modes hu.continuous
  intro m s hs hsR
  exact helmholtzFourierMode_eq_zero_of_annular_abel hu hr hra hinner hAbel m hs hsR

end J0RadialUniqueness
