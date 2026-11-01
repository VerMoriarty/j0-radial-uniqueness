import Solutions.J0RadialUniqueness.CircularMeanFourier
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact annihilation of low-degree coordinate polynomials by the actual
integer angular Fourier projection. The proof expands powers recursively into
the two integer frequency shifts and uses the explicit exponential integral.
No angular orthogonality or Funk--Hecke assertion is assumed. -/

noncomputable section

open MeasureTheory
open scoped Topology Interval ComplexConjugate BigOperators

namespace J0RadialUniqueness

def rotatedFirstCoordinate (z : ℂ) (θ : ℝ) : ℂ :=
  ((complexToPlane (Complex.exp ((θ : ℂ) * Complex.I) * z)) 0 : ℂ)

theorem complexToPlane_firstCoordinate (w : ℂ) : (complexToPlane w) 0 = w.re := by
  have hh := congrArg Complex.re (complexToPlane_symm_apply (complexToPlane w))
  simpa only [LinearIsometryEquiv.symm_apply_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero] using hh.symm

/-- The actual first coordinate under a rotation has exactly frequencies ±1. -/
theorem rotatedFirstCoordinate_eq_exp (z : ℂ) (θ : ℝ) :
    rotatedFirstCoordinate z θ =
      (Complex.exp ((θ : ℂ) * Complex.I) * z +
        Complex.exp (-((θ : ℂ) * Complex.I)) * conj z) / 2 := by
  have he : conj (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  unfold rotatedFirstCoordinate
  rw [complexToPlane_firstCoordinate, Complex.re_eq_add_conj, map_mul, he]

theorem continuous_rotatedFirstCoordinate (z : ℂ) : Continuous (rotatedFirstCoordinate z) := by
  have he : rotatedFirstCoordinate z = fun θ : ℝ =>
      (Complex.exp ((θ : ℂ) * Complex.I) * z +
        Complex.exp (-((θ : ℂ) * Complex.I)) * conj z) / 2 :=
    funext (rotatedFirstCoordinate_eq_exp z)
  rw [he]
  fun_prop

theorem angularWeight_mul_rotation_exp (m : ℤ) (θ : ℝ) :
    helmholtzAngularWeight m θ * Complex.exp ((θ : ℂ) * Complex.I) =
      helmholtzAngularWeight (m - 1) θ := by
  unfold helmholtzAngularWeight
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem angularWeight_mul_rotation_exp_neg (m : ℤ) (θ : ℝ) :
    helmholtzAngularWeight m θ * Complex.exp (-((θ : ℂ) * Complex.I)) =
      helmholtzAngularWeight (m + 1) θ := by
  unfold helmholtzAngularWeight
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem angularWeight_mul_rotatedFirstCoordinate (m : ℤ) (z : ℂ) (θ : ℝ) :
    helmholtzAngularWeight m θ * rotatedFirstCoordinate z θ =
      (z / 2) * helmholtzAngularWeight (m - 1) θ +
        (conj z / 2) * helmholtzAngularWeight (m + 1) θ := by
  rw [rotatedFirstCoordinate_eq_exp]
  calc
    _ = (z / 2) * (helmholtzAngularWeight m θ * Complex.exp ((θ : ℂ) * Complex.I)) +
        (conj z / 2) * (helmholtzAngularWeight m θ * Complex.exp (-((θ : ℂ) * Complex.I))) := by ring
    _ = _ := by rw [angularWeight_mul_rotation_exp, angularWeight_mul_rotation_exp_neg]

/-- The actual integral of a nonconstant integer character over a full turn. -/
theorem integral_angularWeight_eq_zero {m : ℤ} (hm : m ≠ 0) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), helmholtzAngularWeight m θ) = 0 := by
  have hc : -Complex.I * (m : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Int.cast_ne_zero.mpr hm)
  have hend := helmholtzAngularWeight_period_endpoints m
  change Complex.exp ((-Complex.I * (m : ℂ)) * ((2 * Real.pi : ℝ) : ℂ)) =
    Complex.exp ((-Complex.I * (m : ℂ)) * ((0 : ℝ) : ℂ)) at hend
  unfold helmholtzAngularWeight
  rw [integral_exp_mul_complex hc, hend, sub_self, zero_div]

theorem natAbs_le_natAbs_sub_one_add_one (m : ℤ) :
    m.natAbs ≤ (m - 1).natAbs + 1 := by
  have hh := Int.natAbs_add_le (m - 1) 1
  simpa only [show m - 1 + 1 = m by ring, Int.natAbs_one] using hh

theorem natAbs_le_natAbs_add_one_add_one (m : ℤ) :
    m.natAbs ≤ (m + 1).natAbs + 1 := by
  have hh := Int.natAbs_add_le (m + 1) (-1)
  simpa only [show m + 1 + -1 = m by ring, Int.natAbs_neg, Int.natAbs_one] using hh

/-- Every degree-n monomial has angular frequencies only between -n and n.
The induction is the actual two-character expansion of the rotated coordinate. -/
theorem integral_angularWeight_mul_coordinate_pow_eq_zero (n : ℕ) (m : ℤ)
    (hm : n < m.natAbs) (z : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      helmholtzAngularWeight m θ * rotatedFirstCoordinate z θ ^ n) = 0 := by
  induction n generalizing m with
  | zero =>
      simp only [pow_zero, mul_one]
      apply integral_angularWeight_eq_zero
      intro hmzero
      simp only [hmzero, Int.natAbs_zero] at hm
      omega
  | succ n ih =>
      have hmminus : n < (m - 1).natAbs := by
        have hh := natAbs_le_natAbs_sub_one_add_one m
        omega
      have hmplus : n < (m + 1).natAbs := by
        have hh := natAbs_le_natAbs_add_one_add_one m
        omega
      have hp : IntervalIntegrable (fun θ : ℝ => (z / 2) *
          (helmholtzAngularWeight (m - 1) θ * rotatedFirstCoordinate z θ ^ n))
          volume 0 (2 * Real.pi) :=
        (((continuous_helmholtzAngularWeight (m - 1)).mul
          ((continuous_rotatedFirstCoordinate z).pow n)).const_mul (z / 2)).intervalIntegrable _ _
      have hn : IntervalIntegrable (fun θ : ℝ => (conj z / 2) *
          (helmholtzAngularWeight (m + 1) θ * rotatedFirstCoordinate z θ ^ n))
          volume 0 (2 * Real.pi) :=
        (((continuous_helmholtzAngularWeight (m + 1)).mul
          ((continuous_rotatedFirstCoordinate z).pow n)).const_mul (conj z / 2)).intervalIntegrable _ _
      calc
        _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
            (z / 2) * (helmholtzAngularWeight (m - 1) θ * rotatedFirstCoordinate z θ ^ n) +
              (conj z / 2) * (helmholtzAngularWeight (m + 1) θ * rotatedFirstCoordinate z θ ^ n) := by
          apply intervalIntegral.integral_congr
          intro θ _
          dsimp only
          calc
            _ = (helmholtzAngularWeight m θ * rotatedFirstCoordinate z θ) *
                rotatedFirstCoordinate z θ ^ n := by rw [pow_succ]; ring
            _ = _ := by rw [angularWeight_mul_rotatedFirstCoordinate]; ring
        _ = _ := by
          rw [intervalIntegral.integral_add hp hn,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            ih (m - 1) hmminus, ih (m + 1) hmplus, mul_zero, mul_zero, add_zero]

/-- The actual angular Fourier projection annihilates every coordinate
polynomial whose degree is smaller than the absolute integer mode. -/
theorem angularFourierAt_coordinate_polynomial_eq_zero (p : Polynomial ℂ) (m : ℤ)
    (hm : p.natDegree < m.natAbs) (z : ℂ) :
    angularFourierAt (fun x : Plane => p.eval (x 0 : ℂ)) m z = 0 := by
  change (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    helmholtzAngularWeight m θ * p.eval (rotatedFirstCoordinate z θ)) = 0
  have hi (k : ℕ) (_hk : k ∈ Finset.range m.natAbs) :
      IntervalIntegrable (fun θ : ℝ => p.coeff k *
        (helmholtzAngularWeight m θ * rotatedFirstCoordinate z θ ^ k)) volume 0 (2 * Real.pi) :=
    (((continuous_helmholtzAngularWeight m).mul ((continuous_rotatedFirstCoordinate z).pow k)).const_mul
      (p.coeff k)).intervalIntegrable _ _
  calc
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ∑ k ∈ Finset.range m.natAbs, p.coeff k *
          (helmholtzAngularWeight m θ * rotatedFirstCoordinate z θ ^ k) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [Polynomial.eval_eq_sum_range' hm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k ∈ Finset.range m.natAbs, ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        p.coeff k * (helmholtzAngularWeight m θ * rotatedFirstCoordinate z θ ^ k) :=
      intervalIntegral.integral_finsetSum hi
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [intervalIntegral.integral_const_mul,
        integral_angularWeight_mul_coordinate_pow_eq_zero k m (Finset.mem_range.mp hk) z, mul_zero]

/-- The same statement with an arbitrary point of the actual real plane as
the projection center parameter, including the origin. -/
theorem angularFourierAt_coordinate_polynomial_eq_zero_on_plane (p : Polynomial ℂ) (m : ℤ)
    (hm : p.natDegree < m.natAbs) (x : Plane) :
    angularFourierAt (fun y : Plane => p.eval (y 0 : ℂ)) m (complexToPlane.symm x) = 0 :=
  angularFourierAt_coordinate_polynomial_eq_zero p m hm _

end J0RadialUniqueness
