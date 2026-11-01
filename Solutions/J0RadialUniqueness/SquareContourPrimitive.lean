import Solutions.J0RadialUniqueness.SquareContourAlgebra
import Solutions.J0RadialUniqueness.FiniteHigherPoleSubtraction
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Actual primitive integrals on the four square edges. The primitive need
not be defined holomorphically at interior poles: only its derivatives on the
boundary are used. In particular every inverse power except the first has
zero contour integral, with the first normalized by the proved winding
calculation. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Interval

namespace J0RadialUniqueness

theorem squareBoundaryIntegral_eq_zero_of_primitive {a : ℝ} (ha : 0 ≤ a)
    (G G' : ℂ → ℂ) (hG : ∀ z ∈ squareBoundarySet a, HasDerivAt G (G' z) z)
    (hi : SquareBoundaryIntegrable a G') : squareBoundaryIntegral a G' = 0 := by
  have hb : (∫ t : ℝ in -a..a, G' ((t : ℂ) - (a : ℂ) * Complex.I)) =
      G ((a : ℂ) - (a : ℂ) * Complex.I) - G ((-a : ℝ) - (a : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => G ((t : ℂ) - (a : ℂ) * Complex.I)) _ hi.bottom
    intro t ht
    have hp := ((hG _ (squareBoundary_edge_mem ha ht).1).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).sub_const ((a : ℂ) * Complex.I))).comp_ofReal
    convert! hp using 1 <;> simp only [Function.comp_def, id_eq, sub_zero, mul_one]
  have ht : (∫ t : ℝ in -a..a, G' ((t : ℂ) + (a : ℂ) * Complex.I)) =
      G ((a : ℂ) + (a : ℂ) * Complex.I) - G ((-a : ℝ) + (a : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => G ((t : ℂ) + (a : ℂ) * Complex.I)) _ hi.top
    intro t ht
    have hp := ((hG _ (squareBoundary_edge_mem ha ht).2.1).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).add_const ((a : ℂ) * Complex.I))).comp_ofReal
    convert! hp using 1 <;> simp only [Function.comp_def, id_eq, add_zero, mul_one]
  have hr : Complex.I * (∫ t : ℝ in -a..a, G' ((a : ℂ) + (t : ℂ) * Complex.I)) =
      G ((a : ℂ) + (a : ℂ) * Complex.I) - G ((a : ℂ) + ((-a : ℝ) : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => G ((a : ℂ) + (t : ℂ) * Complex.I)) _ (hi.right.const_mul Complex.I)
    intro t ht
    have hp := ((hG _ (squareBoundary_edge_mem ha ht).2.2.1).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (a : ℂ))).comp_ofReal
    convert! hp using 1 <;>
      simp only [Function.comp_def, id_eq, one_mul, mul_one, zero_add] <;> ring
  have hl : Complex.I * (∫ t : ℝ in -a..a, G' (-(a : ℂ) + (t : ℂ) * Complex.I)) =
      G (-(a : ℂ) + (a : ℂ) * Complex.I) - G (-(a : ℂ) + ((-a : ℝ) : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => G (-(a : ℂ) + (t : ℂ) * Complex.I)) _ (hi.left.const_mul Complex.I)
    intro t ht
    have hp := ((hG _ (squareBoundary_edge_mem ha ht).2.2.2).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (-(a : ℂ)))).comp_ofReal
    convert! hp using 1 <;>
      simp only [Function.comp_def, id_eq, one_mul, mul_one, zero_add] <;> ring
  simp only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] at hb ht hr hl
  unfold squareBoundaryIntegral
  linear_combination hb - ht + hr - hl

theorem squareBoundary_ne_zero {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ squareBoundarySet a) : z ≠ 0 := by
  intro hzero
  subst z
  rcases hz with ⟨hh, _⟩ | ⟨hh, _⟩ <;>
    simp only [Complex.zero_re, Complex.zero_im, abs_zero] at hh <;> linarith

theorem inversePower_squareBoundaryIntegrable {a : ℝ} (ha : 0 < a) (k : ℕ) :
    SquareBoundaryIntegrable a (fun z : ℂ => 1 / z ^ k) := by
  apply squareBoundaryIntegrable_of_continuousOn ha.le
  have hh : AnalyticOnNhd ℂ (fun z : ℂ => 1 / z ^ k) (squareBoundarySet a) := by
    intro z hz
    exact analyticAt_const.div (analyticAt_id.pow k) (pow_ne_zero _ (squareBoundary_ne_zero ha hz))
  exact hh.continuousOn

theorem squareBoundaryIntegral_inversePower {a : ℝ} (ha : 0 < a) (k : ℕ) :
    squareBoundaryIntegral a (fun z : ℂ => 1 / z ^ k) =
      if k = 1 then 2 * (Real.pi : ℂ) * Complex.I else 0 := by
  by_cases hk : k = 1
  · subst k
    simp only [ite_true, pow_one, one_div]
    simpa only [sub_zero] using squareBoundaryIntegral_inv_sub ha
      (w := (0 : ℂ)) (by simpa using ha) (by simpa using ha)
  · rw [if_neg hk]
    let m : ℤ := 1 - (k : ℤ)
    have hm : m ≠ 0 := by
      dsimp only [m]
      intro h
      have hh : (k : ℤ) = 1 := by linarith
      exact hk (by exact_mod_cast hh)
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    apply squareBoundaryIntegral_eq_zero_of_primitive ha.le
      (fun z : ℂ => z ^ m / (m : ℂ)) _ _ (inversePower_squareBoundaryIntegrable ha k)
    intro z hz
    have hd := (hasDerivAt_zpow m z (Or.inl (squareBoundary_ne_zero ha hz))).div_const (m : ℂ)
    have he : m - 1 = -(k : ℤ) := by dsimp only [m]; ring
    convert! hd using 1
    rw [he, mul_div_cancel_left₀ _ hmC, zpow_neg, zpow_natCast, one_div]

/-- Integrating the explicitly constructed finite principal part retains
exactly the actual coefficient of the first inverse power. -/
theorem squareBoundaryIntegral_finiteLaurentPrincipalPart {a : ℝ} (ha : 0 < a)
    (f : ℂ → ℂ) (n : ℕ) (hn : 0 < n) :
    squareBoundaryIntegral a (finiteLaurentPrincipalPart f 0 n) =
      (2 * (Real.pi : ℂ) * Complex.I) * iteratedDSlope f 0 (n - 1) 0 := by
  unfold finiteLaurentPrincipalPart
  simp only [sub_zero, div_eq_mul_inv]
  have hf (k : ℕ) (_hk : k ∈ Finset.range n) : SquareBoundaryIntegrable a
      (fun z : ℂ => iteratedDSlope f 0 k 0 * (z ^ (n - k))⁻¹) := by
    have hi := inversePower_squareBoundaryIntegrable ha (n - k)
    have hc : SquareBoundaryIntegrable a
        (fun z : ℂ => iteratedDSlope f 0 k 0 * (1 / z ^ (n - k))) :=
      ⟨hi.bottom.const_mul _, hi.top.const_mul _, hi.right.const_mul _, hi.left.const_mul _⟩
    simpa only [one_div] using hc
  rw [squareBoundaryIntegral_sum (Finset.range n) _ hf]
  simp_rw [squareBoundaryIntegral_const_mul, ← one_div,
    squareBoundaryIntegral_inversePower ha]
  rw [Finset.sum_eq_single (n - 1)]
  · have hsub : n - (n - 1) = 1 := by omega
    simp only [hsub, ite_true]
    ring
  · intro b hb hbn
    have hne : n - b ≠ 1 := by have := Finset.mem_range.mp hb; omega
    simp only [if_neg hne, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

end J0RadialUniqueness
