import Solutions.J0RadialUniqueness.AmplitudeAnalytic
import Solutions.J0RadialUniqueness.K0Connection
import Solutions.J0RadialUniqueness.BranchGeometry

/-!
The exact J₀ decomposition, reduced only to identification of the two
independently defined K₀ functions. Principal-branch rotations and all phase
constants are proved here rather than supplied as additional assumptions.
-/

noncomputable section

namespace J0RadialUniqueness

theorem log_I_mul_rightHalf {z : ℂ} (hz : 0 < z.re) :
    Complex.log (Complex.I * z) = Complex.log z + (Real.pi : ℂ) * Complex.I / 2 := by
  have hz0 := rightHalfPlane_ne_zero hz
  have hlo : -(Real.pi / 2) < z.arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz)
  have hhi : z.arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hb : Complex.I.arg + z.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_I]
    constructor <;> linarith [Real.pi_pos]
  calc
    Complex.log (Complex.I * z) = Complex.log Complex.I + Complex.log z :=
      Complex.log_mul Complex.I_ne_zero hz0 hb
    _ = Complex.log z + (Real.pi : ℂ) * Complex.I / 2 := by
      rw [Complex.log_I]
      ring

theorem log_negI_mul_rightHalf {z : ℂ} (hz : 0 < z.re) :
    Complex.log (-Complex.I * z) = Complex.log z - (Real.pi : ℂ) * Complex.I / 2 := by
  have hz0 := rightHalfPlane_ne_zero hz
  have hlo : -(Real.pi / 2) < z.arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz)
  have hhi : z.arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hb : (-Complex.I).arg + z.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_I]
    constructor <;> linarith [Real.pi_pos]
  calc
    Complex.log (-Complex.I * z) = Complex.log (-Complex.I) + Complex.log z :=
      Complex.log_mul (neg_ne_zero.mpr Complex.I_ne_zero) hz0 hb
    _ = Complex.log z - (Real.pi : ℂ) * Complex.I / 2 := by
      rw [Complex.log_neg_I]
      ring

/-- The negative half-power rotation is on the principal branch throughout H₊. -/
theorem cpow_I_mul_neg_half {z : ℂ} (hz : 0 < z.re) :
    Complex.cpow (Complex.I * z) (-1 / 2 : ℂ) =
      Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) * Complex.cpow z (-1 / 2 : ℂ) := by
  have hz0 := rightHalfPlane_ne_zero hz
  change (Complex.I * z) ^ (-1 / 2 : ℂ) =
    Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) * z ^ (-1 / 2 : ℂ)
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero Complex.I_ne_zero hz0),
    Complex.cpow_def_of_ne_zero hz0, log_I_mul_rightHalf hz, ← Complex.exp_add]
  congr 1
  ring

theorem cpow_negI_mul_neg_half {z : ℂ} (hz : 0 < z.re) :
    Complex.cpow (-Complex.I * z) (-1 / 2 : ℂ) =
      Complex.exp (Complex.I * (Real.pi : ℂ) / 4) * Complex.cpow z (-1 / 2 : ℂ) := by
  have hz0 := rightHalfPlane_ne_zero hz
  change (-Complex.I * z) ^ (-1 / 2 : ℂ) =
    Complex.exp (Complex.I * (Real.pi : ℂ) / 4) * z ^ (-1 / 2 : ℂ)
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0),
    Complex.cpow_def_of_ne_zero hz0, log_negI_mul_rightHalf hz, ← Complex.exp_add]
  congr 1
  ring

theorem quarter_phase_plus :
    Complex.exp (Complex.I * (Real.pi : ℂ) / 4) =
      Complex.I * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) := by
  have hi : Complex.exp (Complex.I * (Real.pi : ℂ) / 2) = Complex.I := by
    convert Complex.exp_pi_div_two_mul_I using 1 <;> congr 1 <;> ring
  calc
    _ = Complex.exp (Complex.I * (Real.pi : ℂ) / 2 +
        -Complex.I * (Real.pi : ℂ) / 4) := by congr 1; ring
    _ = Complex.exp (Complex.I * (Real.pi : ℂ) / 2) *
        Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) := Complex.exp_add _ _
    _ = _ := by rw [hi]

theorem quarter_phase_minus :
    Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) =
      -Complex.I * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) := by
  have hi : Complex.exp (-Complex.I * (Real.pi : ℂ) / 2) = -Complex.I := by
    convert Complex.exp_neg_pi_div_two_mul_I using 1 <;> congr 1 <;> ring
  calc
    _ = Complex.exp (-Complex.I * (Real.pi : ℂ) / 2 +
        Complex.I * (Real.pi : ℂ) / 4) := by congr 1; ring
    _ = Complex.exp (-Complex.I * (Real.pi : ℂ) / 2) *
        Complex.exp (Complex.I * (Real.pi : ℂ) / 4) := Complex.exp_add _ _
    _ = _ := by rw [hi]

theorem log_pi_div_two_mul {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    Complex.log ((Real.pi : ℂ) / (2 * w)) =
      (Real.log (Real.pi / 2) : ℂ) - Complex.log w := by
  have hw0 := Complex.slitPlane_ne_zero hw
  have halg : (Real.pi : ℂ) / (2 * w) = ((Real.pi / 2 : ℝ) : ℂ) * w⁻¹ := by
    push_cast
    field_simp [hw0] <;> ring
  rw [halg, Complex.log_ofReal_mul (div_pos Real.pi_pos (by norm_num)) (inv_ne_zero hw0),
    Complex.log_inv w (Complex.slitPlane_arg_ne_pi hw)]
  ring

theorem log_two_pi_mul {z : ℂ} (hz : z ≠ 0) :
    Complex.log (2 * (Real.pi : ℂ) * z) =
      (Real.log (2 * Real.pi) : ℂ) + Complex.log z := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
    (Complex.log_ofReal_mul (r := 2 * Real.pi) (mul_pos (by norm_num) Real.pi_pos) hz)

theorem log_pi_halves_sum :
    (Real.log (Real.pi / 2) : ℂ) + (Real.log (2 * Real.pi) : ℂ) =
      2 * (Real.log Real.pi : ℂ) := by
  have h : Real.log (Real.pi / 2) + Real.log (2 * Real.pi) = 2 * Real.log Real.pi := by
    rw [Real.log_div Real.pi_ne_zero (by norm_num),
      Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  exact_mod_cast h

/-- Product normalization avoids any unrestricted multiplicativity claim for square roots. -/
theorem laplace_prefactor_plus_product {z : ℂ} (hz : 0 < z.re) :
    Complex.cpow ((Real.pi : ℂ) / (2 * (-Complex.I * z))) (1 / 2 : ℂ) *
      Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ) =
        (Real.pi : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) := by
  have hz0 := rightHalfPlane_ne_zero hz
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw0 : -Complex.I * z ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  have hp0 : (Real.pi : ℂ) / (2 * (-Complex.I * z)) ≠ 0 :=
    div_ne_zero hpi0 (mul_ne_zero (by norm_num) hw0)
  have hD0 : 2 * (Real.pi : ℂ) * z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hpi0) hz0
  change ((Real.pi : ℂ) / (2 * (-Complex.I * z))) ^ (1 / 2 : ℂ) *
    (2 * (Real.pi : ℂ) * z) ^ (1 / 2 : ℂ) = _
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hD0,
    ← Complex.exp_add, log_pi_div_two_mul (negI_mul_mem_slitPlane hz),
    log_two_pi_mul hz0, log_negI_mul_rightHalf hz]
  calc
    _ = Complex.exp ((Real.log Real.pi : ℂ) + Complex.I * (Real.pi : ℂ) / 4) := by
      congr 1
      linear_combination (1 / 2 : ℂ) * log_pi_halves_sum
    _ = (Real.pi : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log Real.pi_pos]

theorem laplace_prefactor_minus_product {z : ℂ} (hz : 0 < z.re) :
    Complex.cpow ((Real.pi : ℂ) / (2 * (Complex.I * z))) (1 / 2 : ℂ) *
      Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ) =
        (Real.pi : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) := by
  have hz0 := rightHalfPlane_ne_zero hz
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw0 : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hp0 : (Real.pi : ℂ) / (2 * (Complex.I * z)) ≠ 0 :=
    div_ne_zero hpi0 (mul_ne_zero (by norm_num) hw0)
  have hD0 : 2 * (Real.pi : ℂ) * z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hpi0) hz0
  change ((Real.pi : ℂ) / (2 * (Complex.I * z))) ^ (1 / 2 : ℂ) *
    (2 * (Real.pi : ℂ) * z) ^ (1 / 2 : ℂ) = _
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hD0,
    ← Complex.exp_add, log_pi_div_two_mul (I_mul_mem_slitPlane hz),
    log_two_pi_mul hz0, log_I_mul_rightHalf hz]
  calc
    _ = Complex.exp ((Real.log Real.pi : ℂ) - Complex.I * (Real.pi : ℂ) / 4) := by
      congr 1
      linear_combination (1 / 2 : ℂ) * log_pi_halves_sum
    _ = (Real.pi : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) := by
      rw [sub_eq_add_neg, Complex.exp_add, ← Complex.ofReal_exp,
        Real.exp_log Real.pi_pos]
      congr 2
      ring

theorem component_phase_plus (z : ℂ) :
    Complex.exp (Complex.I * (Real.pi : ℂ) / 4) * Complex.exp (Complex.I * z) =
      Complex.I * Complex.exp (Complex.I * (z - (Real.pi : ℂ) / 4)) := by
  rw [quarter_phase_plus]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem component_phase_minus (z : ℂ) :
    -(Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) * Complex.exp (-Complex.I * z)) =
      Complex.I * Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4)) := by
  rw [quarter_phase_minus]
  have harg : Complex.I * (Real.pi : ℂ) / 4 + -Complex.I * z =
      -Complex.I * (z - (Real.pi : ℂ) / 4) := by ring
  rw [mul_assoc, ← Complex.exp_add, harg]
  ring

/-- Proposition 3.2 reduced strictly to the remaining global K₀ identification. -/
theorem exactDecomposition_of_laplaceIdentification
    (hident : KLaplaceIdentificationStatement) : ExactDecompositionStatement := by
  intro z hz
  change 0 < z.re at hz
  let D : ℂ := Complex.cpow (2 * (Real.pi : ℂ) * z) (1 / 2 : ℂ)
  let P : ℂ := Complex.cpow ((Real.pi : ℂ) / (2 * (-Complex.I * z))) (1 / 2 : ℂ)
  let M : ℂ := Complex.cpow ((Real.pi : ℂ) / (2 * (Complex.I * z))) (1 / 2 : ℂ)
  have hplus : laplaceK (-Complex.I * z) = P * Complex.exp (Complex.I * z) * APlus z := by
    unfold laplaceK
    rw [← APlus_eq_laplaceI]
    simp only [P, neg_mul, neg_neg]
  have hminus : laplaceK (Complex.I * z) = M * Complex.exp (-Complex.I * z) * AMinus z := by
    unfold laplaceK
    rw [← AMinus_eq_laplaceI]
    simp only [M, neg_mul]
  have hconn := K0_connection z hz
  rw [← hident _ (negI_mul_mem_slitPlane hz), ← hident _ (I_mul_mem_slitPlane hz),
    hplus, hminus] at hconn
  have hP : P * D = (Real.pi : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4) :=
    laplace_prefactor_plus_product hz
  have hM : M * D = (Real.pi : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4) :=
    laplace_prefactor_minus_product hz
  have hscaled : ((Real.pi : ℂ) * Complex.I) * (J0 z * D) =
      (P * D) * Complex.exp (Complex.I * z) * APlus z -
        (M * D) * Complex.exp (-Complex.I * z) * AMinus z := by
    linear_combination D * hconn
  rw [hP, hM] at hscaled
  have hphases :
      ((Real.pi : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) *
          Complex.exp (Complex.I * z) * APlus z -
        ((Real.pi : ℂ) * Complex.exp (-Complex.I * (Real.pi : ℂ) / 4)) *
          Complex.exp (-Complex.I * z) * AMinus z =
      ((Real.pi : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * (z - (Real.pi : ℂ) / 4)) * APlus z +
          Complex.exp (-Complex.I * (z - (Real.pi : ℂ) / 4)) * AMinus z) := by
    have hp := component_phase_plus z
    have hm := component_phase_minus z
    linear_combination (Real.pi : ℂ) * APlus z * hp +
      (Real.pi : ℂ) * AMinus z * hm
  rw [hphases] at hscaled
  have hpiI : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  have hnum := (mul_right_inj' hpiI).mp hscaled
  have hD : D ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl
    (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (rightHalfPlane_ne_zero hz)))
  exact (eq_div_iff hD).2 hnum

end J0RadialUniqueness
