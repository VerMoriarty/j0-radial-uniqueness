import Solutions.J0RadialUniqueness.K0SeriesAnalytic
import Solutions.J0RadialUniqueness.FRightHalfPlane

/-! The endpoints of the manuscript's displayed connection formula.
With the principal logarithm, the upper imaginary endpoint has the displayed
sign, whereas the lower endpoint requires the lower bank of the negative-real
cut. The latter bank is proved to be an actual one-sided limit. In particular
the unqualified principal-value formula at both endpoints is false. -/

noncomputable section
open Set Filter
open scoped Topology

namespace J0RadialUniqueness

theorem log_neg_real_pos (y : ℝ) (hy : 0 < y) :
    Complex.log (-(y : ℂ)) = Complex.log (y : ℂ) + (Real.pi : ℂ) * Complex.I := by
  have ha : Complex.arg (-(y : ℂ)) = Real.pi := by
    rw [← Complex.ofReal_neg]
    exact Complex.arg_ofReal_of_neg (by linarith)
  simp only [Complex.log, norm_neg, ha, Complex.arg_ofReal_of_nonneg hy.le,
    Complex.ofReal_zero, zero_mul, add_zero]

theorem K0Series_negative_real_jump (y : ℝ) (hy : 0 < y) :
    K0Series (-(y : ℂ)) - K0Series (y : ℂ) =
      -(Real.pi : ℂ) * Complex.I * F ((y : ℂ) ^ 2 / 4) := by
  have hlog : Complex.log (-(y : ℂ) / 2) =
      Complex.log ((y : ℂ) / 2) + (Real.pi : ℂ) * Complex.I := by
    have hh := log_neg_real_pos (y / 2) (by positivity)
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, neg_div] using hh
  unfold K0Series
  rw [neg_sq, hlog]
  ring

theorem J0_imaginary_eq_F (y : ℝ) :
    J0 (Complex.I * (y : ℂ)) = F ((y : ℂ) ^ 2 / 4) := by
  unfold J0
  congr 1
  rw [mul_pow, Complex.I_sq]
  ring

theorem K0_connection_upper_imaginary (y : ℝ) (hy : 0 < y) :
    (Real.pi : ℂ) * Complex.I * J0 (Complex.I * (y : ℂ)) =
      K0Series (-Complex.I * (Complex.I * (y : ℂ))) -
        K0Series (Complex.I * (Complex.I * (y : ℂ))) := by
  have hp : -Complex.I * (Complex.I * (y : ℂ)) = (y : ℂ) := by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I]; ring
  have hm : Complex.I * (Complex.I * (y : ℂ)) = -(y : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  rw [hp, hm, J0_imaginary_eq_F]
  linear_combination K0Series_negative_real_jump y hy

theorem K0_connection_lower_imaginary_principal (y : ℝ) (hy : 0 < y) :
    K0Series (-Complex.I * (-Complex.I * (y : ℂ))) -
        K0Series (Complex.I * (-Complex.I * (y : ℂ))) =
      -(Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ)) := by
  have hp : -Complex.I * (-Complex.I * (y : ℂ)) = -(y : ℂ) := by
    ring_nf; simp [Complex.I_sq]
  have hm : Complex.I * (-Complex.I * (y : ℂ)) = (y : ℂ) := by
    ring_nf; simp [Complex.I_sq]
  have hJ : J0 (-Complex.I * (y : ℂ)) = F ((y : ℂ) ^ 2 / 4) := by
    rw [show -Complex.I * (y : ℂ) = -(Complex.I * (y : ℂ)) by ring,
      J0_neg, J0_imaginary_eq_F]
  rw [hp, hm, hJ]
  exact K0Series_negative_real_jump y hy

/-- Actual lower-bank value on the negative-real cut. -/
def K0LowerBank (w : ℂ) : ℂ :=
  K0Series w + 2 * (Real.pi : ℂ) * Complex.I * F (w ^ 2 / 4)

theorem K0Series_tendsto_lower_bank {w : ℂ} (hre : w.re < 0) (him : w.im = 0) :
    Tendsto K0Series (𝓝[{z : ℂ | z.im < 0}] w) (𝓝 (K0LowerBank w)) := by
  have hre2 : (w / 2).re < 0 := by simpa using div_neg_of_neg_of_pos hre (by norm_num : (0 : ℝ) < 2)
  have him2 : (w / 2).im = 0 := by simp [him]
  have hmap : Tendsto (fun z : ℂ => z / 2)
      (𝓝[{z : ℂ | z.im < 0}] w) (𝓝[{z : ℂ | z.im < 0}] (w / 2)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.div_const (2 : ℂ)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    change (z / 2).im < 0
    simpa using div_neg_of_neg_of_pos hz (by norm_num : (0 : ℝ) < 2)
  have hlog := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre2 him2).comp hmap
  have he : (Real.log ‖w / 2‖ : ℂ) - (Real.pi : ℂ) * Complex.I =
      Complex.log (w / 2) - 2 * (Real.pi : ℂ) * Complex.I := by
    rw [Complex.log, Complex.arg_eq_pi_iff.mpr ⟨hre2, him2⟩]
    ring
  rw [he] at hlog
  have hF : Tendsto (fun z : ℂ => F (z ^ 2 / 4))
      (𝓝[{z : ℂ | z.im < 0}] w) (𝓝 (F (w ^ 2 / 4))) :=
    (modifiedI0_analyticAt w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hH : Tendsto (fun z : ℂ => harmonicF (z ^ 2 / 4))
      (𝓝[{z : ℂ | z.im < 0}] w) (𝓝 (harmonicF (w ^ 2 / 4))) :=
    (K0Correction_analyticAt w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh := (((hlog.add_const (Real.eulerMascheroniConstant : ℂ)).neg).mul hF).add hH
  convert! hh using 1
  congr 1
  unfold K0LowerBank K0Series harmonicF
  ring

theorem K0_connection_lower_imaginary_bank (y : ℝ) (hy : 0 < y) :
    (Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ)) =
      K0LowerBank (-Complex.I * (-Complex.I * (y : ℂ))) -
        K0Series (Complex.I * (-Complex.I * (y : ℂ))) := by
  have harg : (-Complex.I * (-Complex.I * (y : ℂ))) ^ 2 / 4 =
      -(-Complex.I * (y : ℂ)) ^ 2 / 4 := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  have hh := K0_connection_lower_imaginary_principal y hy
  unfold K0LowerBank
  rw [harg]
  change _ = _ + 2 * (Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ)) - _
  linear_combination -hh

/-- The manuscript's closed lower endpoint cannot mean two principal values.
This is a refutation at every nonzero point of that endpoint, rather than an
unproved warning about a possible branch issue. -/
theorem K0_connection_lower_imaginary_principal_false (y : ℝ) (hy : 0 < y) :
    (Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ)) ≠
      K0Series (-Complex.I * (-Complex.I * (y : ℂ))) -
        K0Series (Complex.I * (-Complex.I * (y : ℂ))) := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hF := F_rightHalfPlane ((y : ℂ) ^ 2 / 4)
    (div_ne_zero (pow_ne_zero 2 hyC) (by norm_num))
    (show (0 : ℝ) ≤ ((y : ℂ) ^ 2 / 4).re by
      simpa only [Complex.div_ofNat_re, pow_two, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero] using
          (div_nonneg (sq_nonneg y) (by norm_num : (0 : ℝ) ≤ 4)))
  have hJ : J0 (-Complex.I * (y : ℂ)) ≠ 0 := by
    rw [show -Complex.I * (y : ℂ) = -(Complex.I * (y : ℂ)) by ring,
      J0_neg, J0_imaginary_eq_F]
    intro he
    rw [he, norm_zero] at hF
    linarith
  have hn : (Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero) hJ
  intro he
  have hp := K0_connection_lower_imaginary_principal y hy
  have hz : 2 * ((Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ))) = 0 := by
    linear_combination he + hp
  exact (mul_ne_zero (by norm_num) hn) hz

/-- All nonzero imaginary endpoint obligations, including the actual lower
bank limit and the explicit failure of the unqualified principal-value claim. -/
theorem paper_k0_boundary_connection (y : ℝ) (hy : 0 < y) :
    ((Real.pi : ℂ) * Complex.I * J0 (Complex.I * (y : ℂ)) =
      K0Series (-Complex.I * (Complex.I * (y : ℂ))) -
        K0Series (Complex.I * (Complex.I * (y : ℂ)))) ∧
    ((Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ)) =
      (K0Series (-Complex.I * (-Complex.I * (y : ℂ))) +
        2 * (Real.pi : ℂ) * Complex.I * F (((-Complex.I * (-Complex.I * (y : ℂ))) ^ 2) / 4)) -
        K0Series (Complex.I * (-Complex.I * (y : ℂ)))) ∧
    Tendsto K0Series (𝓝[{z : ℂ | z.im < 0}] (-(y : ℂ)))
      (𝓝 (K0Series (-(y : ℂ)) +
        2 * (Real.pi : ℂ) * Complex.I * F ((-(y : ℂ)) ^ 2 / 4))) ∧
    ((Real.pi : ℂ) * Complex.I * J0 (-Complex.I * (y : ℂ)) ≠
      K0Series (-Complex.I * (-Complex.I * (y : ℂ))) -
        K0Series (Complex.I * (-Complex.I * (y : ℂ)))) := by
  exact ⟨K0_connection_upper_imaginary y hy, K0_connection_lower_imaginary_bank y hy,
    K0Series_tendsto_lower_bank (by simp; linarith) (by simp),
    K0_connection_lower_imaginary_principal_false y hy⟩

end J0RadialUniqueness
