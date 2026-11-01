import Definitions.J0RadialUniqueness.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The actual principal-branch Laplace kernel on the entire slit plane.
The real integration parameter is nonnegative throughout the branch lemmas.
No compactness estimate or Bessel identification is assumed here.
-/

noncomputable section

namespace J0RadialUniqueness

def laplaceBase (w : ℂ) (t : ℝ) : ℂ := 1 + (t : ℂ) / (2 * w)

theorem laplaceBase_mem_slitPlane {w : ℂ} {t : ℝ}
    (hw : w ∈ Complex.slitPlane) (ht : 0 ≤ t) :
    laplaceBase w t ∈ Complex.slitPlane := by
  by_cases ht0 : t = 0
  · simpa only [laplaceBase, ht0, Complex.ofReal_zero, zero_div, add_zero] using
      Complex.one_mem_slitPlane
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have hd0 : 2 * w ≠ 0 := mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hw0
  have hn0 : Complex.normSq (2 * w) ≠ 0 := (Complex.normSq_pos.mpr hd0).ne'
  rw [Complex.mem_slitPlane_iff] at hw ⊢
  rcases hw with hwr | hwi
  · left
    have hre : (laplaceBase w t).re =
        1 + (t * (2 * w.re)) / Complex.normSq (2 * w) := by
      simp [laplaceBase, Complex.div_re, Complex.mul_re]
    rw [hre]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (mul_nonneg ht (mul_nonneg (by norm_num) hwr.le))
        (Complex.normSq_nonneg _))
  · right
    have him : (laplaceBase w t).im =
        -(t * (2 * w.im)) / Complex.normSq (2 * w) := by
      simp [laplaceBase, Complex.div_im, Complex.mul_im] <;> ring
    rw [him]
    exact div_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero htpos.ne'
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hwi))) hn0

theorem laplaceBase_ne_zero {w : ℂ} {t : ℝ}
    (hw : w ∈ Complex.slitPlane) (ht : 0 ≤ t) : laplaceBase w t ≠ 0 :=
  Complex.slitPlane_ne_zero (laplaceBase_mem_slitPlane hw ht)

theorem laplaceBase_hasDerivAt {w : ℂ} (hw : w ≠ 0) (t : ℝ) :
    HasDerivAt (fun v : ℂ => laplaceBase v t) (-(t : ℂ) / (2 * w ^ 2)) w := by
  have hd := (hasDerivAt_id w).const_mul (2 : ℂ)
  have hq := (hasDerivAt_const w (t : ℂ)).div hd
    (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hw)
  have hb := hq.const_add 1
  change HasDerivAt (fun v : ℂ => laplaceBase v t)
    ((0 * (2 * w) - (t : ℂ) * (2 * 1)) / (2 * w) ^ 2) w at hb
  apply hb.congr_deriv
  field_simp [hw] <;> ring

/-- Differentiation on the fixed principal branch, with the original actual kernel. -/
theorem laplaceKernel_hasDerivAt {w : ℂ} {t : ℝ}
    (hw : w ∈ Complex.slitPlane) (ht : 0 ≤ t) :
    HasDerivAt (fun v : ℂ => laplaceKernel v t)
      ((t : ℂ) / (4 * w ^ 2) * Complex.cpow (laplaceBase w t) (-3 / 2 : ℂ)) w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have h := (laplaceBase_hasDerivAt hw0 t).cpow_const
    (c := (-1 / 2 : ℂ)) (laplaceBase_mem_slitPlane hw ht)
  change HasDerivAt (fun v : ℂ => laplaceKernel v t)
    ((-1 / 2 : ℂ) * Complex.cpow (laplaceBase w t) ((-1 / 2 : ℂ) - 1) *
      (-(t : ℂ) / (2 * w ^ 2))) w at h
  apply h.congr_deriv
  rw [show (-1 / 2 : ℂ) - 1 = -3 / 2 by norm_num]
  field_simp [hw0] <;> ring

/-- The equivalent derivative form used by the differentiated integral. -/
theorem laplaceKernel_hasDerivAt_moment {w : ℂ} {t : ℝ}
    (hw : w ∈ Complex.slitPlane) (ht : 0 ≤ t) :
    HasDerivAt (fun v : ℂ => laplaceKernel v t)
      ((1 / (4 * w ^ 2)) * laplaceMomentKernel w t) w := by
  apply (laplaceKernel_hasDerivAt hw ht).congr_deriv
  dsimp only [laplaceMomentKernel, laplaceBase]
  ring

theorem laplaceBase_continuous_t (w : ℂ) : Continuous (laplaceBase w) :=
  continuous_const.add (Complex.continuous_ofReal.div_const (2 * w))

theorem laplaceKernel_continuousOn_t_Ici {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContinuousOn (laplaceKernel w) (Set.Ici (0 : ℝ)) := by
  change ContinuousOn
    (fun t : ℝ => Complex.cpow (laplaceBase w t) (-1 / 2 : ℂ)) (Set.Ici 0)
  exact (laplaceBase_continuous_t w).continuousOn.cpow_const
    (fun _ ht => laplaceBase_mem_slitPlane hw ht)

theorem laplaceMomentKernel_continuousOn_t_Ici {w : ℂ}
    (hw : w ∈ Complex.slitPlane) :
    ContinuousOn (laplaceMomentKernel w) (Set.Ici (0 : ℝ)) := by
  change ContinuousOn
    (fun t : ℝ => (t : ℂ) * Complex.cpow (laplaceBase w t) (-3 / 2 : ℂ)) (Set.Ici 0)
  exact Complex.continuous_ofReal.continuousOn.mul
    ((laplaceBase_continuous_t w).continuousOn.cpow_const
      (fun _ ht => laplaceBase_mem_slitPlane hw ht))

theorem laplaceKernel_continuousOn_t {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContinuousOn (laplaceKernel w) (Set.Ioi (0 : ℝ)) :=
  (laplaceKernel_continuousOn_t_Ici hw).mono Set.Ioi_subset_Ici_self

theorem laplaceMomentKernel_continuousOn_t {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContinuousOn (laplaceMomentKernel w) (Set.Ioi (0 : ℝ)) :=
  (laplaceMomentKernel_continuousOn_t_Ici hw).mono Set.Ioi_subset_Ici_self

theorem norm_cpow_le_of_norm_lower_bound {v : ℂ} {a b : ℝ}
    (ha : 0 < a) (hv : a ≤ ‖v‖) (hb : b ≤ 0) :
    ‖Complex.cpow v (b : ℂ)‖ ≤ Real.rpow a b := by
  change ‖v ^ (b : ℂ)‖ ≤ Real.rpow a b
  rw [Complex.norm_cpow_real]
  exact Real.rpow_le_rpow_of_nonpos ha hv hb

theorem norm_cpow_neg_half_le_of_lower_bound {v : ℂ} {a : ℝ}
    (ha : 0 < a) (hv : a ≤ ‖v‖) :
    ‖Complex.cpow v (-1 / 2 : ℂ)‖ ≤ Real.rpow a (-1 / 2 : ℝ) := by
  simpa using norm_cpow_le_of_norm_lower_bound (b := (-1 / 2 : ℝ)) ha hv (by norm_num)

theorem norm_cpow_neg_three_halves_le_of_lower_bound {v : ℂ} {a : ℝ}
    (ha : 0 < a) (hv : a ≤ ‖v‖) :
    ‖Complex.cpow v (-3 / 2 : ℂ)‖ ≤ Real.rpow a (-3 / 2 : ℝ) := by
  simpa using norm_cpow_le_of_norm_lower_bound (b := (-3 / 2 : ℝ)) ha hv (by norm_num)

theorem laplaceKernel_norm_le_of_base_lower_bound {w : ℂ} {t a : ℝ}
    (ha : 0 < a) (hbase : a ≤ ‖laplaceBase w t‖) :
    ‖laplaceKernel w t‖ ≤ Real.rpow a (-1 / 2 : ℝ) :=
  norm_cpow_neg_half_le_of_lower_bound ha hbase

theorem laplaceMomentKernel_norm_le_of_base_lower_bound {w : ℂ} {t a : ℝ}
    (ht : 0 ≤ t) (ha : 0 < a) (hbase : a ≤ ‖laplaceBase w t‖) :
    ‖laplaceMomentKernel w t‖ ≤ t * Real.rpow a (-3 / 2 : ℝ) := by
  change ‖(t : ℂ) * Complex.cpow (laplaceBase w t) (-3 / 2 : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (norm_cpow_neg_three_halves_le_of_lower_bound ha hbase) ht

end J0RadialUniqueness
