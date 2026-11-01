import Solutions.J0RadialUniqueness.ChebyshevAbelKernel
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual weakly singular annular circular-mean kernel after extracting
the factor (p-s)^(-1/2). Its remaining factor is smooth on an open neighborhood
of every required compact square, and has strictly positive diagonal. The
circle/Fourier change of variables and the Abel inversion are separate tasks. -/

noncomputable section

open Set
open scoped ContDiff

namespace J0RadialUniqueness

def annularKernelDomain (r : ℝ) : Set (ℝ × ℝ) :=
  {v | r < v.1 ∧ 0 < v.2 ∧ |v.1 - 2 * r| < v.2}

def annularVolterraKernel (m : ℕ) (r : ℝ) (v : ℝ × ℝ) : ℝ :=
  (2 / Real.pi) * v.2 *
    chebyshevTValue m ((v.2 ^ 2 + (v.1 - r) ^ 2 - r ^ 2) / (2 * v.2 * (v.1 - r))) /
      Real.sqrt ((v.2 ^ 2 - (v.1 - 2 * r) ^ 2) * (v.1 + v.2))

theorem annularKernelDomain_isOpen (r : ℝ) : IsOpen (annularKernelDomain r) := by
  unfold annularKernelDomain
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.sub continuous_const).abs continuous_snd))

theorem annularKernelDomain_denominator_pos {r : ℝ} (hr : 0 < r)
    {v : ℝ × ℝ} (hv : v ∈ annularKernelDomain r) :
    0 < (v.2 ^ 2 - (v.1 - 2 * r) ^ 2) * (v.1 + v.2) := by
  have hpm := abs_lt.mp hv.2.2
  have hprod := mul_pos (sub_pos.mpr hpm.2) (by linarith : 0 < v.2 + (v.1 - 2 * r))
  have hsq : 0 < v.2 ^ 2 - (v.1 - 2 * r) ^ 2 := by nlinarith only [hprod]
  exact mul_pos hsq (by linarith [hv.1, hv.2.1])

theorem annularVolterraKernel_contDiffAt (m : ℕ) {r : ℝ} (hr : 0 < r)
    {v : ℝ × ℝ} (hv : v ∈ annularKernelDomain r) :
    ContDiffAt ℝ ∞ (annularVolterraKernel m r) v := by
  have hden : 2 * v.2 * (v.1 - r) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hv.2.1.ne') (sub_pos.mpr hv.1).ne'
  have harg : ContDiffAt ℝ ∞ (fun w : ℝ × ℝ =>
      (w.2 ^ 2 + (w.1 - r) ^ 2 - r ^ 2) / (2 * w.2 * (w.1 - r))) v := by
    apply ContDiffAt.div <;> try fun_prop
    exact hden
  have hT : ContDiff ℝ ∞ (chebyshevTValue m) := by
    convert! (Polynomial.Chebyshev.T ℝ (m : ℤ)).contDiff_aeval ∞ using 1 <;> rfl
  have hpoly : ContDiffAt ℝ ∞ (fun w : ℝ × ℝ =>
      (w.2 ^ 2 - (w.1 - 2 * r) ^ 2) * (w.1 + w.2)) v := by fun_prop
  have hp := annularKernelDomain_denominator_pos hr hv
  unfold annularVolterraKernel
  exact ((contDiffAt_const.mul contDiffAt_snd).mul (hT.contDiffAt.comp v harg)).div
    (hpoly.sqrt hp.ne') (Real.sqrt_pos.mpr hp).ne'

theorem annularVolterraKernel_contDiffOn (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ ∞ (annularVolterraKernel m r) (annularKernelDomain r) :=
  fun v hv => (annularVolterraKernel_contDiffAt m hr hv).contDiffWithinAt

theorem square_subset_annularKernelDomain {r a b : ℝ} (hr : 0 < r)
    (hra : r < a) (hb : b < a + r) :
    Icc a b ×ˢ Icc a b ⊆ annularKernelDomain r := by
  intro v hv
  refine ⟨by linarith [hv.1.1], by linarith [hv.2.1], ?_⟩
  apply abs_lt.mpr
  constructor <;> linarith [hv.1.1, hv.1.2, hv.2.1]

theorem annularVolterraKernel_continuousOn_square (m : ℕ) {r a b : ℝ} (hr : 0 < r)
    (hra : r < a) (hb : b < a + r) :
    ContinuousOn (annularVolterraKernel m r) (Icc a b ×ˢ Icc a b) :=
  ((annularVolterraKernel_contDiffOn m hr).mono
    (square_subset_annularKernelDomain hr hra hb)).continuousOn

theorem annularVolterraKernel_diagonal_pos (m : ℕ) {r p : ℝ} (hr : 0 < r) (hp : r < p) :
    0 < annularVolterraKernel m r (p, p) := by
  have hp0 : 0 < p := hr.trans hp
  have harg : (p ^ 2 + (p - r) ^ 2 - r ^ 2) / (2 * p * (p - r)) = 1 := by
    field_simp [hp0.ne', (sub_pos.mpr hp).ne']
    ring
  have hv : (p, p) ∈ annularKernelDomain r := by
    refine ⟨hp, hp0, abs_lt.mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> linarith
  have hden := annularKernelDomain_denominator_pos hr hv
  simp only [annularVolterraKernel, harg, chebyshevTValue, Polynomial.Chebyshev.T_eval_one, mul_one]
  exact div_pos (mul_pos (div_pos (by norm_num) Real.pi_pos) hp0)
    (Real.sqrt_pos.mpr hden)

theorem annularVolterraKernel_diagonal_uniform_pos (m : ℕ) {r a b : ℝ}
    (hr : 0 < r) (hra : r < a) (hb : b < a + r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Icc a b, ε ≤ annularVolterraKernel m r (p, p) := by
  have hc : ContinuousOn (fun p : ℝ => annularVolterraKernel m r (p, p)) (Icc a b) :=
    (annularVolterraKernel_continuousOn_square m hr hra hb).comp
      (continuous_id.prodMk continuous_id).continuousOn (fun p hp => ⟨hp, hp⟩)
  exact isCompact_Icc.exists_forall_le' hc
    (fun p hp => annularVolterraKernel_diagonal_pos m hr (lt_of_lt_of_le hra hp.1))

end J0RadialUniqueness
