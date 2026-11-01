import Solutions.J0RadialUniqueness.BesselSpectralResidueExpansion
import Solutions.J0RadialUniqueness.BesselCosineSeries
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Tactic

/-! Actual pairing and exhaustion of the finite spectral-box root sums.
The origin is explicitly removed before the ± pairing. Every remaining root
has nonzero real part by the proved localization theorem. The right-half-plane
sum is then exhausted by the actual expanding finite boxes, and its convergence
is certified by the proved weighted residue bounds and Bessel exponential bound. -/

noncomputable section

open Set Filter
open scoped Topology Classical

namespace J0RadialUniqueness

@[simp] theorem besselSpectralRootCoefficient_eq_residueCoefficient (M : ℕ) (nu : ℂ) :
    besselSpectralRootCoefficient M nu = besselResidueCoefficient M nu := rfl

def besselSpectralBoxPoleFinset (n : ℕ) : Finset ℂ := (besselSpectralBoxPoles_finite n).toFinset

@[simp] theorem mem_besselSpectralBoxPoleFinset (n : ℕ) (z : ℂ) :
    z ∈ besselSpectralBoxPoleFinset n ↔ z ∈ besselSpectralBoxPoles n :=
  Set.Finite.mem_toFinset _

def rightOnePointBoxSet (n : ℕ) : Set RightOnePoint :=
  {z | (z : ℂ) ∈ besselSpectralClosedBox n}

theorem rightOnePointBoxSet_finite (n : ℕ) : (rightOnePointBoxSet n).Finite := by
  have hi : Function.Injective (fun z : RightOnePoint => (z : ℂ)) := by
    intro z w h
    exact Subtype.ext (Subtype.ext h)
  have hh := (besselSpectralBoxPoles_finite n).preimage
    (f := fun z : RightOnePoint => (z : ℂ)) (fun _ _ _ _ h => hi h)
  apply hh.subset
  intro z hz
  exact ⟨hz, Or.inr z.val.property.2⟩

def rightOnePointBoxFinset (n : ℕ) : Finset RightOnePoint := (rightOnePointBoxSet_finite n).toFinset

@[simp] theorem mem_rightOnePointBoxFinset (n : ℕ) (z : RightOnePoint) :
    z ∈ rightOnePointBoxFinset n ↔ (z : ℂ) ∈ besselSpectralClosedBox n :=
  Set.Finite.mem_toFinset _

theorem one_point_re_ne_zero {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1) : z.re ≠ 0 := by
  intro hre
  have hh := (globalLocalization z hz hJ).1
  simp only [pow_two, Complex.mul_re, hre, zero_mul] at hh
  nlinarith [sq_nonneg z.im]

theorem besselSpectralClosedBox_neg {n : ℕ} {z : ℂ}
    (hz : z ∈ besselSpectralClosedBox n) : -z ∈ besselSpectralClosedBox n := by
  simpa only [besselSpectralClosedBox, mem_setOf_eq, Complex.neg_re, Complex.neg_im, abs_neg] using hz

theorem besselSpectralBoxPoleFinset_neg {n : ℕ} {z : ℂ}
    (hz : z ∈ (besselSpectralBoxPoleFinset n).erase 0) :
    -z ∈ (besselSpectralBoxPoleFinset n).erase 0 := by
  obtain ⟨hz0, hzS⟩ := Finset.mem_erase.mp hz
  have hp := (mem_besselSpectralBoxPoleFinset n z).mp hzS
  have hJ : J0 z = 1 := hp.2.resolve_left hz0
  apply Finset.mem_erase.mpr
  refine ⟨neg_ne_zero.mpr hz0, (mem_besselSpectralBoxPoleFinset n (-z)).mpr ?_⟩
  exact ⟨besselSpectralClosedBox_neg hp.1, Or.inr (by rw [J0_neg]; exact hJ)⟩

/-- Pair a genuinely finite symmetric set of roots by the sign of the real
part. No multiplicity or root enumeration is hidden in the indexing. -/
theorem besselSpectralBox_sum_pair (n : ℕ) (f : ℂ → ℂ) :
    (∑ z ∈ (besselSpectralBoxPoleFinset n).erase 0, f z) =
      ∑ z ∈ ((besselSpectralBoxPoleFinset n).erase 0).filter (fun z => 0 < z.re),
        (f z + f (-z)) := by
  let S : Finset ℂ := (besselSpectralBoxPoleFinset n).erase 0
  let U : Finset ℂ := S.filter (fun z => 0 < z.re)
  have hneg (z : ℂ) (hz : z ∈ S) : -z ∈ S := besselSpectralBoxPoleFinset_neg hz
  have hren (z : ℂ) (hz : z ∈ S) : z.re ≠ 0 := by
    obtain ⟨hz0, hzS⟩ := Finset.mem_erase.mp hz
    exact one_point_re_ne_zero hz0
      (((mem_besselSpectralBoxPoleFinset n z).mp hzS).2.resolve_left hz0)
  have hsplit : S = U ∪ U.image (fun z : ℂ => -z) := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      by_cases hre : 0 < z.re
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hre⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨-z, Finset.mem_filter.mpr ⟨hneg z hz, ?_⟩, neg_neg z⟩
        simp only [Complex.neg_re]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hre) (hren z hz))
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        exact hneg w (Finset.mem_filter.mp hw).1
  have hdis : Disjoint U (U.image (fun z : ℂ => -z)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzI
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzI
    have hzre := (Finset.mem_filter.mp hz).2
    have hwre := (Finset.mem_filter.mp hw).2
    simp only [Complex.neg_re] at hzre
    linarith
  change (∑ z ∈ S, f z) = ∑ z ∈ U, (f z + f (-z))
  rw [hsplit, Finset.sum_union hdis,
    Finset.sum_image (fun a _ b _ h => neg_injective h), Finset.sum_add_distrib]

theorem besselSpectralBox_right_sum_eq (n : ℕ) (f : ℂ → ℂ) :
    (∑ z ∈ ((besselSpectralBoxPoleFinset n).erase 0).filter (fun z => 0 < z.re), f z) =
      ∑ z ∈ rightOnePointBoxFinset n, f (z : ℂ) := by
  symm
  apply Finset.sum_bij (fun (z : RightOnePoint) _ => ((z : onePoints) : ℂ))
  · intro z hz
    have hbox := (mem_rightOnePointBoxFinset n z).mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨z.val.property.1, ?_⟩, z.property⟩
    exact (mem_besselSpectralBoxPoleFinset n z).mpr ⟨hbox, Or.inr z.val.property.2⟩
  · intro z hz w hw heq
    exact Subtype.ext (Subtype.ext heq)
  · intro z hz
    obtain ⟨hzT, hzre⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz0, hzS⟩ := Finset.mem_erase.mp hzT
    have hp := (mem_besselSpectralBoxPoleFinset n z).mp hzS
    let w : RightOnePoint := ⟨⟨z, hz0, hp.2.resolve_left hz0⟩, hzre⟩
    exact ⟨w, (mem_rightOnePointBoxFinset n w).mpr hp.1, rfl⟩
  · intro z hz
    rfl

def besselSpectralRightBoxSum (M : ℕ) (t : ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ rightOnePointBoxFinset n, besselResidueCoefficient M z * J0 (t * (z : ℂ))

/-- Exact finite ± pairing, with the origin already removed. This is the
nonzero contribution needed by the finite contour identity. -/
theorem besselSpectralBox_nonzero_residue_sum (M : ℕ) (t : ℂ) (n : ℕ) :
    (∑ z ∈ (besselSpectralBoxPoleFinset n).erase 0, besselSpectralSimpleResidue M t z) =
      -besselSpectralRightBoxSum M t n := by
  rw [besselSpectralBox_sum_pair]
  simp_rw [besselSpectralSimpleResidue_pair, besselSpectralRootCoefficient_eq_residueCoefficient,
    neg_mul]
  rw [Finset.sum_neg_distrib, besselSpectralBox_right_sum_eq]
  rfl

theorem besselSpectralBoxRadius_monotone : Monotone besselSpectralBoxRadius := by
  intro n m hnm
  have hh : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  unfold besselSpectralBoxRadius
  nlinarith [Real.pi_pos]

theorem rightOnePointBoxFinset_monotone : Monotone rightOnePointBoxFinset := by
  intro n m hnm z hz
  have hp := (mem_rightOnePointBoxFinset n z).mp hz
  exact (mem_rightOnePointBoxFinset m z).mpr
    ⟨hp.1.trans (besselSpectralBoxRadius_monotone hnm), hp.2.trans (besselSpectralBoxRadius_monotone hnm)⟩

theorem rightOnePointBoxFinset_exhausts (z : RightOnePoint) : ∃ n : ℕ, z ∈ rightOnePointBoxFinset n := by
  obtain ⟨n, hn⟩ := exists_nat_ge ‖(z : ℂ)‖
  have hnN : (n : ℝ) ≤ besselSpectralBoxRadius n := by
    have hmul := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    unfold besselSpectralBoxRadius
    nlinarith [Real.pi_pos]
  refine ⟨n, (mem_rightOnePointBoxFinset n z).mpr ?_⟩
  exact ⟨(Complex.abs_re_le_norm _).trans (hn.trans hnN),
    (Complex.abs_im_le_norm _).trans (hn.trans hnN)⟩

theorem rightOnePointBoxFinset_tendsto : Tendsto rightOnePointBoxFinset atTop atTop :=
  rightOnePointBoxFinset_monotone.tendsto_atTop_finset rightOnePointBoxFinset_exhausts

theorem norm_J0_one_point_scale_le {z : ℂ} (hz : z ≠ 0) (hJ : J0 z = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖J0 ((t : ℂ) * z)‖ ≤ 4 * ‖z‖ := by
  have hh := norm_J0_le_exp_abs_im ((t : ℂ) * z)
  have him : |((t : ℂ) * z).im| = t * |z.im| := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_nonneg ht.1]
  rw [him] at hh
  exact (hh.trans (Real.exp_le_exp.mpr (by nlinarith [ht.2, abs_nonneg z.im]))).trans
    (one_point_exp_abs_im_bound hz hJ).le

def besselRadialRootSeries (M : ℕ) (t : ℝ) : ℂ :=
  ∑' z : RightOnePoint, besselResidueCoefficient M z * J0 ((t : ℂ) * (z : ℂ))

theorem besselRadialRootSeries_summable (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun z : RightOnePoint => besselResidueCoefficient M z * J0 ((t : ℂ) * (z : ℂ))) := by
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hs := ((besselResidueCoefficient_weight_summable M (b := 1) (by linarith)).subtype
    (fun z : onePoints => 0 < (z : ℂ).re)).mul_left 4
  simp only [Real.rpow_one] at hs
  dsimp only [Function.comp_def] at hs
  apply Summable.of_norm_bounded hs
  intro z
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (norm_J0_one_point_scale_le z.val.property.1 z.val.property.2 ht) (norm_nonneg _)).trans_eq (by ring)

/-- The actual growing-box sums converge to the right-half-plane spectral
tsum. The exhaustion is proved for these boxes, not assumed as an enumeration. -/
theorem besselSpectralRightBoxSum_tendsto (M : ℕ) (hM : 2 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => besselSpectralRightBoxSum M (t : ℂ) n) atTop
      (𝓝 (besselRadialRootSeries M t)) := by
  have hh := (besselRadialRootSeries_summable M hM ht).hasSum.comp rightOnePointBoxFinset_tendsto
  exact hh

end J0RadialUniqueness
