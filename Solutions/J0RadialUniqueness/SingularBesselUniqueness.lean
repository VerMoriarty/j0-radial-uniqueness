import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

/-!
Uniqueness at the regular singular endpoint of the real order-zero modified
Bessel equation. No derivative or ordinary initial-value theorem is applied
at zero. The Wronskian constant is eliminated by a mean-value argument on
positive intervals [ε, 2ε].
-/

noncomputable section

open Set Filter
open scoped Topology

namespace J0RadialUniqueness

def singularWronskian (a ap b bp : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (a x * bp x - ap x * b x)

def singularRatio (a b : ℝ → ℝ) (x : ℝ) : ℝ := b x / a x

theorem singularWronskian_hasDerivAt
    {a ap b bp : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (ha : HasDerivAt a (ap x) x) (hap : HasDerivAt ap (a x - ap x / x) x)
    (hb : HasDerivAt b (bp x) x) (hbp : HasDerivAt bp (b x - bp x / x) x) :
    HasDerivAt (singularWronskian a ap b bp) 0 x := by
  have h := (hasDerivAt_id x).mul ((ha.mul hbp).sub (hap.mul hb))
  have hfun : id * (a * bp - ap * b) = singularWronskian a ap b bp := by
    funext y
    rfl
  rw [hfun] at h
  apply h.congr_deriv
  simp only [id_eq, Pi.mul_apply, Pi.sub_apply]
  field_simp [hx.ne'] <;> ring

theorem singularWronskian_constant
    (a ap b bp : ℝ → ℝ)
    (ha : ∀ x : ℝ, 0 < x → HasDerivAt a (ap x) x)
    (hap : ∀ x : ℝ, 0 < x → HasDerivAt ap (a x - ap x / x) x)
    (hb : ∀ x : ℝ, 0 < x → HasDerivAt b (bp x) x)
    (hbp : ∀ x : ℝ, 0 < x → HasDerivAt bp (b x - bp x / x) x) :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → singularWronskian a ap b bp x = C := by
  have hd (x : ℝ) (hx : 0 < x) :=
    singularWronskian_hasDerivAt hx (ha x hx) (hap x hx) (hb x hx) (hbp x hx)
  exact isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv)

theorem singularRatio_hasDerivAt
    {a ap b bp : ℝ → ℝ} {x : ℝ}
    (ha : HasDerivAt a (ap x) x) (hb : HasDerivAt b (bp x) x) (ha0 : a x ≠ 0) :
    HasDerivAt (singularRatio a b)
      ((a x * bp x - ap x * b x) / (a x) ^ 2) x := by
  have h := hb.div ha ha0
  apply h.congr_deriv
  ring

theorem singularRatio_hasDerivAt_of_wronskian
    {a ap b bp : ℝ → ℝ} {x C : ℝ} (hx : 0 < x)
    (ha : HasDerivAt a (ap x) x) (hb : HasDerivAt b (bp x) x) (ha0 : a x ≠ 0)
    (hW : singularWronskian a ap b bp x = C) :
    HasDerivAt (singularRatio a b) (C / (x * (a x) ^ 2)) x := by
  apply (singularRatio_hasDerivAt ha hb ha0).congr_deriv
  change x * (a x * bp x - ap x * b x) = C at hW
  calc
    (a x * bp x - ap x * b x) / (a x) ^ 2 =
        (x * (a x * bp x - ap x * b x)) / (x * (a x) ^ 2) := by
      field_simp [hx.ne', ha0] <;> ring
    _ = C / (x * (a x) ^ 2) := by rw [hW]

/-- A nonzero singular Wronskian constant contradicts a finite zero limit of
the quotient, as shown on arbitrarily small positive doubling intervals. -/
theorem singular_constant_zero_of_ratio_limit
    (a q : ℝ → ℝ) (C : ℝ)
    (ha0 : ∀ x : ℝ, 0 < x → a x ≠ 0)
    (halim : Tendsto a (𝓝[>] 0) (𝓝 1))
    (hqlim : Tendsto q (𝓝[>] 0) (𝓝 0))
    (hq : ∀ x : ℝ, 0 < x → HasDerivAt q (C / (x * (a x) ^ 2)) x) : C = 0 := by
  by_contra hC
  have hCpos : 0 < |C| := abs_pos.mpr hC
  have han : Tendsto (fun x : ℝ => |a x|) (𝓝[>] 0) (𝓝 1) := by
    simpa using halim.norm
  have hqn : Tendsto (fun x : ℝ => |q x|) (𝓝[>] 0) (𝓝 0) := by
    simpa using hqlim.norm
  have haNear : ∀ᶠ x : ℝ in 𝓝[>] 0, |a x| < 2 :=
    (tendsto_order.1 han).2 2 (by norm_num)
  have hqNear : ∀ᶠ x : ℝ in 𝓝[>] 0, |q x| < |C| / 32 :=
    (tendsto_order.1 hqn).2 (|C| / 32) (by positivity)
  have hNear : {x : ℝ | |a x| < 2 ∧ |q x| < |C| / 32} ∈ 𝓝[>] 0 :=
    haNear.and hqNear
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hNear
  change 0 < δ at hδ
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hspan : ε < 2 * ε := by linarith
  have hεδ : 2 * ε < δ := by dsimp [ε]; linarith
  have hb1 := hbound (show ε ∈ Ioo 0 δ from ⟨hε, lt_trans hspan hεδ⟩)
  have hb2 := hbound (show 2 * ε ∈ Ioo 0 δ from ⟨by linarith, hεδ⟩)
  have hcont : ContinuousOn q (Icc ε (2 * ε)) := by
    intro x hx
    exact (hq x (lt_of_lt_of_le hε hx.1)).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope q
    (fun x : ℝ => C / (x * (a x) ^ 2)) hspan hcont
    (fun x hx => hq x (lt_trans hε hx.1))
  have hξpos : 0 < ξ := lt_trans hε hξ.1
  have hbξ := hbound (show ξ ∈ Ioo 0 δ from ⟨hξpos, lt_trans hξ.2 hεδ⟩)
  have haξsq : (a ξ) ^ 2 < 4 := by
    have hsq := (sq_lt_sq₀ (abs_nonneg (a ξ)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hbξ.1
    rw [sq_abs] at hsq
    norm_num at hsq
    exact hsq
  have hdiff : |q (2 * ε) - q ε| < |C| / 16 := by
    have htri : |q (2 * ε) - q ε| ≤ |q (2 * ε)| + |q ε| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (q (2 * ε)) (-q ε)
    calc
      |q (2 * ε) - q ε| ≤ |q (2 * ε)| + |q ε| := htri
      _ < |C| / 32 + |C| / 32 := add_lt_add hb2.2 hb1.2
      _ = |C| / 16 := by ring
  have hden : 0 < ξ * (a ξ) ^ 2 :=
    mul_pos hξpos (sq_pos_of_ne_zero (ha0 ξ hξpos))
  rw [show 2 * ε - ε = ε by ring] at heq
  have hcross : C * ε = (q (2 * ε) - q ε) * (ξ * (a ξ) ^ 2) :=
    (div_eq_div_iff hden.ne' hε.ne').mp heq
  have habs : |C| * ε = |q (2 * ε) - q ε| * (ξ * (a ξ) ^ 2) := by
    have h := congrArg abs hcross
    simpa only [abs_mul, abs_of_pos hε, abs_of_pos hξpos,
      abs_of_nonneg (sq_nonneg (a ξ))] using h
  have hfac : ξ * (a ξ) ^ 2 ≤ 8 * ε := by
    calc
      ξ * (a ξ) ^ 2 ≤ ξ * 4 := mul_le_mul_of_nonneg_left haξsq.le hξpos.le
      _ ≤ (2 * ε) * 4 := mul_le_mul_of_nonneg_right hξ.2.le (by norm_num)
      _ = 8 * ε := by ring
  have hbad : |C| * ε < (|C| / 16) * (8 * ε) := by
    calc
      |C| * ε = |q (2 * ε) - q ε| * (ξ * (a ξ) ^ 2) := habs
      _ ≤ |q (2 * ε) - q ε| * (8 * ε) :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      _ < (|C| / 16) * (8 * ε) := mul_lt_mul_of_pos_right hdiff (by positivity)
  nlinarith [mul_pos hCpos hε]

/-- The regular-singular uniqueness theorem on the positive real axis. -/
theorem singularBessel_zero_of_limits
    (a ap b bp : ℝ → ℝ)
    (ha : ∀ x : ℝ, 0 < x → HasDerivAt a (ap x) x)
    (hap : ∀ x : ℝ, 0 < x → HasDerivAt ap (a x - ap x / x) x)
    (hb : ∀ x : ℝ, 0 < x → HasDerivAt b (bp x) x)
    (hbp : ∀ x : ℝ, 0 < x → HasDerivAt bp (b x - bp x / x) x)
    (ha0 : ∀ x : ℝ, 0 < x → a x ≠ 0)
    (halim : Tendsto a (𝓝[>] 0) (𝓝 1))
    (hblim : Tendsto b (𝓝[>] 0) (𝓝 0)) :
    ∀ x : ℝ, 0 < x → b x = 0 := by
  obtain ⟨C, hW⟩ := singularWronskian_constant a ap b bp ha hap hb hbp
  have hqlim : Tendsto (singularRatio a b) (𝓝[>] 0) (𝓝 0) := by
    convert! hblim.div halim (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> simp [singularRatio]
  have hq (x : ℝ) (hx : 0 < x) :
      HasDerivAt (singularRatio a b) (C / (x * (a x) ^ 2)) x :=
    singularRatio_hasDerivAt_of_wronskian hx (ha x hx) (hb x hx) (ha0 x hx) (hW x hx)
  have hC : C = 0 := singular_constant_zero_of_ratio_limit a (singularRatio a b) C
    ha0 halim hqlim hq
  have hq0 (x : ℝ) (hx : 0 < x) : HasDerivAt (singularRatio a b) 0 x := by
    simpa only [hC, zero_div] using hq x hx
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hq0 x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hq0 x hx).deriv)
  have heq : singularRatio a b =ᶠ[𝓝[>] 0] fun _ : ℝ => c := by
    filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx
    exact hc x hx
  have hclim : Tendsto (singularRatio a b) (𝓝[>] 0) (𝓝 c) :=
    tendsto_const_nhds.congr' heq.symm
  have hc0 : c = 0 := tendsto_nhds_unique hclim hqlim
  intro x hx
  have hzero : b x / a x = 0 := (hc x hx).trans hc0
  exact (div_eq_zero_iff.mp hzero).resolve_right (ha0 x hx)

end J0RadialUniqueness
